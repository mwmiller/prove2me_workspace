#!/usr/bin/env python3
"""Mirror accepted proofs into Theorems/Thm_*.lean; normalize Solutions/Sol_*.lean.

Replaces the lost /tmp gap-family mirror.py with a general, git-tracked tool.

Usage:
  python3 scripts/mirror_family.py fill  --inv INV.json --map MAP.json [--dry] [--fam PREFIX]
  python3 scripts/mirror_family.py strip --inv INV.json [--dry] [--fam PREFIX]
  python3 scripts/mirror_family.py run   --inv INV.json --map MAP.json [--dry] [--fam PREFIX]
  python3 scripts/mirror_family.py deps  --files Thm/a.lean,Thm/b.lean [--cap N] [--dry]

Data files:
  --inv  inventory JSON: [{name, thm, sol, t_sorry, s_sorry, s_self, kids, tid}, ...]
  --map  platform map JSON: {local_name: {theorem_id, theorem_name, status, title}}

fill sources, in order:
  1. local Solutions/Sol_<name>.lean (our accepted proof),
  2. else, if the platform node is Proved, the accepted submission that needs
     the fewest imports we cannot resolve locally (attributed with a comment
     line above the declaration); submissions requiring missing Definitions.*
     are treated as unusable (LEAVE),
  3. else (Open node, no local proof): leave the statement skeleton untouched.

Thm outcomes:
  - skeleton with `sorry` + simple source  -> proof spliced after the skeleton's
    own statement; imports = skeleton imports ∪ local source imports;
  - source defines helper decls its proof needs -> whole source mirrored with
    `theorem solution` renamed to the platform's dotted name;
  - missing Thm                            -> created from the source (same
    rename), keeping the source's header/meta verbatim.
Sol outcome: the forbidden self-import line is removed (strip).

deps materializes the transitive Theorems.Thm_* closure referenced by the
sources of the given Thm files: two phases (plan the closure with per-module
submission choice first, then write, so intra-closure imports resolve); a
module is skipped when every accepted submission needs unmaterializable
imports (missing Definitions.*) or when a planned dependency is skipped.

Stale local duplicates (no platform node) are skipped by name.
Platform fetches read the token from /tmp/p2m_token.
"""
import argparse
import json
import os
import re
import urllib.parse
import urllib.request

WS = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
API = 'https://prove2.me/api/v1'
SKIP = {
    'Kyprianou_Ch08_StageB_open_result8_3_accepted',   # stale duplicate of open_result8_3
    'Kyprianou_Ch08_StageB_open_result8_5_accepted',   # stale duplicate of open_result8_5
}


def api(path):
    tok = open('/tmp/p2m_token').read().strip()
    req = urllib.request.Request(API + path, headers={'Authorization': f'Bearer {tok}'})
    try:
        return json.load(urllib.request.urlopen(req))
    except urllib.error.HTTPError as e:
        raise RuntimeError(f'GET {path} -> {e.code} {e.read().decode()[:200]}')


def module_file_exists(mod):
    if mod.startswith(('Mathlib', 'Init', 'Std', 'Batteries', 'Lean', 'Qq')):
        return True
    return os.path.exists(os.path.join(WS, *mod.split('.')) + '.lean')


def imports_of(text):
    return re.findall(r'^import\s+(\S+)\s*$', text, re.M)


NOTES = []


def filtered_imports(src_text, own_name, seen=None, extra_ok=None):
    """Source import lines, local modules only, no self-import, deduped.
    `extra_ok`: module names that will exist by write time (planned closure)."""
    seen = seen if seen is not None else set()
    out = []
    for mod in imports_of(src_text):
        if mod == f'Theorems.Thm_{own_name}':
            continue
        if not module_file_exists(mod) and not (extra_ok and mod in extra_ok):
            NOTES.append(f'dropped non-local import {mod}')
            continue
        if mod not in seen:
            seen.add(mod)
            out.append(mod)
    return out


def replace_import_block(text, mods):
    """Replace the leading `import ...` block of a file with the given modules."""
    lines = text.split('\n')
    i, saw = 0, False
    while i < len(lines):
        if lines[i].startswith('import '):
            saw = True
            i += 1
        elif saw and lines[i].strip() == '':
            i += 1
        else:
            break
    head = '\n'.join(f'import {m}' for m in mods)
    return head + '\n\n' + '\n'.join(lines[i:])


def split_solution(text):
    """-> (before_decl, decl_text_through_colon, proof_after_colon)."""
    m = re.search(r'^theorem (?:_root_\.)?solution\b', text, re.M)
    if not m:
        raise ValueError('no top-level `theorem solution`')
    before = text[:m.start()]
    decl = text[m.start():]
    c = decl.find(':=')
    if c < 0:
        raise ValueError('no `:=` after theorem solution')
    proof = decl[c + 2:]
    if not (proof.startswith(' by') or proof.startswith('\n')):
        raise ValueError(f'suspicious text after :=: {proof[:40]!r}')
    if '_root_' not in m.group(0):
        open_ns = None
        for lm in re.finditer(r'^(namespace|end)\s+(\S+)', before, re.M):
            open_ns = lm.group(2) if lm.group(1) == 'namespace' else None
        if open_ns is not None:
            raise ValueError(f'theorem solution is inside namespace {open_ns}')
    return before, decl[:c + 2], proof


def rename_solution(src_text, pname):
    """Rename `theorem (?:_root_.)?solution` to the platform name, respecting
    any enclosing namespace. Returns new text, or None if no decl found."""
    m = re.search(r'^theorem (?:_root_\.)?solution\b', src_text, re.M)
    if not m:
        return None
    open_ns = None
    for lm in re.finditer(r'^(namespace|end)\s+(\S+)', src_text[:m.start()], re.M):
        open_ns = lm.group(2) if lm.group(1) == 'namespace' else None
    if open_ns is None:
        new_name = pname
    elif pname.startswith(open_ns + '.'):
        new_name = pname[len(open_ns) + 1:]
    else:
        new_name = '_root_.' + pname
    return src_text[:m.start()] + 'theorem ' + new_name + src_text[m.end():]


def with_attribution(src_text, attrib):
    if not attrib:
        return src_text
    m = re.search(r'^theorem (?:_root_\.)?solution\b', src_text, re.M)
    if not m:
        return src_text
    return src_text[:m.start()] + attrib + src_text[m.start():]


def helper_decls(text):
    return [m.group(1) for m in
            re.finditer(r'^(?:private\s+|protected\s+)?(?:theorem|lemma|def|abbrev)'
                        r'\s+(?:_root_\.)?(\w+)',
                        text, re.M)
            if m.group(1) != 'solution']


_SOL_CACHE = {}


def submission_content(sid):
    if sid not in _SOL_CACHE:
        _SOL_CACHE[sid] = api(f'/submissions/{sid}/solution').get('content', '')
    return _SOL_CACHE[sid]


def missing_imports(text):
    return [m for m in imports_of(text) if not module_file_exists(m)]


def pick_submission(theorem_id, log):
    """Score every accepted submission: unusable first if it needs imports we
    cannot materialize (non-Theorems.*), then fewest missing Theorems.Thm_*
    imports; ties keep platform order (earliest first).
    Returns {sid, user, content, blocked} or None."""
    subs = api(f'/theorems/{theorem_id}/submissions'
               f'?status=ACCEPTED,SKETCH_ACCEPTED').get('submissions') or []
    cands = []
    for s in subs:
        try:
            content = submission_content(s['id'])
        except RuntimeError as e:
            log(f'    fetch fail {s["id"][:8]}: {e}')
            continue
        if not content:
            continue
        if not (re.search(r'^theorem (?:_root_\.)?solution\b', content, re.M)
                or re.search(r'^theorem\s+\S+', content, re.M)):
            continue
        miss = missing_imports(content)
        bad = [m for m in miss if not m.startswith('Theorems.Thm_')]
        cands.append(((1 if bad else 0, len(miss)), s['id'],
                      s.get('username', '?'), content, bad))
    if not cands:
        return None
    cands.sort(key=lambda c: c[0])
    _, sid, user, content, bad = cands[0]
    return {'sid': sid, 'user': user, 'content': content,
            'blocked': bad or None}


def splice_proof(thm_text, proof, attribution=''):
    """Replace the skeleton's `sorry` proof with `proof` (text after :=)."""
    hits = list(re.finditer(r'\bsorry\b', thm_text))
    if len(hits) != 1:
        raise ValueError(f'skeleton has {len(hits)} `sorry` occurrences (want 1)')
    si = hits[0].start()
    ci = thm_text.rfind(':=', 0, si)
    if ci < 0:
        raise ValueError('no `:=` before sorry')
    after = thm_text[si + 5:]
    bad = [l for l in after.split('\n') if l.strip() and not l.strip().startswith('end ')]
    if bad:
        raise ValueError(f'unexpected content after sorry: {bad[:2]!r}')
    prefix = thm_text[:ci]
    if attribution:
        ti = prefix.rfind('\ntheorem ')
        if ti < 0:
            raise ValueError('cannot place attribution (no theorem line)')
        prefix = prefix[:ti + 1] + attribution + prefix[ti + 1:]
    return prefix + ':=' + proof.rstrip('\n') + (after if after else '\n')


def do_fill(name, pmap, dry, log):
    thm_path = os.path.join(WS, 'Theorems', f'Thm_{name}.lean')
    sol_path = os.path.join(WS, 'Solutions', f'Sol_{name}.lean')
    info = pmap.get(name)
    pname = info['theorem_name'] if info else None

    if os.path.exists(thm_path):
        thm_text = open(thm_path).read()
        if not re.search(r'\bsorry\b', thm_text):
            log(f'  KEEP   {name}: Thm already has a proof')
            return 'kept'
    else:
        thm_text = None

    src_text, src_kind, attrib = None, None, ''
    if os.path.exists(sol_path):
        src_text, src_kind = open(sol_path).read(), 'local'
    elif info and info['status'] == 'Proved':
        cand = pick_submission(info['theorem_id'], log)
        if cand is None:
            log(f'  FAIL   {name}: Proved but no usable accepted submission')
            return 'fail'
        if cand['blocked']:
            log(f'  LEAVE  {name}: best submission needs unmaterializable '
                f'imports {cand["blocked"][:3]}')
            return 'left'
        src_text, src_kind = cand['content'], 'platform'
        attrib = (f'-- Proof mirrored from accepted submission {cand["sid"]} '
                  f'(by {cand["user"]}).\n')
    else:
        status = info['status'] if info else 'unmapped'
        log(f'  LEAVE  {name}: no local proof, platform status {status}')
        return 'left'

    if pname is None:
        log(f'  FAIL   {name}: no platform name in map (needed for rename)')
        return 'fail'

    try:
        before, decl, proof = split_solution(src_text)
    except ValueError as e:
        log(f'  FAIL   {name}: cannot parse source: {e}')
        return 'fail'

    extras = helper_decls(src_text)

    if thm_text is not None and not extras:
        # SPLICE: keep the skeleton (statement/doc/namespace), swap in the proof
        merged = filtered_imports(thm_text, name)
        for mod in filtered_imports(src_text, name, set(merged)):
            merged.append(mod)
        try:
            new = splice_proof(thm_text, proof, attrib)
        except ValueError as e:
            log(f'  FAIL   {name}: splice: {e}')
            return 'fail'
        new = replace_import_block(new, merged)
        action = 'FILL'
    elif thm_text is not None and extras:
        # FULL MIRROR: helpers live only in the source file
        new = with_attribution(src_text, attrib)
        new = rename_solution(new, pname)
        if new is None:
            log(f'  FAIL   {name}: cannot rename solution decl')
            return 'fail'
        new = replace_import_block(new, filtered_imports(src_text, name))
        action = 'MIRROR'
    else:  # create missing Thm (with or without helpers: whole source mirrored)
        new = with_attribution(src_text, attrib)
        new = rename_solution(new, pname)
        if new is None:
            log(f'  FAIL   {name}: cannot rename solution decl')
            return 'fail'
        new = replace_import_block(new, filtered_imports(src_text, name))
        action = 'CREATE'

    if dry:
        log(f'  {action}   {name} ({src_kind} source)')
        return action.lower()
    open(thm_path, 'w').write(new)
    log(f'  {action}   {name} ({src_kind} source) -> {os.path.relpath(thm_path, WS)}')
    return action.lower()


# ---------------------------------------------------------------- dep closure

ATTRIB_RE = re.compile(r'(?:earliest )?accepted submission ([0-9a-f-]{36})')


def find_platform_theorem(rest, log):
    """rest: module suffix after `Thm_`, e.g. `GRH_principal_mobius_...`.
    Match platform theorem whose dotted name flattens to rest."""
    toks = rest.split('_')
    queries = []
    if len(toks) <= 8:
        queries.append('_'.join(toks))
    for k in (6, 4, 3):
        if k < len(toks):
            q = '_'.join(toks[-k:])
            if q not in queries:
                queries.append(q)
    for q in queries:
        try:
            items = api(f'/theorems?q={urllib.parse.quote(q)}&view=compact&per_page=50') \
                .get('theorems', [])
        except RuntimeError as e:
            log(f'    search fail for {rest}: {e}')
            continue
        for it in items:
            if it['theorem_name'].replace('.', '_') == rest:
                return it
        cands = [it for it in items
                 if it['theorem_name'].replace('.', '_').endswith(rest)]
        if len(cands) == 1:
            return cands[0]
    return None


def declared_names(text):
    """Approximate set of full names of top-level decls (single-level namespace
    tracking; `_root_.x` counted as `x`)."""
    names = set()
    open_ns = None
    pat = (r'^(namespace|end)\b\s*(\S*)'
           r'|(?:^(?:private\s+|protected\s+)?(?:theorem|lemma|def|abbrev)\s+)'
           r'((?:_root_\.)?\S+)')
    for m in re.finditer(pat, text, re.M):
        if m.group(1) == 'namespace':
            open_ns = m.group(2) or None
        elif m.group(1) == 'end':
            open_ns = None
        elif m.group(3):
            nm = m.group(3)
            if nm.startswith('_root_.'):
                names.add(nm[len('_root_.'):])
            elif open_ns:
                names.add(f'{open_ns}.{nm}')
            else:
                names.add(nm)
    return names


def create_from_source(src_text, pname, module, log, extra_ok=None):
    """Build a Thm module from a submission source; rename `theorem solution`
    to pname (handling an enclosing namespace / `_root_`). Returns text or None."""
    if declared_names(src_text) & {pname}:
        new = src_text  # target already declared (solution is a wrapper); keep as-is
    elif re.search(r'^theorem (?:_root_\.)?solution\b', src_text, re.M):
        new = rename_solution(src_text, pname)
    else:
        log(f'    FAIL: no solution/named decl for {pname}')
        return None
    mods = filtered_imports(new, module.split('Thm_', 1)[1], set(), extra_ok)
    new = replace_import_block(new, mods)
    if not ATTRIB_RE.search(new):
        m = re.search(r'^theorem ', new, re.M)
        new = (new[:m.start()]
               + f'-- Mirrored from accepted submission for `{pname}`.\n'
               + new[m.start():])
    return new


def do_deps(thm_files, dry, log, cap=0):
    """Materialize missing Theorems.Thm_* modules referenced by the sources of
    the given Thm files (transitively)."""
    queue, seen = [], set()

    def source_of(path):
        text = open(path).read()
        am = ATTRIB_RE.search(text)
        if am:
            return api(f'/submissions/{am.group(1)}/solution')['content']
        name = re.search(r'Thm_(\w+)\.lean$', path).group(1)
        sol = os.path.join(WS, 'Solutions', f'Sol_{name}.lean')
        return open(sol).read() if os.path.exists(sol) else None

    for path in thm_files:
        src = source_of(path)
        if src is None:
            log(f'  note   {path}: no source found')
            continue
        for mod in imports_of(src):
            if mod.startswith('Theorems.Thm_') and not module_file_exists(mod):
                queue.append(mod)

    made = 0
    blocked = []
    plan = {}  # mod -> (info, cand): the chosen source for each closure module
    while queue:
        mod = queue.pop(0)
        if mod in seen:
            continue
        seen.add(mod)
        if module_file_exists(mod):
            continue
        if cap and len(plan) >= cap:
            log(f'  STOP   cap {cap} reached; {len(queue)} modules left unexamined')
            break
        rest = mod.split('Thm_', 1)[1]
        info = find_platform_theorem(rest, log)
        if not info:
            log(f'  FAIL   {mod}: no platform theorem matching {rest}')
            blocked.append(mod)
            continue
        if info['status'] != 'Proved':
            log(f'  FAIL   {mod}: platform {info["theorem_name"]} is {info["status"]}')
            blocked.append(mod)
            continue
        cand = pick_submission(info['theorem_id'], log)
        if cand is None:
            log(f'  FAIL   {mod}: Proved but no usable accepted submission')
            blocked.append(mod)
            continue
        if cand['blocked']:
            log(f'  BLOCK  {mod}: best submission needs {cand["blocked"][:3]}')
            blocked.append(mod)
            continue
        plan[mod] = (info, cand)
        for dep in imports_of(cand['content']):
            if dep.startswith('Theorems.Thm_') and not module_file_exists(dep):
                queue.append(dep)

    # write phase: only write modules whose closure deps will exist
    writable = set()
    changed = True
    while changed:
        changed = False
        for mod, (info, cand) in plan.items():
            if mod in writable:
                continue
            deps = [m for m in imports_of(cand['content'])
                    if m.startswith('Theorems.Thm_')
                    and not module_file_exists(m)]
            if all(d in writable for d in deps):
                writable.add(mod)
                changed = True
    for mod in plan:
        if mod not in writable:
            log(f'  BLOCK  {mod}: depends on blocked module')
            blocked.append(mod)
    for mod in sorted(writable):
        info, cand = plan[mod]
        sid, user, src = cand['sid'], cand['user'], cand['content']
        new = create_from_source(src, info['theorem_name'], mod, log,
                                 extra_ok=set(plan))
        if new is None:
            blocked.append(mod)
            continue
        new = new.replace(
            f'-- Mirrored from accepted submission for `{info["theorem_name"]}`.',
            f'-- Proof mirrored from accepted submission {sid} (by {user}).',
            1) if '-- Mirrored from accepted submission' in new else new
        path = os.path.join(WS, *mod.split('.')) + '.lean'
        if dry:
            log(f'  MAKE  {mod}  <- {info["theorem_name"]} ({sid[:8]})')
        else:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            open(path, 'w').write(new)
            log(f'  MAKE   {mod}  <- {info["theorem_name"]} ({sid[:8]})')
        made += 1
    log(f'deps: {made} modules materialized, {len(seen)} examined, '
        f'{len(blocked)} blocked')
    for b in blocked:
        log(f'  blocked: {b}')


def do_fiximports(paths, log):
    """Re-merge each target Thm file's source imports (post-deps): keeps the
    file's current imports and appends source imports that now resolve."""
    for path in paths:
        text = open(path).read()
        name_m = re.search(r'Thm_(\w+)\.lean$', path)
        name = name_m.group(1)
        am = ATTRIB_RE.search(text)
        src = None
        if am:
            try:
                src = submission_content(am.group(1))
            except RuntimeError as e:
                log(f'  note   {path}: fetch {e}')
        if src is None:
            sol = os.path.join(WS, 'Solutions', f'Sol_{name}.lean')
            if os.path.exists(sol):
                src = open(sol).read()
        if src is None:
            log(f'  note   {path}: no source found')
            continue
        have = imports_of(text)
        want = filtered_imports(src, name, set(have))
        add = [m for m in want if m not in have]
        if not add:
            log(f'  OK     {path}')
            continue
        new = replace_import_block(text, have + add)
        open(path, 'w').write(new)
        log(f'  PATCH  {path}: + {add}')


def do_strip(name, dry, log):
    sol_path = os.path.join(WS, 'Solutions', f'Sol_{name}.lean')
    if not os.path.exists(sol_path):
        return 'nosol'
    text = open(sol_path).read()
    line = f'import Theorems.Thm_{name}\n'
    if line not in text:
        return 'clean'
    if not dry:
        open(sol_path, 'w').write(text.replace(line, '', 1))
    log(f'  STRIP  {name}')
    return 'strip'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cmd', choices=['fill', 'strip', 'run', 'deps', 'fiximports'])
    ap.add_argument('--inv', help='inventory JSON (fill/strip/run)')
    ap.add_argument('--map', dest='map_path')
    ap.add_argument('--dry', action='store_true')
    ap.add_argument('--fam', help='comma-separated name prefixes')
    ap.add_argument('--files', help='comma-separated Thm file paths (deps cmd)')
    ap.add_argument('--cap', type=int, default=0, help='max modules to materialize')
    args = ap.parse_args()

    lines = []

    def log(msg):
        lines.append(msg)
        print(msg)

    if args.cmd == 'deps':
        if not args.files:
            ap.error('deps requires --files')
        do_deps(args.files.split(','), args.dry, log, cap=args.cap)
        for n in sorted(set(NOTES)):
            log(f'  note   {n}')
        return

    if args.cmd == 'fiximports':
        if not args.files:
            ap.error('fiximports requires --files')
        do_fiximports(args.files.split(','), log)
        return

    if not args.inv:
        ap.error(f'{args.cmd} requires --inv')
    inv = json.load(open(args.inv))
    pmap = json.load(open(args.map_path)) if args.map_path else {}
    fams = args.fam.split(',') if args.fam else None
    rows = [r for r in inv if (not fams or any(r['name'].startswith(f) for f in fams))
            and r['name'] not in SKIP]

    stats = {}
    if args.cmd in ('fill', 'run'):
        log('== fill ==')
        for r in rows:
            st = do_fill(r['name'], pmap, args.dry, log)
            stats[st] = stats.get(st, 0) + 1
    if args.cmd in ('strip', 'run'):
        log('== strip ==')
        for r in rows:
            st = do_strip(r['name'], args.dry, log)
            stats[st] = stats.get(st, 0) + 1
    for s in sorted(SKIP):
        log(f'  SKIP   {s} (stale duplicate)')
    for n in sorted(set(NOTES)):
        log(f'  note   {n}')
    log('summary: ' + json.dumps(stats))


if __name__ == '__main__':
    main()
