"""Independent rebuild of the fractional project from a copy in an empty directory.
Compiles every module reachable from fourth_pass.Unconditional in dependency order; certificate groups in parallel."""
import os, re, shutil, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
SRC = 'E:/lean/se20-fractional'; D = 'E:/lean/verify/fractional'; LANES = int(sys.argv[1]) if len(sys.argv) > 1 else 3
LEAN = 'E:/lean/elan/toolchains/leanprover--lean4---v4.35.0-rc4/bin/lean.exe'
if os.path.exists(D): shutil.rmtree(D)
os.makedirs(D)
for sub in ['Se20Fractional', 'second_pass', 'third_pass', 'fourth_pass', 'independent']:
    for root, dirs, files in os.walk(os.path.join(SRC, sub)):
        for f in files:
            if f.endswith('.lean'):
                t = os.path.join(D, os.path.relpath(os.path.join(root, f), SRC))
                os.makedirs(os.path.dirname(t), exist_ok=True); shutil.copy(os.path.join(root, f), t)
shutil.copy(SRC + '/Se20Fractional.lean', D)
pkg = 'E:/lean/sep19/route-c/lean/.lake/packages'
paths = [D + '/.lake/build/lib/lean'] + [os.path.join(pkg, p, '.lake/build/lib/lean') for p in os.listdir(pkg)]
env = dict(os.environ, LEAN_PATH=';'.join(paths), TEMP='E:\\lean\\tmp', TMP='E:\\lean\\tmp')
seen = {}; order = []
def visit(m):
    if m in seen: return
    seen[m] = 1
    f = os.path.join(D, m.replace('.', '/') + '.lean')
    if not os.path.exists(f): return
    for line in open(f, encoding='utf-8'):
        k = re.match(r'^(?:public )?import\s+([A-Za-z0-9_.]+)\s*$', line)
        if k: visit(k[1])
    order.append(m)
visit('fourth_pass.Unconditional')
log = open('E:/lean/verify/fractional_BUILD.log', 'w', encoding='utf-8')
def comp(m):
    f = m.replace('.', '/') + '.lean'; out = '.lake/build/lib/lean/' + m.replace('.', '/') + '.olean'
    os.makedirs(os.path.join(D, os.path.dirname(out)), exist_ok=True)
    for att in range(25):
        t = time.time()
        r = subprocess.run([LEAN, '-M6000', '-o', out, f], cwd=D, env=env, capture_output=True, text=True, encoding='utf-8', errors='replace')
        txt = r.stdout + r.stderr
        if r.returncode == 0:
            log.write(f'OK {m} {time.time()-t:.0f}s attempt {att}\n');
            for l in txt.splitlines():
                if 'depends on axioms' in l or 'sorry' in l: log.write(l + '\n')
            log.flush(); return
        if 'failed to read file' in txt or 'bad_alloc' in txt or 'out of memory' in txt.lower() or 'exceeded memory' in txt.lower():
            log.write(f'RETRY {m} attempt {att}\n'); log.flush(); time.sleep(60); continue
        log.write(f'FAIL {m}\n{txt[-1500:]}\n'); log.flush(); print('FAIL', m); sys.exit(1)
    print('GAVE UP', m); sys.exit(1)
groups = [m for m in order if '.certificates.group_' in m]
pre = []
post = []
for m in order:
    if m in groups: continue
    (post if '.certificates.root_' in m or m.endswith('Unconditional') else pre).append(m)
print('modules', len(order), 'groups', len(groups), flush=True)
for m in pre: comp(m)
print('base done', flush=True)
with ThreadPoolExecutor(LANES) as ex:
    list(ex.map(comp, groups))
print('groups done', flush=True)
for m in post: comp(m)
log.close()
print('ALL OK', flush=True)
for l in open('E:/lean/verify/fractional_BUILD.log', encoding='utf-8'):
    if 'depends on axioms' in l and ('theorem_F_unconditional' in l or 'no_obstruction14' in l or 'propositionD_unconditional' in l): print(l.strip()[:120])
