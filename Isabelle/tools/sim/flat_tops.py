"""Original method (Algorithm.thy, strict peaks, threshold max/100): what the test does not see.
Sweep [0, pi/4] (4501 foci), bisect at every change of the correction sequence, and at each stop
evaluate the pattern on a grid 64 times finer.  Reports the level just outside the band, the stops
with an invisible flat top (two equal adjacent samples above the threshold), and the stops whose true
peak between grid points exceeds -20 dB.  These are the numbers of paper section 3.4.
usage: flat_tops.py dc|oct   (30-degree band; without a band the runs are the same)"""
import sys, numpy as np
sys.path.insert(0, '/home/dusty/Desktop/Matlab_UH_Project/Proof/Termination_Counterexample')
import pm_core as pc
arr = sys.argv[1]
if arr == 'dc':
    a, b = 0.042211347450806, 0.039173549691350
    x = np.array([0, -a, a, 0, 0, b, -b, -b, b]); y = np.array([0, 0, 0, a, -a, b, b, -b, -b])
else:
    x, y = pc.octagon9(0.04880)
N = 9; M = pc.M; cone = np.pi/6
K = pc.steer(x, y, pc.PHI)
PHIF = np.linspace(0, 2*np.pi, M*64, endpoint=False); KF = pc.steer(x, y, PHIF)
def st(p): return np.exp(1j*pc.K0*(x*np.cos(p) + y*np.sin(p)))
def cdist(u, v): return np.abs(np.angle(np.exp(1j*(u - v))))
def run(t):
    A = np.exp(-1j*pc.K0*(x*np.cos(t) + y*np.sin(t))); seq = []
    while True:
        Sl, idx, mi, mv, Fmax = pc.scan_sl(A @ K, t, -20.0, cone)
        if Sl.size == 0 or len(seq) > 40: return tuple(seq), A
        s = int(idx[0]); v = st(pc.PHI[s]); A = A - (A @ v)/N*np.conj(v); seq.append(s)
def cont_worst(A, t):
    P = np.abs(A @ KF)**2
    pk = np.flatnonzero((P > np.roll(P, 1)) & (P > np.roll(P, -1))); lv = []
    for k in pk:
        u, w, v = P[k-1], P[k], P[(k+1) % P.size]; d = 0.5*(u - v)/(u - 2*w + v)
        ph = PHIF[k] + d*(PHIF[1] - PHIF[0]); lv.append((ph, np.abs(A @ st(ph))**2))
    pmax = max(q[1] for q in lv); main = min(lv, key=lambda q: cdist(q[0], t))
    side = [q[1] for q in lv if q != main and cdist(q[0], t) > cone]
    return 10*np.log10(max(side)/pmax) if side else -np.inf
def grid_worst(A, t):
    P = np.abs(A @ K)**2; pk = np.flatnonzero((P > np.roll(P, 1)) & (P > np.roll(P, -1)))
    m0 = pk[np.argmin(cdist(pc.PHI[pk], t))]
    side = [P[k] for k in pk if k != m0 and cdist(pc.PHI[k], t) > cone]
    return 10*np.log10(max(side)/P.max()) if side else -np.inf
ts = np.linspace(0, np.pi/4, 4501); res = [run(t) for t in ts]
edge = []
for (s, A), t in zip(res[::50], ts[::50]):
    P = np.abs(A @ KF)**2; edge.append(10*np.log10(P[cdist(PHIF, t) > cone].max()/P.max()))
print(f"{arr}: just outside the 30 deg band the stopped pattern is {min(edge):.1f} to {max(edge):.1f} dB")
flat, hair = [], []
for i in range(len(ts) - 1):
    s0, s1 = res[i][0], res[i+1][0]
    if s0 == s1: continue
    lo, hi = ts[i], ts[i+1]
    for _ in range(60):
        mid = 0.5*(lo + hi)
        if run(mid)[0] == s0: lo = mid
        else: hi = mid
    for t in (lo, hi):
        s, A = run(t); c = cont_worst(A, t); P = np.abs(A @ K)**2; thr = P.max()/100
        pl = [m for m in range(M) if P[m] > thr and abs(P[m] - P[(m+1) % M]) <= 1e-12*P[m] and cdist(pc.PHI[m], t) > cone]
        if pl: flat.append((np.degrees(t), len(s), 10*np.log10(P[pl[0]]/P.max())))
        elif c > -20: hair.append((np.degrees(t), len(s), c, grid_worst(A, t)))
lv = sorted(f[2] for f in flat)
print(f"{arr}: {len(flat)} stops with an invisible flat top, missed sidelobe {lv[0]:.2f} to {lv[-1]:.2f} dB" if flat else f"{arr}: no flat-top stops")
z = [f for f in flat if f[1] == 0]
if z: print(f"{arr}: stops after no correction near {', '.join(f'{f[0]:.3f}' for f in z[:3])} deg")
print(f"{arr}: {len(hair)} stops with a true peak above -20 dB between grid points" + (f", excess at most {max(h[2] for h in hair) + 20:.5f} dB" if hair else ""))
