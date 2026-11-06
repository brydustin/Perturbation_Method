"""Changed method (G_Method.thy): peak = >= both neighbours and > one; the main peak and its two
neighbours are excluded; threshold max/100 - dl.  Sweep [0, pi/4], bisect at sequence changes.
Reports the most corrections (first-index tie rule) and the worst true pattern outside the main
lobe arc at the stops (64x finer grid).  usage: sim_changed.py dc|oct dl [band_deg]"""
import sys, os, numpy as np
sys.path.insert(0, '/home/dusty/Desktop/Matlab_UH_Project/Proof/Termination_Counterexample')
import pm_core as pc
arr, dl = sys.argv[1], float(sys.argv[2])
band = np.deg2rad(float(sys.argv[3])) if len(sys.argv) > 3 else None
if arr == 'dc':
    a, b = 0.042211347450806, 0.039173549691350
    x = np.array([0, -a, a, 0, 0, b, -b, -b, b]); y = np.array([0, 0, 0, a, -a, b, b, -b, -b])
else:
    x, y = pc.octagon9(0.04880)
N = 9; M = pc.M; h = 2*np.pi/M
K = pc.steer(x, y, pc.PHI)
PHIF = np.linspace(0, 2*np.pi, M*64, endpoint=False); KF = pc.steer(x, y, PHIF)
def cdist(u, v): return np.abs(np.angle(np.exp(1j*(u - v))))
def st(ph): return np.exp(1j*pc.K0*(x*np.cos(ph) + y*np.sin(ph)))
def fpeaks(P):
    pr, nx = np.roll(P, 1), np.roll(P, -1)
    return np.flatnonzero((P >= pr) & (P >= nx) & ((P > pr) | (P > nx)))
def run(t, upto=None):
    A = np.exp(-1j*pc.K0*(x*np.cos(t) + y*np.sin(t))); seq = []
    while True:
        P = np.abs(A @ K)**2; pk = fpeaks(P)
        m0 = pk[np.argmin(cdist(pc.PHI[pk], t))]
        thr = P.max()/100 - dl
        E = [m for m in pk if m not in (m0, (m0-1) % M, (m0+1) % M) and P[m] > thr
             and (band is None or cdist(pc.PHI[m], t) > band)]
        if not E or len(seq) > 60 or (upto is not None and len(seq) >= upto):
            return tuple(seq), A, P, m0, thr
        s = max(E, key=lambda m: (P[m], -m)); v = st(pc.PHI[s])
        A = A - (A @ v)/N*np.conj(v); seq.append(s)
def worst(t):
    seq, A, P, m0, thr = run(t); c = P.max()/100
    ab = P > thr; lo = hi = m0
    while ab[(lo-1) % M] and (lo-1) % M != m0: lo -= 1
    while ab[(hi+1) % M] and (hi+1) % M != m0: hi += 1
    a0, a1 = (lo-1)*h, (hi+1)*h
    out = np.mod(PHIF - a0, 2*np.pi) > (a1 - a0)
    if band is not None: out &= cdist(PHIF, t) > band
    PF = np.abs(A @ KF)**2
    return len(seq), (PF[out].max()/c if out.any() else 0.0)
ts = np.linspace(0, np.pi/4, 4501); seqs = [run(t)[0] for t in ts]; pts = list(ts)
for i in range(len(ts) - 1):
    if seqs[i] == seqs[i+1]: continue
    u, v = ts[i], ts[i+1]
    for _ in range(60):
        w = 0.5*(u + v)
        if run(w)[0] == seqs[i]: u = w
        else: v = w
    pts += [u, v]
res = [worst(t) for t in pts]
print(f"{arr} dl={dl} band={sys.argv[3] if band is not None else 'none'}: {len(pts)} foci "
      f"({len(pts)-len(ts)} at sequence changes); most corrections {max(r[0] for r in res)}; "
      f"worst true pattern outside the main lobe {10*np.log10(max(r[1] for r in res)) - 20:.3f} dB")
