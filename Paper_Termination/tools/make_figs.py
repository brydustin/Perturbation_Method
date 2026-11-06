"""Figures for the paper: array layouts, one run of the double cross, corrections versus focus.
Simulations use the floating-point port pm_core.py (same rules as perturb_method_v25b.m)."""
import os, sys
for _v in ("OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "OMP_NUM_THREADS"): os.environ[_v] = "1"
import numpy as np
import matplotlib
matplotlib.use("pdf")
import matplotlib.pyplot as plt
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TC = os.path.join(os.path.dirname(HERE), "Termination_Counterexample")
sys.path.insert(0, TC)
from pm_core import run, PHI
matplotlib.rcParams.update({"pdf.fonttype": 42, "font.family": "DejaVu Sans", "font.size": 8,
                            "mathtext.fontset": "dejavusans", "axes.linewidth": 0.6})
INK, INK2, GRIDC = "#0b0b0b", "#52514e", "#e6e5e1"
AXC, DGC = "#2a78d6", "#eb6834"
FIG = os.path.join(HERE, "figs")

def pos(name):
    return np.loadtxt(os.path.join(TC, "checker", name)) * 1000.0

def tidy(ax):
    for s in ("top", "right"): ax.spines[s].set_visible(False)
    ax.tick_params(colors=INK2, labelsize=7, length=2)
    ax.grid(color=GRIDC, lw=0.5); ax.set_axisbelow(True)

# Figure 1: layouts
fig, axs = plt.subplots(1, 3, figsize=(6.5, 2.55), gridspec_kw={"width_ratios": [1, 1, 1]})
for ax, (fname, title) in zip(axs[:2], [("double_cross.txt", "double cross"), ("octagon_d4.txt", "octagon")]):
    xy = pos(fname); r = np.hypot(xy[:, 0], xy[:, 1])
    a = np.degrees(np.arctan2(xy[:, 1], xy[:, 0])) % 90
    c = r < 1e-6; axm = ~c & (np.minimum(a, 90 - a) < 1); dg = ~c & ~axm
    t = np.linspace(0, 2 * np.pi, 400)
    for rr, col in ((r[axm].mean(), AXC), (r[dg].mean(), DGC)):
        ax.plot(rr * np.cos(t), rr * np.sin(t), color=col, lw=0.6, ls=(0, (3, 2)), alpha=0.7)
    ax.plot(xy[axm, 0], xy[axm, 1], "o", color=AXC, ms=5, mec="white", mew=0.8, label=r"axes, radius $\rho_+$")
    ax.plot(xy[dg, 0], xy[dg, 1], "s", color=DGC, ms=4.6, mec="white", mew=0.8, label=r"diagonals, radius $\rho_\times$")
    ax.plot(xy[c, 0], xy[c, 1], "o", color=INK, ms=5, mec="white", mew=0.8, label="centre")
    ax.set_xlim(-68, 68); ax.set_ylim(-68, 68); ax.set_aspect("equal"); tidy(ax)
    ax.set_title(title, fontsize=8, color=INK)
    ax.text(0, -64, f"$\\rho_+$ = {r[axm].mean():.2f} mm, $\\rho_\\times$ = {r[dg].mean():.2f} mm", ha="center", va="bottom", fontsize=6.3, color=INK2)
    ax.set_xlabel("x (mm)", fontsize=7, color=INK2)
axs[0].set_ylabel("y (mm)", fontsize=7, color=INK2)
h, l = axs[0].get_legend_handles_labels()
fig.legend(h, l, loc="lower center", ncol=3, fontsize=6.5, frameon=False, handletextpad=0.3, columnspacing=1.6)
ax = axs[2]; L, R = 32, 400.0; th = 2 * np.pi * np.arange(L) / L
ax.plot(R * np.cos(th), R * np.sin(th), "o", color=INK, ms=3.2, mec="white", mew=0.5)
t = np.linspace(0, 2 * np.pi, 400)
ax.plot(55.4 * np.cos(t), 55.4 * np.sin(t), color=INK2, lw=0.6, ls=(0, (1.5, 1.5)))
ax.annotate("nine-element\narrays", xy=(-39, -39), xytext=(-260, -210), fontsize=6, color=INK2, ha="center",
            arrowprops=dict(arrowstyle="-", color=INK2, lw=0.5))
ax.set_xlim(-460, 460); ax.set_ylim(-460, 460); ax.set_aspect("equal"); tidy(ax)
ax.set_title("circular array", fontsize=8, color=INK)
ax.text(0, -450, "32 elements, radius 400 mm", ha="center", va="bottom", fontsize=6.3, color=INK2)
ax.set_xlabel("x (mm)", fontsize=7, color=INK2)
fig.tight_layout(w_pad=1.0, rect=(0, 0.07, 1, 1))
fig.savefig(os.path.join(FIG, "layouts.pdf")); plt.close(fig)

# Figure 2: one run of the double cross
xy = pos("double_cross.txt") / 1000.0; t0 = np.deg2rad(17.9); band = np.deg2rad(30)  # metres for the simulation
r = run(xy[:, 0], xy[:, 1], t0, -20.0, band, max_iter=100, record=True)
from pm_core import steer
K = steer(xy[:, 0], xy[:, 1], PHI)
def level(A):
    P = np.abs(A @ K) ** 2
    return 10 * np.log10(np.maximum(P / P.max(), 1e-12))
A0 = np.conj(steer(xy[:, 0], xy[:, 1], t0)[:, 0])
deg = np.degrees(PHI)
fig, axs = plt.subplots(2, 1, figsize=(6.5, 3.4), sharex=True)
for ax, A, ttl in ((axs[0], A0, "initial excitation (steered to the focus)"),
                   (axs[1], r["A_eff"], f"after {r['iters']} corrections (ticks: corrected directions): the method stops")):
    ax.axvspan(17.9 - 30, 17.9 + 30, color="#f0efec", lw=0)
    ax.plot(deg, level(A), color=AXC, lw=0.9)
    ax.axhline(-20, color=INK2, lw=0.7, ls=(0, (4, 2)))
    ax.set_ylim(-40, 2); ax.set_xlim(0, 360); tidy(ax)
    ax.set_ylabel("level (dB)", fontsize=7, color=INK2)
    ax.text(0.995, 0.96, ttl, transform=ax.transAxes, ha="right", va="top", fontsize=7, color=INK)
axs[0].text(17.9, -38.5, "band", ha="center", fontsize=6.5, color=INK2)
axs[0].text(358, -19, "$-20$ dB", ha="right", va="bottom", fontsize=6.5, color=INK2)
for k, s in enumerate(r["trace"]["sel_idx"]):
    axs[1].plot([deg[s]] * 2, [-40, -37], color=DGC, lw=1.0)
axs[1].set_xlabel("azimuth (degrees)", fontsize=7, color=INK2)
axs[1].set_xticks(range(0, 361, 45))
fig.tight_layout(h_pad=0.4)
fig.savefig(os.path.join(FIG, "run_double_cross.pdf")); plt.close(fig)
print("run:", r["iters"], [round(float(deg[s]), 1) for s in r["trace"]["sel_idx"]])

# Figure 3: corrections used versus focus angle (one tie rule, floating point)
foc = np.linspace(0, 360, 3601)[:-1]
arrays = (("double cross", "double_cross.txt", 20, AXC), ("octagon", "octagon_d4.txt", 10, DGC))
fig, axs = plt.subplots(2, 1, figsize=(6.5, 2.7), sharex=True)
summary = {}
for ax, (name, fname, bound, col) in zip(axs, arrays):
    q = pos(fname) / 1000.0
    res = {}
    for b, lab in ((band, "band"), (None, "none")):
        n = []
        for f in foc:
            rr = run(q[:, 0], q[:, 1], np.deg2rad(f), -20.0, b, max_iter=1000, record=False)
            n.append(rr["iters"] if rr["terminated"] else np.nan)
        res[lab] = np.array(n)
    same = bool(np.array_equal(res["band"], res["none"], equal_nan=True))
    n = res["band"]
    summary[name] = (int(np.sum(~np.isnan(n))), int(np.nanmax(n)), float(np.nanmean(n)), same,
                     int(np.nanmax(res["none"])), int(np.sum(~np.isnan(res["none"]))))
    ax.plot(foc, n, ".", ms=1.2, color=col)
    if not same:
        ax.plot(foc, res["none"], ".", ms=0.8, color=INK2)
    ax.axhline(bound, color=INK2, lw=0.7, ls=(0, (4, 2)))
    ax.set_ylim(0, 25.5); ax.set_yticks([0, 5, 10, 15, 20]); tidy(ax)
    note = "same without the band" if same else "grey: without the band"
    ax.text(0.995, 0.97, f"{name}: at most {int(np.nanmax(n))} corrections, mean {np.nanmean(n):.1f} ({note})",
            transform=ax.transAxes, ha="right", va="top", fontsize=7, color=INK)
    ax.text(2, bound + 0.4, f"bound of the theorem ({bound})", fontsize=6.5, color=INK2, va="bottom")
    ax.set_ylabel("corrections", fontsize=7, color=INK2)
axs[1].set_xlabel("focus angle (degrees)", fontsize=7, color=INK2); axs[1].set_xticks(range(0, 361, 45)); axs[1].set_xlim(0, 360)
fig.tight_layout(h_pad=0.4)
fig.savefig(os.path.join(FIG, "corrections_vs_focus.pdf")); plt.close(fig)
for name, v in summary.items():
    print(name, "stopped(band)", v[0], "max", v[1], "mean", round(v[2], 2), "same_without_band", v[3], "max(none)", v[4], "stopped(none)", v[5])
