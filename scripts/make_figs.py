"""Generate paper/fig1_scaling.png and paper/fig_hero.png from results/*.json."""
import glob, os
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, Rectangle
import numpy as np
from math import log, sqrt
from _common import *
OUT = os.path.join(ROOT, "paper")
SURF="#fcfcfb"; INK="#0b0b0b"; INK2="#52514e"; MUTED="#898781"; GRID="#e1e0d9"; AXIS="#c3c2b7"
BLUE="#2a78d6"; ORANGE="#eb6834"; AQUA="#1baf7a"; DEEMPH="#c3c2b7"
plt.rcParams.update({"font.family": ["Helvetica Neue","Helvetica","Arial","DejaVu Sans"], "font.size": 9.5,
    "axes.edgecolor": AXIS, "axes.linewidth": 0.8, "xtick.color": MUTED, "ytick.color": MUTED, "axes.labelcolor": INK2, "text.color": INK})
def style(ax, grid_axis):
    for s in ("top","right"): ax.spines[s].set_visible(False)
    ax.set_facecolor(SURF); ax.grid(True, axis=grid_axis, color=GRID, linewidth=0.8); ax.set_axisbelow(True); ax.tick_params(length=0)

# ---- Fig. 2 (scaling)
rows = sorted((load(os.path.basename(f)[:-5]) for f in glob.glob(os.path.join(RESULTS, "classical_*.json"))), key=lambda r: r["bits"])
bits = np.array([r["bits"] for r in rows]); secs = np.array([r["total_time"] for r in rows])
X = np.array([sqrt(b*log(2)*log(b*log(2))) for b in bits]); c, k = np.polyfit(X, np.log(secs), 1)
bb = np.linspace(bits.min()-5, bits.max()+10, 200); fit = np.exp(k + c*np.array([sqrt(b*log(2)*log(b*log(2))) for b in bb]))
fig, ax = plt.subplots(figsize=(7.2, 4.2), dpi=200, facecolor=SURF); style(ax, "y")
ax.plot(bb, fit, color=DEEMPH, linewidth=2, solid_capstyle="round", zorder=1)
ax.plot(bits, secs, color=BLUE, linewidth=2, solid_capstyle="round", zorder=2)
ax.scatter(bits, secs, s=64, color=BLUE, edgecolor=SURF, linewidth=2, zorder=3)
ax.set_yscale("log"); ax.set_yticks([0.1, 1, 60, 3600, 86400]); ax.set_yticklabels(["0.1 s","1 s","1 min","1 h","1 day"])
ax.set_xlabel("Modulus size (bits)"); ax.set_xlim(bits.min()-10, bits.max()+12)
ax.set_title("Classical class-group factoring: wall time vs modulus size", loc="left", fontsize=12, color=INK, pad=14)
ax.text(0, 1.015, f"{len(rows)} runs of the Schnorr–Lenstra method; gray curve is the fitted L[1/2] growth (c = {c:.2f})", transform=ax.transAxes, fontsize=9, color=INK2)
for r in rows[-2:]:
    t = r["total_time"]; lab = f"{t/3600:.1f} h" if t > 3600 else f"{t/60:.1f} min"
    ax.annotate(f"{r['bits']} bits: {lab}", (r["bits"], t), xytext=(-8, 8), textcoords="offset points", ha="right", fontsize=9, color=INK2)
fig.tight_layout(); fig.savefig(os.path.join(OUT, "fig1_scaling.png"), facecolor=SURF); plt.close(fig); print("-> paper/fig1_scaling.png", f"c={c:.2f}")

# ---- Fig. 1 (hero)
cst = load("cost_4096"); g, kc = cst["garbage"], cst["clean"]
rows = [("Integer Regev step", [0, 0, cst["int_step"]]),
        ("Class group, garbage kept", [g["inverse"], g["fig_partial"], g["fig_arith"]]),
        ("Class group, fully uncomputed", [kc["inverse"], kc["fig_partial"], kc["fig_arith"]])]
cats = ["Modular inverse (Euclid)", "Partial Euclid", "Multiplications and divisions"]; cols=[BLUE, ORANGE, AQUA]
fig = plt.figure(figsize=(9.0, 3.4), dpi=220, facecolor=SURF)
gs = fig.add_gridspec(1, 2, width_ratios=[2.5, 1], left=0.26, right=0.965, top=0.80, bottom=0.17, wspace=0.42)
ax = fig.add_subplot(gs[0]); style(ax, "x"); ax.grid(False, axis="y")
H=0.3; xmax = 150; ax.set_xlim(0, xmax); ax.set_ylim(-0.55, 2.55); fig.canvas.draw()
bb=ax.get_window_extent(); r_x=4/(bb.width/xmax); aspect=(xmax/bb.width)/(3.1/bb.height)
for i,(name,vals) in enumerate(rows):
    y=2-i; x=0
    for j,v in enumerate(vals):
        if v<=0: continue
        last=all(vv<=0 for vv in vals[j+1:])
        P = FancyBboxPatch((x,y-H/2),v,H,boxstyle=f"round,pad=0,rounding_size={r_x}",mutation_aspect=aspect,facecolor=cols[j],edgecolor=SURF,linewidth=2,zorder=3) if last else Rectangle((x,y-H/2),v,H,facecolor=cols[j],edgecolor=SURF,linewidth=2,zorder=3)
        ax.add_patch(P); x+=v
    ax.text(x+2.5,y,f"{x:.0f}",va="center",ha="left",fontsize=9,color=INK2)
ax.set_yticks([0,1,2]); ax.set_yticklabels([r[0] for r in rows][::-1], color=INK2)
ax.set_xlabel("Toffolis per sequential squaring step, units of n\u2032\u00b2 (n\u2032 = 2048)")
ax.set_title("(a) One squaring step, 4096-bit modulus", loc="left", fontsize=10, color=INK, pad=8)
fig.legend([Rectangle((0,0),1,1,facecolor=c) for c in cols], cats, loc="upper left", bbox_to_anchor=(0.26, 0.955), ncol=3, frameon=False, fontsize=8.5, labelcolor=INK2, handlelength=1.2, columnspacing=1.3)
ax2 = fig.add_subplot(gs[1]); style(ax2, "y")
vals=[g["total_ratio"], kc["total_ratio"]]; labels=["garbage\nkept","fully\nuncomputed"]
ax2.set_xlim(-0.6,1.6); ax2.set_ylim(0,5); fig.canvas.draw()
bb2=ax2.get_window_extent(); W=0.5; r_y=4/(bb2.height/5); asp2=(2.2/bb2.width)/(5/bb2.height)
for i,v in enumerate(vals):
    ax2.add_patch(FancyBboxPatch((i-W/2,0),W,v,boxstyle=f"round,pad=0,rounding_size={r_y}",mutation_aspect=1/asp2,facecolor=BLUE,edgecolor=SURF,linewidth=2,zorder=3))
    ax2.text(i, v+0.12, f"{v:.1f}\u00d7", ha="center", va="bottom", fontsize=9, color=INK2)
ax2.axhline(1.0, color=INK2, linewidth=1.0, zorder=2); ax2.text(0.5, 1.06, "break-even", ha="center", va="bottom", fontsize=7.5, color=INK2)
ax2.set_xticks([0,1]); ax2.set_xticklabels(labels, color=INK2); ax2.set_yticks([0,1,2,3,4,5])
ax2.set_ylabel("total cost, class group / integers"); ax2.set_title(f"(b) Total, after {cst['step_ratio']:.2f}\u00d7 steps", loc="left", fontsize=10, color=INK, pad=8)
fig.savefig(os.path.join(OUT, "fig_hero.png"), facecolor=SURF); plt.close(fig); print("-> paper/fig_hero.png")
