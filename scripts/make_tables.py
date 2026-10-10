"""Generate paper/tables/*.tex from results/*.json."""
import glob, os
from _common import *
TAB = os.path.join(ROOT, "paper", "tables"); os.makedirs(TAB, exist_ok=True)
def w(name, text):
    open(os.path.join(TAB, name + ".tex"), "w").write(text); print(f"-> paper/tables/{name}.tex")
def fmt_time(t):
    return f"{t:.1f} s" if t < 100 else (f"{t/60:.1f} min" if t < 3600 else f"{t/3600:.1f} h")
# Table I
rows = sorted((load(os.path.basename(f)[:-5]) for f in glob.glob(os.path.join(RESULTS, "classical_*.json"))), key=lambda r: r["bits"])
body = "".join(f"{r['bits']} & {r['fb_size']} & {r['relations']} & ${r['trials']/10**int(len(str(r['trials']))-1):.1f}\\times10^{{{len(str(r['trials']))-1}}}$ & {fmt_time(r['total_time'])}{'$^*$' if r.get('recorded') else ''}\\\\\n" for r in rows)
w("classical", "\\begin{tabular}{rrrrr}\n\\toprule\nbits & factor base & relations & trials & time \\\\\n\\midrule\n" + body + "\\bottomrule\n\\end{tabular}")
# Table II
rows = sorted((load(os.path.basename(f)[:-5]) for f in glob.glob(os.path.join(RESULTS, "sim_*.json"))), key=lambda r: (r["bits"], -r["eta"]))
def res(r):
    if r["ok"]: return f"index {r['index']}, factored" + (f", {r['time']:.1f} s" if r["eta"] == r["Dp"] // 2 else "")
    return "no relations recovered" if r["n_verified"] < r["d"] else "not factored"
body = "".join(f"{r['bits']} & {r['d']} & {r['m']} & {r['B']} & {r['Dp']} & $2^{{-{r['eta']}}}$ & {res(r)}\\\\\n" for r in rows)
w("sim", "\\begin{tabular}{rrrrrrl}\n\\toprule\nbits & $d$ & runs & $B$ & $D'$ & noise & result \\\\\n\\midrule\n" + body + "\\bottomrule\n\\end{tabular}")
# Table III
c = load("cost_4096"); g, k = c["garbage"], c["clean"]
body = (f"modular inverse (measured) & {g['inverse']:.1f} & {k['inverse']:.1f}\\\\\n"
        f"partial Euclid (measured) & {g['partial']:.1f} & {k['partial']:.1f}\\\\\n"
        f"NUDUPL products, divisions (measured) & {g['arith']:.1f} & {k['arith']:.1f}\\\\\n"
        f"small-form composition (modelled) & {g['small']:.1f} & {k['small']:.1f}\\\\\n\\midrule\n"
        f"class-group step & {g['total']:.0f} & {k['total']:.0f}\\\\\n"
        f"integer Regev step (modelled) & {c['int_step']:.1f} & {c['int_step']:.1f}\\\\\n"
        f"total ratio after $\\times{c['step_ratio']:.2f}$ & ${g['total_ratio']:.1f}\\times$ & ${k['total_ratio']:.1f}\\times$\\\\\n")
w("cost", "\\begin{tabular}{lrr}\n\\toprule\ncomponent & garbage kept & clean \\\\\n\\midrule\n" + body + "\\bottomrule\n\\end{tabular}")
