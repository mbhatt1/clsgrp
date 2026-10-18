"""Assemble the per-step cost comparison (Table 3, Fig. 1) from the measured components.
usage: python3 scripts/compare.py <bits of N>"""
import sys, math, random
from _common import *
from clsgrp.forms import random_semiprime, first_prime_forms

n = int(sys.argv[1]); h = n // 2; T0 = h * h
nud = load(f"nudupl_{n}"); inv = load(f"rev_gcd_{h}"); par = load(f"rev_partial_{h}")
d = int(round(n ** 0.5)); c = 8
# Bits of the subset product prod p_l over the d smallest split primes: a reversible circuit must be
# sized for the full product (all exponent bits set), so take the worst case over seeded moduli.
SEEDS = range(8); prods = []; elld = []
for s_ in SEEDS:
    _, _, N = random_semiprime(n, random.Random(1000 + s_))
    ls = [l for l, _ in first_prime_forms(-N, d)]
    prods.append(sum(math.log2(l) for l in ls)); elld.append(ls[-1])
sigma = math.ceil(max(prods))
print(f"subset product: {min(prods):.0f}-{max(prods):.0f} bits (sigma = {sigma}), l_d in {min(elld)}-{max(elld)}")
small_arith = (2 * h * sigma * 2 + 2 * (h + sigma) ** 2 + 3 * h * (h + sigma) + 2 * sigma * sigma * 2) / T0
small_euc = 8 * 1.15 * h * (2.88 * sigma) / T0 + 1.0
int_step = (2 * n * n + n * n) / T0 + (2 * n * sigma + n * n) / T0
arith = nud["arith_toffoli_units"]
comp = {
 "garbage": dict(inverse=inv["fwd_units"], partial=par["fwd_units"], arith=arith, small=small_arith + small_euc),
 "clean":   dict(inverse=inv["clean_units"], partial=par["clean_units"], arith=1.5 * arith, small=1.5 * small_arith + 2 * small_euc),
}
tot_class = (d + 4) * (h / d + c); tot_int = (d + 4) * (n / d + c); step_ratio = tot_class / tot_int
out = dict(n=n, nprime=h, d=d, sigma=sigma, subset_bits_min=min(prods), subset_bits_max=max(prods),
           ell_d_min=min(elld), ell_d_max=max(elld), int_step=int_step, step_ratio=step_ratio, tot_class_steps=tot_class, tot_int_steps=tot_int,
           small_arith=small_arith, small_euc=small_euc)
# the integer step's products and reductions get the same 1.5x arithmetic uncompute overhead
ints = {"garbage": int_step, "clean": 1.5 * int_step}
for k, v in comp.items():
    cls = sum(v.values()); it = ints[k]
    v = dict(v, total=cls, int=it, per_step_ratio=cls / it, total_ratio=step_ratio * cls / it,
             R=(v["inverse"] + v["partial"]) / 1.5 / 2); out[k] = v
    print(f"{k:8s}: class step {cls:6.1f}  int step {it:5.1f}  per-step {cls / it:.2f}x  total {step_ratio * cls / it:.2f}x  R={v['R']:.1f}")
# hero-figure split: 'partial' segment includes the small-form Euclid, 'arith' includes the small-form products
for k in ("garbage", "clean"):
    f = 1.0 if k == "garbage" else 2.0; g = 1.0 if k == "garbage" else 1.5
    out[k]["fig_partial"] = out[k]["partial"] + f * small_euc; out[k]["fig_arith"] = out[k]["arith"] + g * small_arith
save(f"cost_{n}", out)
