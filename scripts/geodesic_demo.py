"""The factor at the midpoint of the continued-fraction period of sqrt(N) (real quadratic picture).
usage: python3 scripts/geodesic_demo.py <seed>"""
import sys, random
from math import isqrt, gcd
from _common import *
from clsgrp.forms import rand_prime
def cf_period(N):
    a0 = isqrt(N); m, d, a = 0, 1, a0; ds = [1]
    while True:
        m = d * a - m; d = (N - m * m) // d; a = (a0 + m) // d; ds.append(d)
        if d == 1: return ds
rng = random.Random(int(sys.argv[1])); rows = []
for _ in range(8):
    p = rand_prime(16, rng); q = rand_prime(16, rng); N = p * q
    if p == q: continue
    ds = cf_period(N); L = len(ds) - 1
    if L % 2 == 0:
        g = gcd(ds[L // 2], N); verdict = "factor" if 1 < g < N else "trivial"
    else: g = None; verdict = "odd period"
    rows.append(dict(N=N, p=p, q=q, period=L, mid=ds[L // 2] if L % 2 == 0 else None, gcd=g, verdict=verdict))
    print(f"N={N}={p}*{q} period {L}: {verdict}" + (f" ({g})" if verdict == 'factor' else ""))
save("geodesic_demo", rows)
