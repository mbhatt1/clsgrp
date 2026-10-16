"""Check the classes of order two for D = -4N, N = pq = 1 (mod 4), N < bound (Section 3.3).
usage: python3 scripts/ambiguous_1mod4.py <bound>"""
import sys
from math import gcd
from _common import *
from clsgrp.forms import reduced_forms, is_prime

bound = int(sys.argv[1]); checked = 0; failures = []
for N in range(5, bound, 4):
    if not any(N % p == 0 and is_prime(p) and is_prime(N // p) and p != N // p for p in range(3, int(N ** .5) + 1)):
        continue
    checked += 1
    amb = [f for f in reduced_forms(-4 * N) if (f[1] == 0 or f[1] == f[0] or f[0] == f[2]) and f != (1, 0, N)]
    g = sorted(gcd(a if (b == 0 or b == a) else 2 * a - b, N) for a, b, c in amb)
    if not (len(amb) == 3 and (2, 2, (N + 1) // 2) in amb and g[0] == 1 and all(1 < y < N for y in g[1:])):
        failures.append(N)
print(f"{checked} moduli N = 1 (mod 4) below {bound}: {len(failures)} failures")
save(f"ambiguous_1mod4_{bound}", dict(bound=bound, checked=checked, failures=failures))
