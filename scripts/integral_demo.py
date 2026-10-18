"""h(-N) = (1/N) int_0^N S(y) dy with S the running Jacobi-symbol sum; then factor from h. Side demonstration, not in the paper.
usage: python3 scripts/integral_demo.py <bits> <seed>"""
import sys, random, time
from _common import *
from clsgrp.forms import *
bits, seed = int(sys.argv[1]), int(sys.argv[2]); rng = random.Random(seed); runs = []
for _ in range(4):
    p, q, N = random_semiprime(bits, rng); D = -N; t0 = time.time(); S = 0; integral = 0
    for m in range(1, N): S += jacobi(m, N); integral += S
    h_int = integral // N; h_true = len(reduced_forms(D))
    fac, w = order2_factor(D, N, h_int, [f for _, f in first_prime_forms(D, 6)])
    runs.append(dict(N=N, p=p, q=q, h_integral=h_int, exact=(integral % N == 0), h_enum=h_true, factor=fac, time=time.time() - t0))
    print(f"N={N}={p}*{q}: (1/N)∫S = {h_int} (integer {integral % N == 0}), h = {h_true}, factor {fac}")
save("integral_demo", runs)
