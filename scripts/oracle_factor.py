"""Theorem 1 run: factor N using only the class number h (from PARI) and form arithmetic.
usage: python3 scripts/oracle_factor.py <bits> <seed>"""
import sys, random, time
from _common import *
from clsgrp.forms import *
from clsgrp import pari

bits, seed = int(sys.argv[1]), int(sys.argv[2])
rng = random.Random(seed); p, q, N = random_semiprime(bits, rng); D = -N; ident = identity(D)
t0 = time.time(); h = pari.class_number(D); t_h = time.time() - t0
print(f"N = {N} ({N.bit_length()} bits); oracle h = {h} ({t_h:.1f}s), h even: {h % 2 == 0}")
k = 0; m = h
while m % 2 == 0: m //= 2; k += 1
fb = [f for _, f in first_prime_forms(D, 12, start=2)]
result = None
for trial in range(1, 11):
    g = ident
    for f in fb: g = compose(g, power(f, rng.randrange(1 << 20), D), D)
    x = power(g, m, D)
    if x == ident: print(f"trial {trial}: odd-order class, retry"); continue
    sq = 0
    while True:
        y = compose(x, x, D); sq += 1
        if y == ident: break
        x = y
    fac = sorted(factor_from_ambiguous(D, N, [x]))[0]
    print(f"trial {trial}: {sq} squarings to the order-2 class {x}; factor {fac}")
    result = dict(trial=trial, squarings=sq, factor=fac, ok=fac * (N // fac) == N); break
save(f"oracle_{N.bit_length()}", dict(bits=N.bit_length(), N=N, p=p, q=q, h=h, k=k, t_h=t_h, **result))
