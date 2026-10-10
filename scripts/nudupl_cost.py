"""NUDUPL squaring (derived identity f^2 ~ f(ax+Cy,y)/a with partial Euclid on (a,C)), validated
against composition, with an operation ledger. Section VI.A.
usage: python3 scripts/nudupl_cost.py <bits of N> <trials> <seed>"""
import sys, random, time
from _common import *
from clsgrp.forms import *

class Ledger:
    def __init__(s): s.reset()
    def reset(s): s.mul = []; s.euc = []
L = Ledger()
def M_(x, y): L.mul.append((x.bit_length(), y.bit_length())); return x * y
def DIV(x, y): L.mul.append((max(1, x.bit_length() - y.bit_length() + 1), y.bit_length())); return x // y
def xgcd_full(a, b):
    w = max(a.bit_length(), b.bit_length()); x0, x1, y0, y1 = 1, 0, 0, 1
    while b:
        q, a, b = a // b, b, a % b; x0, x1 = x1, x0 - q * x1; y0, y1 = y1, y0 - q * y1
    L.euc.append((w, w)); return a, x0, y0

def nudupl(f, D):
    a, b, c = f; Lb = isqrt(isqrt(abs(D) // 4))
    d1, u, v = xgcd_full(b, a)
    if d1 != 1: return None, -1
    C = (-M_(c, u)) % a
    if a - C < C: C = C - a
    w = a.bit_length(); start = abs(C).bit_length(); r0, r1 = a, C; s0, s1 = 0, 1
    while abs(r1) > Lb:
        qq = r0 // r1; r0, r1 = r1, r0 - qq * r1; s0, s1 = s1, s0 - qq * s1
    L.euc.append((w, start - abs(r1).bit_length())); d, v = r0, r1
    if d * s1 - v * s0 != a: v, s1 = -v, -s1
    assert d * s1 - v * s0 == a
    e1 = DIV(M_(b, d) + M_(c, s0), a); e = DIV(M_(b, v) + M_(c, s1), a)
    a2 = M_(d, d) + M_(s0, e1); b2 = 2 * M_(d, v) + M_(s1, e1) + M_(s0, e); c2 = M_(v, v) + M_(s1, e)
    assert b2 * b2 - 4 * a2 * c2 == D
    steps = 0
    while True:
        if -a2 < b2 <= a2 and a2 <= c2:
            if a2 == c2 and b2 < 0: b2 = -b2
            break
        if a2 > c2: a2, b2, c2 = c2, -b2, a2; steps += 1; continue
        bn = a2 - ((a2 - b2) % (2 * a2)); c2 = DIV(M_(bn, bn) - D, 4 * a2); b2 = bn; steps += 1
    return (a2, b2, c2), steps

def main(bits, trials, seed):
    rng = random.Random(seed); p, q, N = random_semiprime(bits, rng); D = -N; n = N.bit_length(); h = n // 2
    fb = [f for _, f in first_prime_forms(D, 8)]; unit = h * h
    used = ok = skipped = 0; area = full = part = red = 0.0; toff = 0.0; t0 = time.time()
    while used < trials:
        f = random_reduced_form(D, rng, fb); L.reset(); g, st = nudupl(f, D)
        if g is None: skipped += 1; continue
        ok += (g == compose(f, f, D)); used += 1
        area += sum(x * y for x, y in L.mul) / unit; toff += (sum(2 * x * y for x, y in L.mul) + 3 * h * h) / unit
        full += L.euc[0][0] * L.euc[0][1] / unit; part += L.euc[1][0] * L.euc[1][1] / unit; red += st
    out = dict(n=n, nprime=h, trials=used, ok=ok, skipped_gcd_gt1=skipped, mul_area_M=area / used,
               full_xgcd_area_M=full / used, partial_euclid_area_M=part / used, final_reduction_steps=red / used,
               arith_toffoli_units=toff / used, time=time.time() - t0)
    print(f"n={n}: NUDUPL == compose on {ok}/{used}; arithmetic {out['mul_area_M']:.2f} M area, "
          f"XGCD {out['full_xgcd_area_M']:.2f}, partial {out['partial_euclid_area_M']:.2f}, "
          f"arith Toffolis {out['arith_toffoli_units']:.1f} n'^2, reduction steps {out['final_reduction_steps']:.2f}")
    save(f"nudupl_{n}", out)

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
