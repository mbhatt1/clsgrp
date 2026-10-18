"""Reversible partial Euclid on (a, C) with integer cofactors: one full-width division, then
division steps with a 6-bit quotient budget and a done flag. Section 6.3.
usage: python3 scripts/rev_partial.py <n' bits> <trials> <seed>"""
import sys, random
from math import isqrt
from _common import *
from rev_gcd import Cost, CSWAP, HIST

QB = 6
def CMP(w): Cost.toff += w
def CSUB(w): Cost.toff += 2 * w
def PROD(w1, w2): Cost.toff += 2 * w1 * w2

def step_count(a, C, Lb):
    r0, r1, s0, s1, k = a, C, 0, 1, 0
    qq = abs(r0) // abs(r1); sg = 1 if (r0 >= 0) == (r1 >= 0) else -1; r0 -= sg * qq * r1; s0 -= sg * qq * s1
    if abs(r0) < abs(r1): r0, r1, s0, s1 = r1, r0, s1, s0
    while abs(r1) > Lb:
        qq = min(abs(r0) // abs(r1), (1 << QB) - 1); sg = 1 if (r0 >= 0) == (r1 >= 0) else -1
        r0 -= sg * qq * r1; s0 -= sg * qq * s1
        if abs(r0) < abs(r1): r0, r1, s0, s1 = r1, r0, s1, s0
        k += 1
    return k

def partial_euclid_rev(a, C, Lb, d, steps):
    r0, r1, s0, s1 = a, C, 0, 1; w = d; ws = d // 2 + 2; done = False
    qq = abs(r0) // abs(r1); sg = 1 if (r0 >= 0) == (r1 >= 0) else -1; r0 -= sg * qq * r1; s0 -= sg * qq * s1
    for _ in range(d): CMP(w); CSUB(w); HIST(1)
    PROD(d, ws); CSUB(ws)
    if abs(r0) < abs(r1): r0, r1, s0, s1 = r1, r0, s1, s0
    CMP(w); HIST(1); CSWAP(w); CSWAP(ws)
    for _ in range(steps):
        CMP(w); HIST(1)
        if abs(r1) <= Lb: done = True
        if not done:
            qq = min(abs(r0) // abs(r1), (1 << QB) - 1)
            for _ in range(QB): CMP(w); CSUB(w); HIST(1)
            sg = 1 if (r0 >= 0) == (r1 >= 0) else -1; r0 = r0 - sg * qq * r1
            PROD(QB, ws); CSUB(ws); s0 = s0 - sg * qq * s1
            CMP(w); HIST(1); CSWAP(w); CSWAP(ws)
            if abs(r0) < abs(r1): r0, r1, s0, s1 = r1, r0, s1, s0
        else:
            CMP(w); CSUB(w); Cost.toff += (QB - 1) * 3 * w; PROD(QB, ws); CSUB(ws); CMP(w); CSWAP(w); CSWAP(ws); HIST(QB + 1)
    return r0, r1, s0, s1, done

def main(d, trials, seed):
    rng = random.Random(seed); need = []
    inputs = []
    for _ in range(trials):
        a = rng.getrandbits(d) | (1 << (d - 1)); C = rng.randrange(-a // 2, a // 2); Lb = isqrt(a)
        inputs.append((a, C, Lb)); need.append(step_count(a, C, Lb))
    budget = int(max(need) * 1.15) + 8; tot = hist = ok = 0
    for a, C, Lb in inputs:
        Cost.reset(); r0, r1, s0, s1, done = partial_euclid_rev(a, C, Lb, d, budget)
        ok += done and abs(r0 * s1 - r1 * s0) == a and (r0 - s0 * C) % a == 0 and (r1 - s1 * C) % a == 0 and abs(r1) <= Lb
        tot += Cost.toff; hist += Cost.hist
    fwd = tot / trials
    out = dict(nprime=d, trials=trials, ok=ok, steps_avg=sum(need) / len(need), steps_max=max(need), budget=budget,
               quotient_bits=QB, fwd_toffoli=fwd, fwd_units=fwd / d ** 2, clean_units=2 * fwd / d ** 2, history_qubits=hist / trials)
    print(f"n'={d}: valid {ok}/{trials}; steps avg {out['steps_avg']:.0f} max {max(need)} budget {budget}; "
          f"forward {out['fwd_units']:.1f} n'^2, clean {out['clean_units']:.1f} n'^2")
    save(f"rev_partial_{d}", out)

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
