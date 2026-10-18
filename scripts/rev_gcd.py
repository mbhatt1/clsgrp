"""Branch-free reversible modular inverse (Bernstein-Yang divsteps, cofactors mod the odd modulus),
executed classically with a Toffoli ledger. Section 6.3.
usage: python3 scripts/rev_gcd.py <n' bits> <trials> <seed>"""
import sys, random
from math import ceil, gcd
from _common import *

class Cost:
    toff = 0; hist = 0
    @classmethod
    def reset(c): c.toff = 0; c.hist = 0
def CSWAP(w): Cost.toff += w
def CADD(w): Cost.toff += 2 * w
def HALVE_MOD(w): Cost.toff += 2 * w
def SMALL(k): Cost.toff += k
def HIST(k): Cost.hist += k

def divstep_inverse(a, b, d):
    assert b & 1
    K = ceil((49 * d + 57) / 17); delta, f, g, p, q = 1, b, a % b, 0, 1; w = d + 1
    for _ in range(K):
        g0 = g & 1; s = 1 if (delta > 0 and g0) else 0; SMALL(14); HIST(2)
        if s: delta, f, g = -delta, g, f; p, q = q, p
        CSWAP(w); CSWAP(d)
        if g0: g = (f - g) if s else (g + f); q = (p - q) if s else (q + p)
        CADD(w); CADD(d); assert g % 2 == 0; g //= 2
        q = ((q + b) // 2) if (q & 1) else (q // 2); q %= b; HALVE_MOD(d)
        delta += 1; SMALL(12)
    assert g == 0 and f in (1, -1)
    v = p if f == 1 else (b - p) % b; CADD(d)
    return v, K

def main(nbits, trials, seed):
    rng = random.Random(seed); tot = hist = ok = 0
    for _ in range(trials):
        b = rng.getrandbits(nbits) | 1 | (1 << (nbits - 1))
        while True:
            a = rng.getrandbits(nbits) | (1 << (nbits - 1))
            if gcd(a, b) == 1: break
        Cost.reset(); v, K = divstep_inverse(a, b, nbits); ok += (v * a) % b == 1
        tot += Cost.toff; hist += Cost.hist
    fwd = tot / trials
    out = dict(nprime=nbits, trials=trials, ok=ok, K=K, fwd_toffoli=fwd, fwd_units=fwd / nbits ** 2,
               clean_units=2 * fwd / nbits ** 2, history_qubits=hist / trials, divstep_toffoli_per_n=fwd / K / nbits)
    print(f"n'={nbits}: inverse correct {ok}/{trials}, K={K}, forward {out['fwd_units']:.1f} n'^2, "
          f"clean {out['clean_units']:.1f} n'^2, history {out['history_qubits']:.0f} qubits")
    save(f"rev_gcd_{nbits}", out)

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
