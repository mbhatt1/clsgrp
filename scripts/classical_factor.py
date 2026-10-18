"""Classical class-group factoring (Schnorr-Lenstra / Hafner-McCurley): Table 1, Fig. 2.
usage: python3 scripts/classical_factor.py <bits> <smoothness bound B> <seed>"""
import sys, random, time
from _common import *
from clsgrp.forms import *

def main(bits, B, seed):
    rng = random.Random(seed)
    p, q, N = random_semiprime(bits, rng)
    D = -N; ident = identity(D); t0 = time.time()
    fb = prime_forms_upto(D, B); d = len(fb)
    primes = [l for l, _ in fb]; idx = {l: i for i, l in enumerate(primes)}
    P = 1
    for l in primes: P *= l
    print(f"N = {N} ({N.bit_length()} bits); factor base {d} split primes up to {B}")
    rels = []; seen = set(); trials = 0; want = d + 24; cur = None; expo = None; walk = 0
    while len(rels) < want:
        if cur is None or walk > 200:
            expo = [0] * d; cur = ident
            for _ in range(12):
                i = rng.randrange(d); expo[i] += 1; cur = compose(cur, fb[i][1], D)
            walk = 0
        i = rng.randrange(d); expo[i] += 1; cur = compose(cur, fb[i][1], D); walk += 1; trials += 1
        a, b, c = cur
        x = a; g = gcd(x, P)
        while g > 1: x //= g; g = gcd(x, g)
        if x != 1: continue
        vec = list(expo); x = a
        for l in primes:
            if x % l == 0:
                f = 0
                while x % l == 0: x //= l; f += 1
                bl = fb[idx[l]][1][1]
                if (b - bl) % (2 * l) == 0: s = 1
                elif (b + bl) % (2 * l) == 0: s = -1
                else: raise RuntimeError("sign rule failed")
                vec[idx[l]] -= s * f
        tv = tuple(vec)
        if tv in seen: continue
        seen.add(tv); rels.append(vec); cur = None
    t1 = time.time()
    print(f"relations: {len(rels)} after {trials} trials ({t1 - t0:.1f}s)")
    v = rels[0]; chk = ident
    for i, e in enumerate(v):
        if e: chk = compose(chk, power(fb[i][1] if e > 0 else inverse(fb[i][1]), abs(e), D), D)
    assert chk == ident, "relation check failed"
    M = lattice_det(rels, d); t2 = time.time()
    assert M is not None, "lattice not full rank"
    print(f"lattice determinant: {M.bit_length()} bits ({t2 - t1:.1f}s)")
    fac, w = order2_factor(D, N, M, [f for _, f in fb])
    t3 = time.time()
    ok = fac is not None and fac * (N // fac) == N
    print(f"FACTOR: {fac} * {N // fac if fac else None} = N  ok={ok}  total {t3 - t0:.1f}s")
    save(f"classical_{N.bit_length()}", dict(bits=N.bit_length(), N=N, p=p, q=q, B=B, seed=seed, fb_size=d,
         relations=len(rels), trials=trials, t_collect=t1 - t0, det_bits=M.bit_length(), t_det=t2 - t1,
         factor=fac, ok=ok, total_time=t3 - t0, recorded=False))

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
