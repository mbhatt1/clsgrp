"""End-to-end simulation of Regev's algorithm over Cl(-N): Table II.
The quantum sampler is simulated by drawing random characters of Cl(-N) (PARI supplies the group
structure, as Ekera's regevnum needs the factorization for the integer case).
usage: python3 scripts/sim_regev.py <bits> <d> <seed> [noise exponent eta]"""
import sys, random, time
from math import log2, ceil
from _common import *
from clsgrp.forms import *
from clsgrp import pari
from sympy.polys.matrices import DomainMatrix
from sympy import ZZ

def main(bits, d, seed, eta=None):
    rng = random.Random(seed); p, q, N = random_semiprime(bits, rng); D = -N; ident = identity(D)
    t0 = time.time(); cyc, pdata = pari.group_data(N, d); k = len(cyc); h = 1
    for c in cyc: h *= c
    print(f"N = {N} ({N.bit_length()} bits); Cl = {cyc}, h = {h} ({time.time() - t0:.1f}s)")
    forms = []; A = [[0] * d for _ in range(k)]
    for i, (l, x, y, dl) in enumerate(pdata):
        f = prime_form(l, D); assert f is not None and gcd(y, l) == 1
        r = (x * pow(y, -1, l)) % l; bP = (2 * r + 1) % (2 * l)
        s = 1 if (f[1] - bP) % (2 * l) == 0 else -1
        forms.append(f)
        for j in range(k): A[j][i] = (s * dl[j]) % cyc[j]
    def prod_forms(z):
        r = ident
        for i, e in enumerate(z):
            if e: r = compose(r, power(forms[i] if e > 0 else inverse(forms[i]), abs(e), D), D)
        return r
    if k == 1:
        z = [A[0][1], -A[0][0]] + [0] * (d - 2)
        if prod_forms(z) != ident:
            A = [[(-a) % c for a in row] for row, c in zip(A, cyc)]
            assert prod_forms([A[0][1], -A[0][0]] + [0] * (d - 2)) == ident
    m = d + 4; B = ceil(h.bit_length() / d) + 3; Dp = 2 * B + 2 * ceil(log2(d * m)) + 16
    eta = eta if eta is not None else Dp // 2
    print(f"d={d}, m={m} runs, B={B} exponent bits, precision {Dp} bits, noise 2^-{eta}")
    W = []
    for _ in range(m):
        t = [rng.randrange(c) for c in cyc]; w = []
        for i in range(d):
            v = sum((t[j] * A[j][i] * (1 << Dp)) // cyc[j] for j in range(k))
            w.append((v + rng.randrange(-(1 << (Dp - eta)), (1 << (Dp - eta)) + 1)) % (1 << Dp))
        W.append(w)
    S = max(1, (1 << (Dp - eta)) * isqrt(d)); rows = []
    for i in range(d): rows.append([S if j == i else 0 for j in range(d)] + [W[j][i] for j in range(m)])
    for j in range(m): rows.append([0] * d + [(1 << Dp) if jj == j else 0 for jj in range(m)])
    red = DomainMatrix([[ZZ(x) for x in r] for r in rows], (d + m, d + m), ZZ).lll().to_Matrix().tolist()
    cands = []
    for r in red:
        if any(int(x) % S for x in r[:d]): continue
        z = [int(x) // S for x in r[:d]]
        if any(z) and max(abs(e) for e in z) <= (1 << (B + 4)): cands.append(z)
    good = [z for z in cands if prod_forms(z) == ident]
    print(f"short vectors {len(cands)}, verified relations {len(good)}")
    out = dict(bits=N.bit_length(), N=N, p=p, q=q, cyc=cyc, h=h, d=d, m=m, B=B, Dp=Dp, eta=eta,
               B_integer=ceil(N.bit_length() / d) + 3, n_short=len(cands), n_verified=len(good), ok=False)
    if len(good) >= d:
        M = lattice_det(good, d)
        if M is not None:
            out.update(det=M, index=(h // M if h % M == 0 else None))
            fac, w = order2_factor(D, N, M, forms)
            out.update(factor=fac, ok=fac is not None and fac * (N // fac) == N)
            print(f"det = {M} (= h: {M == h}); factor {fac}")
    out["time"] = time.time() - t0
    save(f"sim_{N.bit_length()}_eta{eta}", out)

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else None)
