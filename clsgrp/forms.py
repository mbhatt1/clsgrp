"""Binary quadratic forms of negative discriminant: arithmetic used throughout the paper.

Pure Python. Conventions: a form is a tuple (a, b, c) with b^2 - 4ac = D < 0, primitive,
positive definite. Reduced means |b| <= a <= c with b >= 0 when |b| == a or a == c.
Composition is Cohen, Algorithm 5.4.7; reduction is Algorithm 5.4.2.
"""
import random
from math import gcd, isqrt
mpz = int
def gcdext(a, b):
    x0, x1, y0, y1 = 1, 0, 0, 1
    while b:
        q, a, b = a//b, b, a % b
        x0, x1 = x1, x0 - q*x1
        y0, y1 = y1, y0 - q*y1
    if a < 0: a, x0, y0 = -a, -x0, -y0
    return a, x0, y0
def is_prime(n):
    if n < 2: return False
    for sp in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % sp == 0: return n == sp
    d, s = n-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(s-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True
def next_prime(n):
    n += 1
    while not is_prime(n): n += 1
    return n
def jacobi(a, n):
    a %= n; r = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5): r = -r
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3: r = -r
        a %= n
    return r if n == 1 else 0

def rand_prime(bits, rng):
    while True:
        x = mpz(rng.getrandbits(bits)) | (mpz(1) << (bits-1)) | 1
        if is_prime(x): return x

# ---------- binary quadratic forms, discriminant D < 0 ----------
def reduce_form(a, b, c, D):
    while True:
        if -a < b <= a and a <= c:
            if a == c and b < 0: b = -b
            return (a, b, c)
        if a > c:
            a, b, c = c, -b, a
            continue
        # normalise b into (-a, a]
        bn = a - ((a - b) % (2*a))
        c = (bn*bn - D) // (4*a)
        b = bn

def compose(f1, f2, D):
    a1, b1, c1 = f1; a2, b2, c2 = f2
    if a1 > a2: a1, b1, c1, a2, b2, c2 = a2, b2, c2, a1, b1, c1
    s = (b1 + b2) // 2; n = b2 - s
    if a2 % a1 == 0:
        y1 = mpz(0); d = a1
    else:
        d, u, v = gcdext(a2, a1); y1 = u
    if s % d == 0:
        y2 = mpz(-1); x2 = mpz(0); d1 = d
    else:
        d1, u, v = gcdext(s, d); x2 = u; y2 = -v
    v1 = a1 // d1; v2 = a2 // d1
    r = (y1*y2*n - x2*c2) % v1
    b3 = b2 + 2*v2*r
    a3 = v1*v2
    c3 = (c2*d1 + r*(b2 + v2*r)) // v1
    return reduce_form(a3, b3, c3, D)

def power(f, e, D):
    ident = (mpz(1), mpz(1), (1 - D)//4)
    result = ident; base = f
    e = int(e)
    while e:
        if e & 1: result = compose(result, base, D)
        base = compose(base, base, D); e >>= 1
    return result

def inverse(f): return (f[0], -f[1], f[2]) if f[1] != f[0] and f[0] != f[2] else f

def sqrt_mod_prime(a, p):
    a %= p
    if p == 2: return a
    # Tonelli-Shanks
    if pow(a, (p-1)//2, p) != 1: return None
    q, s = p-1, 0
    while q % 2 == 0: q //= 2; s += 1
    z = 2
    while pow(z, (p-1)//2, p) != p-1: z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q+1)//2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1: t2 = t2*t2 % p; i += 1
        b = pow(c, 1 << (m-i-1), p)
        m, c, t, r = i, b*b % p, t*b*b % p, r*b % p
    return r

def prime_form(l, D):
    if l == 2:
        if D % 8 == 1: return (mpz(2), mpz(1), (1 - D)//8)
        return None
    if jacobi(D, l) != 1: return None
    b = mpz(sqrt_mod_prime(int(D % l), l))
    if (b - D) % 2: b = l - b
    return (l, b, (b*b - D)//(4*l))

# ---------- Bareiss: determinant of a full-rank d x d subset of the rows ----------
def lattice_det(rows, d):
    M = [list(r) for r in rows]
    nrows = len(M); prev = mpz(1)
    for k in range(d):
        piv = next((i for i in range(k, nrows) if M[i][k] != 0), None)
        if piv is None: return None
        if piv != k: M[k], M[piv] = M[piv], M[k]
        pk = M[k][k]
        for i in range(k+1, nrows):
            Mi = M[i]; mik = Mi[k]; Mk = M[k]
            if mik == 0:
                for j in range(k+1, d): Mi[j] = (Mi[j]*pk) // prev
            else:
                for j in range(k+1, d): Mi[j] = (Mi[j]*pk - mik*Mk[j]) // prev
        prev = pk
    return abs(M[d-1][d-1])

def ambiguous_factor(f, N):
    a, b, c = f
    if b == 0: cands = [a, c]
    elif b == a: cands = [a, 4*c - a]
    elif a == c: cands = [2*a - b, 2*a + b]
    else: return None
    for x in cands:
        g = gcd(x, N)
        if 1 < g < N: return g
    return None



def identity(D):
    return (1, 1, (1 - D) // 4)

def reduced_forms(D):
    """Brute-force enumeration of all reduced primitive forms of discriminant D (toy sizes only)."""
    out = []
    amax = isqrt(abs(D) // 3)
    for a in range(1, amax + 1):
        for b in range(-a, a + 1):
            if (b - D) % 2: continue
            num = b * b - D
            if num % (4 * a): continue
            c = num // (4 * a)
            if c < a: continue
            if (abs(b) == a or a == c) and b < 0: continue
            if gcd(gcd(a, abs(b)), c) != 1: continue
            out.append((a, b, c))
    return out

def factor_from_ambiguous(D, N, forms):
    """Lemma 1: a non-identity ambiguous reduced form yields a proper factor of N."""
    found = set()
    for (a, b, c) in forms:
        if b == 0: cands = [a, c]
        elif b == a: cands = [a, 4 * c - a]
        elif a == c: cands = [2 * a - b, 2 * a + b]
        else: continue
        for x in cands:
            g = gcd(x, N)
            if 1 < g < N: found.add(g)
    return found

def random_semiprime(bits, rng, mod4=3):
    """N = p*q with p, q of bits//2 bits and N = mod4 (mod 4)."""
    while True:
        p = rand_prime(bits // 2, rng); q = rand_prime(bits // 2, rng); N = p * q
        if N % 4 == mod4 and p != q:
            return p, q, N

def prime_forms_upto(D, B):
    """(l, form) for split primes l <= B."""
    out = []; l = 2
    while l <= B:
        pf = prime_form(l, D)
        if pf: out.append((l, pf))
        l = next_prime(l)
    return out

def first_prime_forms(D, d, start=3):
    out = []; l = start
    while len(out) < d:
        pf = prime_form(l, D)
        if pf: out.append((l, pf))
        l = next_prime(l)
    return out

def random_reduced_form(D, rng, fb, k=6, ebits=40):
    f = identity(D)
    for _ in range(k):
        f = compose(f, power(fb[rng.randrange(len(fb))], rng.getrandbits(ebits), D), D)
    return f

def order2_factor(D, N, M, gens, max_tries=20):
    """Theorem 1: given a multiple M of the order of every element of <gens>, square down to the
    order-2 class and read a factor. Returns (factor, witness_form) or (None, None)."""
    ident = identity(D); k = 0; m = M
    while m % 2 == 0: m //= 2; k += 1
    for g in gens[:max_tries]:
        x = power(g, m, D)
        if x == ident: continue
        while True:
            y = compose(x, x, D)
            if y == ident: break
            x = y
        fac = factor_from_ambiguous(D, N, [x])
        if fac: return sorted(fac)[0], x
    return None, None
