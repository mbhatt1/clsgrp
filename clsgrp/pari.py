"""Thin wrappers around PARI/GP (the `gp` binary) used as an oracle for the class group structure."""
import subprocess, re, shutil

GP = shutil.which("gp")

def _run(script):
    if GP is None:
        raise RuntimeError("PARI/GP (`gp`) not found on PATH; needed for the simulator and the oracle run")
    pre = "default(parisizemax, 4000000000);\ndefault(threadsizemax, 2000000000);\n"
    r = subprocess.run([GP, "-q"], input=pre + script + "\nquit\n", capture_output=True, text=True)
    return r.stdout

def class_number(D):
    out = _run(f"print(quadclassunit({D}).no);")
    return int(out.strip().splitlines()[-1])

def group_data(N, d):
    """Cyclic structure of Cl(-N) (N = 3 mod 4) and, for the d smallest split primes l,
    PARI's prime ideal above l as (l, x, y) with generator x + y*w, w = (1+sqrt(-N))/2,
    and its discrete logarithm vector w.r.t. the cyclic generators."""
    script = (f"N={N}; bnf=bnfinit(y^2-y+(1+N)/4,1);\n"
              f'print("CYC ", bnf.clgp.cyc);\n'
              f"cnt=0; l=2; while(cnt<{d}, if(kronecker(-N,l)==1, P=idealprimedec(bnf,l)[1]; v=bnfisprincipal(bnf,P,0); "
              f'print("PR ", l, " ", P.gen[2], " ", v); cnt++); l=nextprime(l+1));')
    out = _run(script)
    cyc = [int(x) for x in re.search(r'CYC \[(.*?)\]', out).group(1).split(',')]
    primes = []
    for m in re.finditer(r'PR (\d+) \[(-?\d+), (-?\d+)\]~ \[(.*?)\]~', out):
        primes.append((int(m.group(1)), int(m.group(2)), int(m.group(3)), [int(t) for t in m.group(4).split(',')]))
    if len(primes) != d:
        raise RuntimeError("PARI output not parsed:\n" + out[-800:])
    return cyc, primes
