# clsgrp — Regev's factoring algorithm over class groups

Code, data, and LaTeX source for the paper *Regev's Factoring Algorithm over Class Groups:
Half the Group Operations, Twice the Cost*.

The paper makes a Regev-style quantum factoring algorithm over the class group of
Q(√−N) explicit, proves the reduction from factoring to the class number, verifies the
classical post-processing up to 189 bits, simulates the quantum sampler end to end, and
costs the route at 4096 bits. The verdict is negative: half the sequential group
operations, 2.4× to 4.4× the gate cost, because squaring a form contains a modular inverse
modulo quantum data.

## Reproduce the paper with one command

```
pip install -r requirements.txt     # sympy, matplotlib
./reproduce.sh                      # ~10–15 min on one core
```

This reruns every experiment except the two slow classical runs, regenerates every table
and figure from `results/*.json`, and builds `paper/paper.pdf`. The 160-bit (15 min) and
189-bit (7 h) classical runs use the recorded results shipped in `results/` and are marked
with an asterisk in Table I; `./reproduce.sh --full` reruns them too. `./reproduce.sh --paper`
rebuilds tables, figures, and the PDF from whatever is in `results/` without recomputing.

Requirements: Python 3.9+, [PARI/GP](https://pari.math.u-bordeaux.fr/) (`gp` on the PATH,
used as the oracle for the class-group structure in the simulator and in the Theorem 1 run),
and a TeX distribution with `latexmk`. Moduli are fixed by seeds, so a rerun reproduces the
same N, the same relations, and the same numbers up to timing.

## Layout

| path | contents |
|---|---|
| `clsgrp/forms.py` | binary quadratic form arithmetic: composition, reduction, prime forms, ambiguous-form extraction (Lemma 1), the order-2 extraction (Theorem 1) |
| `clsgrp/pari.py` | wrappers around `gp` for the class number and the discrete logs of prime forms |
| `scripts/classical_factor.py` | Schnorr–Lenstra / Hafner–McCurley classical factoring → Table I, Fig. 2 |
| `scripts/oracle_factor.py` | Theorem 1 with PARI as the class-number oracle |
| `scripts/sim_regev.py` | simulated quantum sampler + LLL post-processing + extraction → Table II |
| `scripts/nudupl_cost.py` | derived NUDUPL squaring, validated against composition, with an operation ledger → §VI.A |
| `scripts/rev_gcd.py` | branch-free reversible modular inverse (divsteps), Toffoli-counted and verified → §VI.C |
| `scripts/rev_partial.py` | reversible partial Euclid with integer cofactors → §VI.C |
| `scripts/compare.py` | assembles the per-step comparison → Table III, Fig. 1 |
| `scripts/ambiguous_1mod4.py` | classes of order two for D = −4N when N ≡ 1 (mod 4) → §3.3 |
| `scripts/integral_demo.py`, `scripts/geodesic_demo.py` | the class number as an integral; the factor at the midpoint of the CF period of √N → §VII |
| `scripts/make_tables.py`, `scripts/make_figs.py` | `results/*.json` → `paper/tables/*.tex`, `paper/*.png` |
| `results/` | one JSON per experiment; the two `recorded: true` entries are the slow classical runs |
| `paper/` | `paper.tex`, `refs.bib`, IEEEtran class and style (CTAN, LPPL), generated tables and figures |

## What is measured and what is modelled

Measured: everything in Tables I and II; the NUDUPL operation counts; the forward and
uncomputed cost of the reversible inverse and partial Euclid. Modelled (stated in the paper):
the integer Regev step, the small-form composition, and the 1.5× arithmetic uncompute
overhead. The cost convention is one set of adder costs applied to both routes
(`scripts/rev_gcd.py` header). Numbers quoted in the paper's prose are those of the
recorded run; a rerun regenerates the tables and figures and should match them up to timing.

## Cite

See `paper/refs.bib` for the references. The reduction and the classical method are due
to Schnorr–Lenstra (1984) and Hafner–McCurley (1989); the quantum class-group algorithms to
Hallgren (2005) and Biasse–Song (2016); the framework to Regev (2023). This repository's
contribution is the explicit combination, the simulator, and the cost measurement.

## License

MIT for the code. `paper/IEEEtran.cls` and `paper/IEEEtran.bst` are from CTAN under the LPPL.
