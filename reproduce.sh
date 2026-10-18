#!/usr/bin/env bash
# Reproduce every table, figure, and the PDF of the paper from scratch.
#   ./reproduce.sh          fast: ~10-15 min; the 160- and 189-bit classical runs (15 min and 7 h)
#                            use the recorded results shipped in results/ (marked * in Table 1)
#   ./reproduce.sh --full   also rerun the 160- and 189-bit classical runs
#   ./reproduce.sh --paper  only regenerate tables, figures, and the PDF from results/
# Requirements: python3 with sympy + matplotlib, PARI/GP (`gp`), a TeX distribution with latexmk.
set -euo pipefail
cd "$(dirname "$0")"
MODE="${1:-fast}"
need() { command -v "$1" >/dev/null 2>&1 || { echo "missing: $1" >&2; exit 1; }; }
need python3; need gp; need latexmk
python3 -c "import sympy, matplotlib" || { echo "pip install -r requirements.txt" >&2; exit 1; }
run() { echo; echo "== $*"; python3 "$@"; }

if [ "$MODE" != "--paper" ]; then
  # Table 1 / Fig. 2: classical class-group factoring (seeds fix the moduli used in the paper)
  run scripts/classical_factor.py 60 1500 7
  run scripts/classical_factor.py 100 4000 11
  run scripts/classical_factor.py 130 10000 13
  if [ "$MODE" = "--full" ]; then
    run scripts/classical_factor.py 160 15000 17
    run scripts/classical_factor.py 190 25000 19
  fi
  # Theorem 1 with PARI as the class-number oracle
  run scripts/oracle_factor.py 100 42
  # Table 2: simulated quantum sampler + Regev post-processing (default noise, then a noise sweep)
  run scripts/sim_regev.py 60 8 3
  run scripts/sim_regev.py 100 10 5
  run scripts/sim_regev.py 100 10 5 12
  run scripts/sim_regev.py 100 10 5 9
  # Section 6: NUDUPL measurement at 4096 bits, reversible inverse and partial Euclid at n' = 2048
  run scripts/nudupl_cost.py 4096 12 7
  run scripts/rev_gcd.py 2048 3 5
  run scripts/rev_partial.py 2048 4 3
  run scripts/compare.py 4096
  # Section 3.3: classes of order two for N = 1 (mod 4)
  run scripts/ambiguous_1mod4.py 2100
  # side demonstrations (not in the paper)
  run scripts/integral_demo.py 22 9
  run scripts/geodesic_demo.py 3
fi

run scripts/make_tables.py
run scripts/make_figs.py
# The LNCS paper lives in paper/pqcrypto/ in the repository and in paper/ in the supplementary archive.
if [ -d paper/pqcrypto ]; then
  cp paper/tables/*.tex paper/pqcrypto/tables/ && cp paper/fig_hero.png paper/fig1_scaling.png paper/pqcrypto/
  PDIR=paper/pqcrypto
else
  PDIR=paper
fi
echo; echo "== building $PDIR/paper.pdf"
( cd "$PDIR" && latexmk -pdf -interaction=nonstopmode paper.tex > build.log 2>&1 && echo "$PDIR/paper.pdf: $(pdfinfo paper.pdf 2>/dev/null | grep Pages || echo built)" ) || { echo "LaTeX failed; see $PDIR/build.log" >&2; exit 1; }
