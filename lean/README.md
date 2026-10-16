# Lean 4 formalization

Machine-checked proofs of Lemma 1 and Theorem 1 of the paper (Lean `v4.32.1`, Mathlib `v4.32.1`).

```sh
cd lean && lake exe cache get && lake build
```

| Paper | Lean |
|---|---|
| Reduced forms satisfy `a ≤ √(N/3)` | `Form.three_a_sq_le` |
| `b = 0` impossible for odd `N` | `Form.b_odd` |
| Lemma 1: a non-principal ambiguous reduced form gives a proper factor | `Form.factor_spec`, `Form.eq_prime_factor` |
| Thm 1: squaring `g^m` fewer than `k` times reaches an order-2 class | `exists_orderOf_eq_two` |
| Thm 1: that class factors `N` | `factor_of_classNumber` |
| Thm 1: at least half of classes succeed | `half_succeed`, `one_le_k_of_orderOf_two` |
| Genus theory: the descent lands on the unique involution | `descent_eq` |

**Assumed, not proved.** `ClassGroupModel` takes three classical facts as hypotheses:
every class has a unique reduced representative, the identity class is represented by the
principal form, and a class of order two has an ambiguous representative [Cohen 1993].
Mathlib has no composition of binary quadratic forms, so none of these can be derived yet.
GRH, which the paper uses only for near-uniform sampling, is not modelled. `Check.lean`
builds a concrete model for `Cl(-15)` to show the hypotheses can all hold at once, and
prints the axioms each theorem uses; the output is only `propext`, `Classical.choice`, and `Quot.sound`.
