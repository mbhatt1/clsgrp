# Lean 4 formalization

Machine-checked proofs of Lemma 1 and Theorem 1 of the paper (Lean `v4.32.1`, Mathlib `v4.32.1`).

```sh
cd lean && lake exe cache get && lake build
```

| Paper | Lean |
|---|---|
| Reduced forms satisfy `a ≤ √(N/3)` | `Form.three_a_sq_le` |
| `b = 0` impossible for odd `N` | `Form.b_odd` |
| Properly equivalent reduced forms are equal | `Form.reduced_unique` |
| A reduced form equivalent to its opposite is ambiguous | `Form.ambiguous_of_equiv_opp` |
| An order-two class has an ambiguous reduced representative | `ClassGroupModel.red_ambiguous` |
| Lemma 1: a non-principal ambiguous reduced form gives a proper factor | `Form.factor_spec`, `Form.eq_prime_factor` |
| Thm 1: squaring `g^m` fewer than `k` times reaches an order-2 class | `exists_orderOf_eq_two` |
| Thm 1: that class factors `N` | `factor_of_classNumber` |
| Thm 1: at least half of classes succeed | `half_succeed`, `one_le_k_of_orderOf_two` |
| Genus theory: the descent lands on the unique involution | `descent_eq` |

**Modelled, not constructed.** Mathlib has no composition of binary quadratic forms, so
`ClassGroupModel` takes the class group as an abstract finite abelian group with a map to
reduced forms of discriminant `-N` satisfying the defining properties of the form class
group: distinct classes have distinct reduced representatives, the identity is the principal
form, and the inverse of a class is the class of the opposite form `(a, -b, c)`
(`SL₂(ℤ)`-equivalence, `Form.PEquiv`). The classical theorems built on these, uniqueness of
reduced representatives and ambiguity of order-two classes, are proved in `Equiv.lean`.
GRH, which the paper uses only for near-uniform sampling, is not modelled. `Check.lean`
builds a concrete model for `Cl(-15)` to show the hypotheses can all hold at once, and
prints the axioms each theorem uses; the output is only `propext`, `Classical.choice`, and `Quot.sound`.
