import ClsgrpProofs.Forms
import ClsgrpProofs.Equiv
import ClsgrpProofs.TwoPart

/-!
# Theorem 1: factoring from the class number

The class group is modelled abstractly as a finite abelian group `G` together with
its map to reduced representatives. Mathlib has no composition of binary quadratic
forms, so `ClassGroupModel` records only the defining properties of the form class group:

* distinct classes have distinct reduced representatives of discriminant `-N`;
* the identity class is represented by the principal form;
* the inverse of a class is the class of the opposite form `(a, -b, c)`.

The two classical theorems the reduction rests on are proved, not assumed:
uniqueness of reduced representatives (`Form.reduced_unique`) and ambiguity of the
reduced representative of an order-two class (`ClassGroupModel.red_ambiguous`, from
`Form.ambiguous_of_equiv_opp`).

Genus theory (a unique element of order two) is not needed for the factoring claim:
any element of order two works. GRH, used in the paper only to sample nearly
uniformly, is not modelled; the counting bound below is stated for uniform `g`.
-/

namespace Clsgrp

open Form

/-- An abstract class group of discriminant `-N` with reduced representatives. -/
structure ClassGroupModel (N : ℤ) (G : Type*) [CommGroup G] where
  red : G → Form
  red_injective : Function.Injective red
  red_reduced : ∀ g, (red g).IsReduced
  red_disc : ∀ g, (red g).disc = -N
  red_one : red 1 = principal N
  red_inv : ∀ g, (red g⁻¹).PEquiv (red g).opp

variable {G : Type*} [CommGroup G] [Fintype G] {N : ℤ}

omit [Fintype G] in
/-- The reduced representative of a class of order two is ambiguous. -/
theorem ClassGroupModel.red_ambiguous (C : ClassGroupModel N G) {g : G}
    (hg : orderOf g = 2) : (C.red g).IsAmbiguous := by
  have hinv : g⁻¹ = g := by
    rw [inv_eq_iff_mul_eq_one, ← sq, ← hg, pow_orderOf_eq_one]
  have := C.red_inv g
  rw [hinv] at this
  exact ambiguous_of_equiv_opp (C.red_reduced g) this

/-- **Theorem 1.** Let `N = p q` be odd and `h = |Cl(-N)| = 2^k m` with `m` odd. For any
class `g` with `g^m ≠ 1`, some `j < k` makes the reduced form of `(g^m)^(2^j)` ambiguous
and non-principal, and its `factor` is `p` or `q`. -/
theorem factor_of_classNumber (C : ClassGroupModel N G) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hN : N = (p * q : ℕ)) (hodd : Odd N) {k m : ℕ}
    (hcard : Fintype.card G = 2 ^ k * m) {g : G} (hg : g ^ m ≠ 1) :
    ∃ j < k, (C.red ((g ^ m) ^ (2 ^ j))).factor = p ∨
      (C.red ((g ^ m) ^ (2 ^ j))).factor = q := by
  obtain ⟨j, hj, hord⟩ := exists_orderOf_eq_two hcard hg
  set y := (g ^ m) ^ (2 ^ j)
  have hy1 : y ≠ 1 := by
    intro h; rw [h, orderOf_one] at hord; exact absurd hord (by decide)
  have hne : C.red y ≠ principal N := by
    rw [← C.red_one]; exact fun h => hy1 (C.red_injective h)
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Nat.mul_pos hp.pos hq.pos
  obtain ⟨hdvd, h1, h2⟩ := factor_spec (C.red_reduced y) (C.red_disc y) hNpos hodd
    (C.red_ambiguous hord) hne
  exact ⟨j, hj, eq_prime_factor hp hq (hN ▸ hdvd) h1 (hN ▸ h2)⟩

/-- **Theorem 1, success probability.** If `k ≥ 1`, at least half of all classes `g`
satisfy `g^m ≠ 1`, so a uniformly random class succeeds with probability `≥ 1/2`. -/
theorem half_succeed (hcard : Fintype.card G = 2 ^ k * m) (hm : Odd m) (hk : 1 ≤ k) :
    Nat.card G ≤ 2 * Nat.card {g : G // g ^ m ≠ 1} := by
  have hhalf := two_mul_card_oddPart_le hcard hm hk
  classical
  have hsplit : Nat.card (oddPart G m) + Nat.card {g : G // g ^ m ≠ 1} = Nat.card G := by
    have e : Nat.card (oddPart G m) = Fintype.card {g : G // g ^ m = 1} :=
      Nat.card_eq_fintype_card (α := {g : G // g ^ m = 1})
    rw [e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    have := Fintype.card_subtype_le (fun g : G => g ^ m = 1)
    omega
  omega

/-- `k ≥ 1` holds for `D = -pq`: an element of order two exists. -/
theorem one_le_k_of_orderOf_two (hcard : Fintype.card G = 2 ^ k * m) (hm : Odd m)
    {t : G} (ht : orderOf t = 2) : 1 ≤ k := by
  by_contra hk
  have : k = 0 := by omega
  subst this
  have h2 : 2 ∣ 2 ^ 0 * m := hcard ▸ ht ▸ orderOf_dvd_card
  simp at h2
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)

end Clsgrp
