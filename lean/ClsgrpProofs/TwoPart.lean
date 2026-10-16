import Mathlib

/-!
# The group-theoretic core of Theorem 1

For a finite abelian group of order `h = 2^k m` with `m` odd:

* if `g^m ≠ 1`, squaring `g^m` fewer than `k` times reaches an element of order two;
* if `k ≥ 1`, the classes with `g^m = 1` form a proper subgroup, so at least half of
  all classes satisfy `g^m ≠ 1`;
* if the group has a unique element of order two (genus theory for `D = -pq`), every
  successful descent lands on that element.
-/

namespace Clsgrp

variable {G : Type*} [CommGroup G] [Fintype G] {k m : ℕ}

/-- Squaring `g^m` at most `k - 1` times reaches an element of order two. -/
theorem exists_orderOf_eq_two (hcard : Fintype.card G = 2 ^ k * m) {g : G}
    (hg : g ^ m ≠ 1) : ∃ j < k, orderOf ((g ^ m) ^ (2 ^ j)) = 2 := by
  set x := g ^ m
  have hx : x ^ (2 ^ k) = 1 := by
    rw [← pow_mul, mul_comm, ← hcard, pow_card_eq_one]
  obtain ⟨i, hi, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx)
  have hi0 : i ≠ 0 := by
    rintro rfl; exact hg (orderOf_eq_one_iff.mp (by simpa using hord))
  refine ⟨i - 1, by omega, ?_⟩
  have hdvd : 2 ^ (i - 1) ∣ orderOf x := hord ▸ pow_dvd_pow 2 (Nat.sub_le i 1)
  rw [orderOf_pow_of_dvd (by positivity) hdvd, hord]
  obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  simp [pow_succ]

/-- With a unique element `t` of order two, the descent from any `g` with `g^m ≠ 1`
lands on `t`. -/
theorem descent_eq (hcard : Fintype.card G = 2 ^ k * m) {t : G}
    (huniq : ∀ y : G, orderOf y = 2 → y = t) {g : G} (hg : g ^ m ≠ 1) :
    ∃ j < k, (g ^ m) ^ (2 ^ j) = t := by
  obtain ⟨j, hj, h⟩ := exists_orderOf_eq_two hcard hg
  exact ⟨j, hj, huniq _ h⟩

/-- The classes with `g^m = 1`. -/
def oddPart (G : Type*) [CommGroup G] (m : ℕ) : Subgroup G := (powMonoidHom m).ker

omit [Fintype G] in
theorem mem_oddPart {g : G} : g ∈ oddPart G m ↔ g ^ m = 1 := Iff.rfl

/-- If `k ≥ 1` then at most half of the classes satisfy `g^m = 1`. -/
theorem two_mul_card_oddPart_le (hcard : Fintype.card G = 2 ^ k * m) (hm : Odd m)
    (hk : 1 ≤ k) : 2 * Nat.card (oddPart G m) ≤ Nat.card G := by
  have h2 : 2 ∣ Fintype.card G := by
    rw [hcard]; exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) m
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card 2 h2
  have hne : oddPart G m ≠ ⊤ := by
    intro htop
    have htm : t ^ m = 1 := (mem_oddPart).mp (htop ▸ Subgroup.mem_top t)
    have : 2 ∣ m := ht ▸ orderOf_dvd_of_pow_eq_one htm
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr this)
  have hidx : 2 ≤ (oddPart G m).index :=
    Subgroup.one_lt_index_of_ne_top hne
  rw [← (oddPart G m).card_mul_index]
  rw [mul_comm]
  exact Nat.mul_le_mul_left _ hidx

end Clsgrp
