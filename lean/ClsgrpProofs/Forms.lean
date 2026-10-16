import Mathlib

/-!
# Lemma 1: ambiguous reduced forms of discriminant `-N` factor `N`

Integer arithmetic only. The classical fact that a reduced form whose class has
order dividing two is ambiguous is proved in `ClsgrpProofs.Equiv`, from the
uniqueness of reduced representatives.
-/

namespace Clsgrp

/-- A binary quadratic form `a x^2 + b x y + c y^2`. -/
@[ext]
structure Form where
  a : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq

namespace Form

def disc (f : Form) : ℤ := f.b ^ 2 - 4 * f.a * f.c

/-- `|b| ≤ a ≤ c`, with `b ≥ 0` when `|b| = a` or `a = c`. -/
def IsReduced (f : Form) : Prop :=
  |f.b| ≤ f.a ∧ f.a ≤ f.c ∧ ((|f.b| = f.a ∨ f.a = f.c) → 0 ≤ f.b)

/-- `b = 0`, `b = a`, or `a = c`. -/
def IsAmbiguous (f : Form) : Prop :=
  f.b = 0 ∨ f.b = f.a ∨ f.a = f.c

/-- The identity form `(1, 1, (1 + N) / 4)` for `N ≡ 3 (mod 4)`. -/
def principal (N : ℤ) : Form := ⟨1, 1, (1 + N) / 4⟩

/-- The factor read off an ambiguous form: `a` if `b = a`, otherwise `2a - b`. -/
def factor (f : Form) : ℤ := if f.b = f.a then f.a else 2 * f.a - f.b

variable {f : Form} {N : ℤ}

theorem a_pos (hr : f.IsReduced) (hd : f.disc = -N) (hN : 0 < N) : 0 < f.a := by
  obtain ⟨h1, h2, -⟩ := hr
  unfold disc at hd
  rcases (abs_nonneg f.b).trans h1 |>.lt_or_eq with h | h
  · exact h
  · have hb : f.b = 0 := abs_eq_zero.mp (le_antisymm (h ▸ h1) (abs_nonneg _))
    rw [← h, hb] at hd
    omega

/-- Reduced forms have `3 a^2 ≤ N`, i.e. `a ≤ √(N/3)`. -/
theorem three_a_sq_le (hr : f.IsReduced) (hd : f.disc = -N) (hN : 0 < N) :
    3 * f.a ^ 2 ≤ N := by
  have ha := a_pos hr hd hN
  obtain ⟨h1, h2, -⟩ := hr
  unfold disc at hd
  have hb2 : f.b ^ 2 ≤ f.a ^ 2 := by
    rw [← sq_abs f.b]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith

/-- For odd `N` the middle coefficient is odd, so `b = 0` never occurs. -/
theorem b_odd (hd : f.disc = -N) (hodd : Odd N) : Odd f.b := by
  unfold disc at hd
  rcases Int.even_or_odd f.b with ⟨k, hk⟩ | h
  · have hev : Even N := ⟨2 * (f.a * f.c) - 2 * k ^ 2, by rw [hk] at hd; linarith⟩
    exact absurd hodd (Int.not_odd_iff_even.mpr hev)
  · exact h

/-- The only reduced form of discriminant `-N` with `a = 1` is the principal form. -/
theorem eq_principal_of_a_eq_one (hr : f.IsReduced) (hd : f.disc = -N) (hodd : Odd N)
    (ha : f.a = 1) : f = principal N := by
  have hbo := b_odd hd hodd
  obtain ⟨h1, -, h3⟩ := hr
  rw [ha] at h1
  have hb : f.b = 1 := by
    obtain ⟨k, hk⟩ := hbo
    have : |f.b| = 1 := le_antisymm h1 (by rw [hk]; rcases abs_cases (2 * k + 1) with h | h <;> omega)
    have h0 : 0 ≤ f.b := h3 (Or.inl (this.trans ha.symm))
    rw [abs_of_nonneg h0] at this; exact this
  unfold disc at hd
  ext
  · simp [principal, ha]
  · simp [principal, hb]
  · simp only [principal]; rw [ha, hb] at hd; omega

/-- **Lemma 1.** A reduced ambiguous form of discriminant `-N`, `N` odd, other than the
principal form, yields the divisor `f.factor` of `N` with `1 < f.factor < N`. -/
theorem factor_spec (hr : f.IsReduced) (hd : f.disc = -N) (hN : 0 < N)
    (hodd : Odd N) (hamb : f.IsAmbiguous) (hne : f ≠ principal N) :
    f.factor ∣ N ∧ 1 < f.factor ∧ f.factor < N := by
  have ha := a_pos hr hd hN
  have ha1 : f.a ≠ 1 := fun h => hne (eq_principal_of_a_eq_one hr hd hodd h)
  have ha2 : 2 ≤ f.a := by omega
  have h3 := three_a_sq_le hr hd hN
  have hbo := b_odd hd hodd
  obtain ⟨h1, h2, h0⟩ := hr
  unfold disc at hd
  rcases hamb with hb | hb | hac
  · -- `b = 0` contradicts `b` odd
    rw [hb] at hbo; exact absurd hbo (by decide)
  · -- `b = a`: `N = a (4c - a)`
    rw [factor, if_pos hb]
    refine ⟨⟨4 * f.c - f.a, ?_⟩, by omega, by nlinarith⟩
    rw [hb] at hd; linarith
  · -- `a = c`: `N = (2a - b)(2a + b)` with `0 ≤ b ≤ a`
    have hb0 : 0 ≤ f.b := h0 (Or.inr hac)
    have hba : f.b ≤ f.a := (le_abs_self _).trans h1
    have hfac : N = (2 * f.a - f.b) * (2 * f.a + f.b) := by rw [← hac] at hd; linarith
    by_cases hb : f.b = f.a
    · rw [factor, if_pos hb]
      refine ⟨⟨4 * f.c - f.a, ?_⟩, by omega, by nlinarith⟩
      rw [hb] at hd; linarith
    rw [factor, if_neg hb]
    refine ⟨⟨2 * f.a + f.b, hfac⟩, by omega, ?_⟩
    rw [hfac]; nlinarith

/-- For `N = p q` with `p, q` prime the divisor of Lemma 1 is `p` or `q`. -/
theorem eq_prime_factor {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {d : ℤ}
    (hdvd : d ∣ (p * q : ℕ)) (h1 : 1 < d) (h2 : d < (p * q : ℕ)) :
    d = p ∨ d = q := by
  lift d to ℕ using (by omega)
  norm_cast at hdvd h1 h2 ⊢
  obtain ⟨d₁, d₂, hd₁, hd₂, rfl⟩ := Nat.dvd_mul.mp hdvd
  rcases hp.eq_one_or_self_of_dvd d₁ hd₁ with rfl | rfl <;>
    rcases hq.eq_one_or_self_of_dvd d₂ hd₂ with rfl | rfl <;> simp_all

end Form

end Clsgrp
