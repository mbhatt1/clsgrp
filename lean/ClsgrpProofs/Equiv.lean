import ClsgrpProofs.Forms

/-!
# Uniqueness of reduced forms and ambiguity of order-two classes

`SL₂(ℤ)` acts on forms by substitution, `(f · M)(x, y) = f(p x + q y, r x + s y)`.
We prove, by integer arithmetic only:

* every nonzero vector takes value `≥ a` on a reduced form, `≥ c` if `y ≠ 0`, and
  `≥ a - |b| + c` if `x y ≠ 0`;
* two properly equivalent reduced forms are equal (`reduced_unique`);
* a reduced form properly equivalent to its opposite `(a, -b, c)` is ambiguous
  (`ambiguous_of_equiv_opp`).

Since the inverse of the class of `(a, b, c)` is the class of `(a, -b, c)`, the second
fact is the statement that a reduced form whose class has order dividing two is ambiguous.
-/

namespace Clsgrp

namespace Form

/-- The value `f(x, y) = a x^2 + b x y + c y^2`. -/
def eval (f : Form) (x y : ℤ) : ℤ := f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2

/-- Substitution `(x, y) ↦ (p x + q y, r x + s y)`. -/
def act (f : Form) (p q r s : ℤ) : Form :=
  ⟨f.eval p r, 2 * f.a * p * q + f.b * (p * s + q * r) + 2 * f.c * r * s, f.eval q s⟩

/-- The opposite form `(a, -b, c)`, whose class is the inverse of the class of `f`. -/
def opp (f : Form) : Form := ⟨f.a, -f.b, f.c⟩

/-- Proper (`SL₂(ℤ)`) equivalence. -/
def PEquiv (f g : Form) : Prop := ∃ p q r s : ℤ, p * s - q * r = 1 ∧ g = f.act p q r s

theorem PEquiv.refl (f : Form) : PEquiv f f :=
  ⟨1, 0, 0, 1, by ring, by ext <;> simp [act, eval]⟩

theorem PEquiv.symm {f g : Form} (h : PEquiv f g) : PEquiv g f := by
  obtain ⟨p, q, r, s, hdet, rfl⟩ := h
  refine ⟨s, -q, -r, p, by linear_combination hdet, ?_⟩
  ext <;> simp only [act, eval]
  · linear_combination (-f.a * (p * s - q * r + 1)) * hdet
  · linear_combination (-f.b * (p * s - q * r + 1)) * hdet
  · linear_combination (-f.c * (p * s - q * r + 1)) * hdet

variable {f g : Form} {N : ℤ}

/-- Lower bounds for a reduced form `f` on a vector `(x, y)`. -/
theorem eval_ge_c (hr : f.IsReduced) {x y : ℤ} (hy : y ≠ 0) : f.c ≤ f.eval x y := by
  obtain ⟨h1, h2, -⟩ := hr
  have hb : -|f.b| ≤ f.b := neg_abs_le f.b
  have hb' : f.b ≤ |f.b| := le_abs_self f.b
  have hy1 : 1 ≤ y ^ 2 := by nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1), sq_pos_of_ne_zero hy]
  unfold eval
  have ha : 0 ≤ f.a := (abs_nonneg _).trans h1
  rcases le_total (x ^ 2) (y ^ 2) with hxy | hxy
  · -- `|x y| ≤ y^2`
    have : |x * y| ≤ y ^ 2 := by
      rw [abs_mul, ← sq_abs y]
      have : |x| ≤ |y| := sq_le_sq.mp hxy |>.trans_eq' (by simp) |>.trans_eq (by simp)
      nlinarith [abs_nonneg x, abs_nonneg y]
    have hbxy : -(|f.b| * y ^ 2) ≤ f.b * x * y := by
      have := abs_le.mp (show |f.b * (x * y)| ≤ |f.b| * y ^ 2 by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left this (abs_nonneg _))
      linarith [mul_assoc f.b x y]
    by_cases hx : x = 0
    · subst hx; nlinarith
    · have hx1 : 1 ≤ x ^ 2 := by nlinarith [sq_pos_of_ne_zero hx]
      nlinarith
  · -- `|x y| ≤ x^2`
    have : |x * y| ≤ x ^ 2 := by
      rw [abs_mul, ← sq_abs x]
      have : |y| ≤ |x| := sq_le_sq.mp hxy |>.trans_eq' (by simp) |>.trans_eq (by simp)
      nlinarith [abs_nonneg x, abs_nonneg y]
    have hbxy : -(|f.b| * x ^ 2) ≤ f.b * x * y := by
      have := abs_le.mp (show |f.b * (x * y)| ≤ |f.b| * x ^ 2 by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left this (abs_nonneg _))
      linarith [mul_assoc f.b x y]
    nlinarith [sq_nonneg x]

theorem eval_ge_a (hr : f.IsReduced) {x y : ℤ} (hxy : (x, y) ≠ (0, 0)) :
    f.a ≤ f.eval x y := by
  by_cases hy : y = 0
  · subst hy
    have hx : x ≠ 0 := by rintro rfl; exact hxy rfl
    have ha : 0 ≤ f.a := (abs_nonneg _).trans hr.1
    have : 1 ≤ x ^ 2 := by nlinarith [sq_pos_of_ne_zero hx]
    unfold eval; nlinarith
  · exact hr.2.1.trans (eval_ge_c hr hy)

/-- Main step: if `g = f · M` with `f`, `g` reduced, then `g.a = f.a` and `f.c ≤ g.c`. -/
theorem le_of_act (hf : f.IsReduced) (hg : g.IsReduced) {p q r s : ℤ}
    (hdet : p * s - q * r = 1) (hgf : g = f.act p q r s) (haa : g.a = f.a) :
    f.c ≤ g.c := by
  have hga : g.a = f.eval p r := by rw [hgf]; rfl
  have hgc : g.c = f.eval q s := by rw [hgf]; rfl
  by_cases hs : s = 0
  · subst hs
    have hr : r ≠ 0 := by rintro rfl; simp at hdet
    have hq : (q, (0 : ℤ)) ≠ (0, 0) := by rintro ⟨⟩; simp at hdet
    have := eval_ge_c hf (x := p) hr
    have := eval_ge_a hf hq
    have := hg.2.1
    linarith
  · rw [hgc]; exact eval_ge_c hf hs

theorem a_eq_of_act (hf : f.IsReduced) (hg : g.IsReduced) {p q r s : ℤ}
    (hdet : p * s - q * r = 1) (hgf : g = f.act p q r s) : g.a = f.a := by
  obtain ⟨p', q', r', s', hdet', hfg⟩ := PEquiv.symm ⟨p, q, r, s, hdet, hgf⟩
  have h1 : f.a ≤ g.a := by
    have hga : g.a = f.eval p r := by rw [hgf]; rfl
    rw [hga]; apply eval_ge_a hf
    rintro ⟨⟩; simp at hdet
  have h2 : g.a ≤ f.a := by
    have hfa : f.a = g.eval p' r' := by rw [hfg]; rfl
    rw [hfa]; apply eval_ge_a hg
    rintro ⟨⟩; simp at hdet'
  exact le_antisymm h2 h1

/-- **Uniqueness of reduced representatives.** Properly equivalent reduced forms of the
same negative discriminant are equal. -/
theorem reduced_unique (hf : f.IsReduced) (hg : g.IsReduced) (hd : g.disc = f.disc)
    (he : PEquiv f g) : f = g := by
  obtain ⟨p, q, r, s, hdet, hgf⟩ := he
  obtain ⟨p', q', r', s', hdet', hfg⟩ := PEquiv.symm ⟨p, q, r, s, hdet, hgf⟩
  have haa := a_eq_of_act hf hg hdet hgf
  have hcc : g.c = f.c := le_antisymm
    (le_of_act hg hf hdet' hfg haa.symm) (le_of_act hf hg hdet hgf haa)
  have hbb : f.b ^ 2 = g.b ^ 2 := by unfold disc at hd; rw [haa, hcc] at hd; linarith
  have hb : g.b = f.b ∨ g.b = -f.b := sq_eq_sq_iff_eq_or_eq_neg.mp hbb.symm
  rcases hb with hb | hb
  · ext <;> simp [haa, hb, hcc]
  -- `g.b = -f.b`: the sign conventions force `0 < |b| < a < c`, and then `M = ±1`.
  by_cases hb0 : f.b = 0
  · ext <;> simp [haa, hb, hcc, hb0]
  obtain ⟨hf1, hf2, hf3⟩ := hf
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hab : |f.b| < f.a := by
    rcases hf1.lt_or_eq with h | h
    · exact h
    · have := hf3 (Or.inl h)
      have := hg3 (Or.inl (by rw [hb, abs_neg, haa]; exact h))
      omega
  have hac : f.a < f.c := by
    rcases hf2.lt_or_eq with h | h
    · exact h
    · have := hf3 (Or.inr h)
      have := hg3 (Or.inr (by rw [haa, hcc]; exact h))
      omega
  have hga : g.a = f.eval p r := by rw [hgf]; rfl
  have hgc : g.c = f.eval q s := by rw [hgf]; rfl
  have hgb : g.b = 2 * f.a * p * q + f.b * (p * s + q * r) + 2 * f.c * r * s := by
    rw [hgf]; rfl
  have hfr : f.IsReduced := ⟨hf1, hf2, hf3⟩
  have hr0 : r = 0 := by
    by_contra hr
    have := eval_ge_c hfr (x := p) hr
    linarith
  subst hr0
  have hps : p * s = 1 := by linarith
  have hs1 : s = 1 ∨ s = -1 := Int.eq_one_or_neg_one_of_mul_eq_one' hps |>.elim
    (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  have hs2 : s ^ 2 = 1 := by rcases hs1 with rfl | rfl <;> norm_num
  have hq0 : q = 0 := by
    have hc : f.a * q ^ 2 + f.b * q * s = 0 := by
      have h := hgc; rw [hcc] at h; unfold eval at h; rw [hs2] at h; linarith
    by_contra hq
    have hq1 : 1 ≤ |q| := Int.one_le_abs hq
    have : f.a * |q| = |f.b| := by
      have : f.a * q = -(f.b * s) := by
        have : q * (f.a * q + f.b * s) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hq
        · linarith
      have := congrArg abs this
      rw [abs_mul, abs_neg, abs_mul, abs_of_pos (by linarith [abs_nonneg f.b])] at this
      rcases hs1 with rfl | rfl <;> simpa using this
    nlinarith [abs_nonneg f.b]
  subst hq0
  have : g.b = f.b := by rw [hgb]; simp; rw [hps]; ring
  exact absurd (by linarith : f.b = 0) hb0

/-- **Order-two classes are ambiguous.** A reduced form properly equivalent to its
opposite is ambiguous. -/
theorem ambiguous_of_equiv_opp (hr : f.IsReduced) (he : PEquiv f f.opp) : f.IsAmbiguous := by
  obtain ⟨h1, h2, h3⟩ := hr
  rcases h1.lt_or_eq with hab | hab
  · rcases h2.lt_or_eq with hac | hac
    · -- strict case: `f.opp` is reduced, so it equals `f` and `b = 0`
      have hopp : f.opp.IsReduced := by
        refine ⟨by simpa [opp] using hab.le, by simpa [opp] using hac.le, ?_⟩
        rintro (h | h)
        · simp [opp] at h; exact absurd h hab.ne
        · simp [opp] at h; exact absurd h hac.ne
      have := reduced_unique ⟨h1, h2, h3⟩ hopp (by simp [opp, disc]) he
      have hb := congrArg Form.b this
      simp [opp] at hb
      left; linarith
    · exact Or.inr (Or.inr hac)
  · have := h3 (Or.inl hab)
    rw [abs_of_nonneg this] at hab
    exact Or.inr (Or.inl hab)

end Form

end Clsgrp
