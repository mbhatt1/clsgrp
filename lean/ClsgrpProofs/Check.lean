import ClsgrpProofs.Reduction

/-! Axiom audit and a worked example. Built by `lake build`. -/

open Clsgrp Form

-- `N = 15 = 3 · 5`: the non-principal reduced form `(2, 1, 2)` is ambiguous (`a = c`)
-- and its factor is `2·2 - 1 = 3`.
example : (⟨2, 1, 2⟩ : Form).disc = -15 := by decide
example : (⟨2, 1, 2⟩ : Form).factor = 3 := by decide
-- `N = 35 = 5 · 7`: `(3, 1, 3)` gives `5`.
example : (⟨3, 1, 3⟩ : Form).disc = -35 ∧ (⟨3, 1, 3⟩ : Form).factor = 5 := by decide

#print axioms Form.reduced_unique
#print axioms Form.ambiguous_of_equiv_opp
#print axioms ClassGroupModel.red_ambiguous
#print axioms Form.factor_spec
#print axioms Form.eq_prime_factor
#print axioms Clsgrp.exists_orderOf_eq_two
#print axioms Clsgrp.two_mul_card_oddPart_le
#print axioms Clsgrp.factor_of_classNumber
#print axioms Clsgrp.half_succeed
#print axioms Clsgrp.one_le_k_of_orderOf_two

/-! Non-vacuity: `Cl(-15) ≅ ℤ/2` with reduced forms `(1,1,4)` and `(2,1,2)` satisfies every
hypothesis of `ClassGroupModel`, and Theorem 1 then returns the factor `3`. -/

/-- The reduced representatives of `Cl(-15)`. -/
def red15 (g : Multiplicative (ZMod 2)) : Form :=
  if g = 1 then principal 15 else ⟨2, 1, 2⟩

def cl15 : ClassGroupModel 15 (Multiplicative (ZMod 2)) where
  red := red15
  red_injective := by unfold red15; decide
  red_reduced := by
    intro g; unfold red15 principal Form.IsReduced
    split_ifs <;> norm_num
  red_disc := by intro g; unfold red15 principal disc; split_ifs <;> norm_num
  red_one := by simp [red15]
  red_inv := by
    intro g
    have hg : g⁻¹ = g := by revert g; decide
    rw [hg]; unfold red15
    split_ifs
    · exact ⟨1, -1, 0, 1, by norm_num, by decide⟩
    · exact ⟨0, -1, 1, 0, by norm_num, by decide⟩

example : ∃ j < 1, (cl15.red ((Multiplicative.ofAdd 1 ^ 1) ^ (2 ^ j))).factor = 3 ∨
    (cl15.red ((Multiplicative.ofAdd 1 ^ 1) ^ (2 ^ j))).factor = 5 :=
  factor_of_classNumber cl15 (p := 3) (q := 5) (by norm_num) (by norm_num) (by norm_num)
    (by decide) (k := 1) (m := 1) (by rfl) (by decide)
