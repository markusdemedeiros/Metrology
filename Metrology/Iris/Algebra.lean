module

public import Iris
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.MeasureTheory.Measure.Sub
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Iris.Algebra.View
public import Iris.Instances.IProp.Instance
public import Iris.Algebra.Auth
public import Iris.Algebra.Numbers

@[expose] public section

open Std Iris COFE ProbabilityTheory MeasureTheory

noncomputable section

instance : UFraction ℕ+ where
  Proper := (· ≤ 1)
  add_comm := by grind
  add_assoc := by grind
  add_left_cancel := by simp
  add_ne {a b} H := by
    cases a; cases b
    rename_i va ha vb hb
    have : va = vb + va := by injection H
    omega
  proper_add_mono_left := by
    intro a b hab
    cases a; cases b
    rename_i va ha vb hb
    change va + vb ≤ 1 at hab
    change va ≤ 1
    omega
  one_whole := by
    simp only [Fraction.Whole, _root_.le_refl, Fraction.Fractional,
      PNat.le_one_iff, not_exists, true_and]
    intro b
    have : 1 + b ≠ 1 := by
      cases b; rename_i vb hb
      intro H
      have : 1 + vb = 1 := by injection H
      omega
    exact this

instance authMeasureOFE [MeasurableSpace α] : OFE (Measure α) where
  Equiv x y := x = y
  Dist _ x y := x = y
  dist_eqv := ⟨fun _ => rfl, (Eq.symm ·), (Eq.trans · ·)⟩
  equiv_dist := .symm <| forall_const _
  dist_lt H _ := H

-- CMRA of subprobability distributions with addition
instance [MeasurableSpace α] : CMRA (Measure α) where
  pcore _ := .some 0
  op μ₁ μ₂ := μ₁ + μ₂
  Valid μ := μ .univ ≤ 1
  ValidN _ μ := μ .univ ≤ 1
  op_ne.ne {_ _ _} H := by rw [H]
  pcore_ne := by simp
  validN_ne := (· ▸ ·)
  valid_iff_validN := ⟨fun H _ => H, fun H => H 0⟩
  validN_succ := (·)
  validN_op_left := (le_of_add_le_of_nonneg_left · <| zero_le _)
  assoc := by simp [add_assoc]
  comm := by simp [add_comm]
  pcore_op_left := by simp
  pcore_idem := by simp
  pcore_op_mono {_ _} := by
    rintro ⟨rfl⟩ Y
    exact ⟨0, .of_eq <| Option.some_inj.mpr (zero_add 0).symm⟩
  extend {_ _ y1 y2} _ := (⟨y1, y2, ·, rfl, rfl⟩)

instance [MeasurableSpace α] : UCMRA (Measure α) where
  unit := 0
  unit_valid := by simp [CMRA.Valid]
  unit_left_id := by
    intro μ
    refine .of_eq (zero_add _)
  pcore_unit := by simp [CMRA.pcore]


-- class WpMarkov (GF : BundledGFunctors) (T : Type _) [MeasurableSpace T] where
--   state : ElemG GF (constOF (Measure T))
--   state_γ : GName
--
-- export WpMarkov (state_γ)
-- attribute [reducible, instance] WpMarkov.state
--
-- section logic
--
-- variable {GF : BundledGFunctors} {T : Type _} [MeasurableSpace T] [WpMarkov GF T]
--
-- def bound (μ : Measure T) := @iOwn GF _ _ WpMarkov.state (WpMarkov.state_γ GF T) μ
--
--
-- variable (κ : Kernel T T)
--
-- def step (μ : Measure T) : Measure T := μ.bind κ
--
-- def is_value (μ : Measure T) : Prop := step κ μ = μ
--
-- def twp_F (μΦ : Measure T × (Measure T → IProp GF))
--     (twp : (Measure T × (Measure T → IProp GF)) → IProp GF) : IProp GF := iprop(
--   (⌜is_value κ μΦ.1⌝ ∗ |==> μΦ.2 μΦ.1) ∨
--   (|==> (twp (step κ μΦ.1, μΦ.2))))
--
-- end logic
end
