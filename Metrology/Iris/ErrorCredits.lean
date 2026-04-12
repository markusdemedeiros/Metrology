import Iris
import Mathlib.Probability.Kernel.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Iris.Algebra.View
import Iris.Instances.IProp.Instance
import Iris.Algebra.Auth
import Iris.Algebra.Numbers

noncomputable section ErrorCredits

open Std Iris COFE ProbabilityTheory MeasureTheory

abbrev ErrorCredit : Type _ := ENNReal

instance : COFE ErrorCredit := COFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete ErrorCredit := ⟨id⟩

instance : CMRA ErrorCredit where
  pcore _ := some 0
  op := (· + ·)
  ValidN _ ε := ε < 1
  Valid ε := ε < 1
  op_ne.ne _ _ _ h := by rw [h]
  pcore_ne _ := by rintro ⟨rfl⟩; exists 0
  validN_ne {_ _ _} := by rintro ⟨rfl⟩; exact id
  valid_iff_validN := .symm <| forall_const Nat
  validN_succ := (·)
  validN_op_left {n x y} H := lt_of_add_lt_of_nonneg_left H (zero_le y)
  assoc {_ _ _} := (add_assoc ..).symm
  comm {_ _} := (add_comm ..).symm
  pcore_op_left {_ _} := by rintro ⟨rfl⟩; simp [OFE.Equiv]
  pcore_idem := by simp
  pcore_op_mono {_ _} := by rintro ⟨rfl⟩ _; exists 0; simp
  extend _ h := ⟨_, _, OFE.discrete h, .rfl, .rfl⟩

instance : UCMRA ErrorCredit where
  unit := 0
  unit_valid := by simp [CMRA.Valid]
  unit_left_id := by simp [CMRA.op]
  pcore_unit := by simp [CMRA.pcore]

theorem ErrorCredit.included_iff {ε₁ ε₂ : ErrorCredit} : ε₁ ≼ ε₂ ↔ ε₁ ≤ ε₂ := by
  refine ⟨?_, (⟨ε₂ - ε₁, add_tsub_cancel_of_le · |>.symm⟩)⟩
  rintro ⟨ε₃, rfl⟩
  exact le_self_add

instance {ε : ErrorCredit} : CMRA.Cancelable ε where
  cancelableN {n ε₁ ε₂} := by
    simp [CMRA.ValidN, CMRA.op, OFE.Dist]
    intro H1 H2
    -- refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
    -- · rintro rfl; simp at H1
    -- · rintro rfl
    --   simp only [add_top, ENNReal.add_eq_top] at H2
    --   rcases H2 with (rfl|rfl) <;> simp at H1
    sorry

theorem ErrorCredit.localUpdate {ε₁ ε₂ ε₁' ε₂' : ErrorCredit} (h1 : ε₂' <= ε₂)
    (h2 : ε₁ + ε₂' = ε₁' + ε₂) : (ε₁, ε₂) ~l~> (ε₁', ε₂') := by
  rintro n (_|ε) <;> simp only [OFE.Dist, CMRA.op?, CMRA.ValidN, CMRA.op]
  · rintro H rfl
    refine ⟨?_, ?_⟩
    · sorry
    · sorry
  · rintro H rfl
    refine ⟨?_, ?_⟩
    · sorry
    · sorry

end ErrorCredits
