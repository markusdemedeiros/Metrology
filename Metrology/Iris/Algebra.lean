module

public import Iris
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.MeasureTheory.Measure.Sub
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Iris.Algebra.View
public import Iris.Instances.IProp.Instance
public import Iris.Algebra.Auth
public import Iris.Algebra.Numbers

@[expose] public section

local stepindex Nat

open Std Iris COFE ProbabilityTheory MeasureTheory

noncomputable section

instance authMeasureOFE [MeasurableSpace α] : OFE (Measure α) where
  dist _ x y := x = y
  dist_eqv := ⟨fun _ => rfl, (Eq.symm ·), (Eq.trans · ·)⟩
  eq_dist' := .symm <| forall_const _
  dist_lt H _ := H

instance [MeasurableSpace α] : RA (Measure α) where
  pcore _ := .some 0
  op μ₁ μ₂ := μ₁ + μ₂
  assoc := by simp [add_assoc]
  comm := by simp [add_comm]
  pcore_op_left := by simp
  pcore_idem := by simp

instance [MeasurableSpace α] : CMRA (Measure α) := ORA.ofCMRAData {
  Valid μ := μ .univ ≤ 1
  ValidN _ μ := μ .univ ≤ 1
  op_ne.ne {_ _ _} H := by rw [H]
  pcore_ne _ := by rintro ⟨rfl⟩; exact ⟨0, rfl, rfl⟩
  validN_ne := (· ▸ ·)
  valid_iff_validN := ⟨fun H _ => H, fun H => H 0⟩
  validN_le H _ := H
  validN_op_left := (le_of_add_le_of_nonneg_left · <| zero_le)
  pcore_op_mono {_ _} := by
    rintro ⟨rfl⟩ Y
    exact ⟨0, Option.some_inj.mpr (zero_add 0).symm⟩
  extend {_ _ y1 y2} _ := (⟨y1, y2, ·, rfl, rfl⟩) }

instance [MeasurableSpace α] : URA (Measure α) where
  unit := 0
  unit_left_id := zero_add _
  pcore_unit := rfl
  total _ := ⟨0, rfl⟩

instance [MeasurableSpace α] : UCMRA (Measure α) := UORA.ofUCMRAData {
  unit_valid := show (0 : Measure α) .univ ≤ 1 by simp }


end
