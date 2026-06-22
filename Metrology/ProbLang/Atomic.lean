module

public import Metrology.ProbLang.HeadStep
public import Metrology.ProbLang.CtxStep

@[expose] public section

/-! # Atomic Expressions -/

namespace ProbLang

variable {rT : Type _} [ProbLangℝ rT]

-- FIXME: I think by this definition all real-returning operations are atomic?
-- Since all atoms have measure zero... this seems very wrong.

/-- Atomic: Each atom that can be prim-stepped to is a value. -/
def Atomic (e : Exp rT) : Prop :=
  ∀ σ e' σ', 0 < primStep ⟨e, σ⟩ {⟨e', σ'⟩} → e'.isValue

/-- Measurable version of atomicity?
The set that we can PrimStep has mass concentrated on the set of value configurations. -/
def Atomic' (e : Exp rT) : Prop :=
  ∀ σ, Concentrated (primStep ⟨e, σ⟩) { ρ | ρ.1.isValue }

namespace Atomic

theorem primStep_eq_headStep_of_decomp_nil
    {e : Exp rT} (hd : e.decompItem = none) (σ : State rT) :
    primStep ⟨e, σ⟩ = headStep ⟨e, σ⟩ := by
  have hde : e.decomp = ([], e) := by
    rw [Exp.decomp_unfold, hd]
  simp only [primStep, hde, Ectx.fillCfg_empty, MeasureTheory.Measure.map_id]

/-! ## Instances for the ops used by Compatibility -/

theorem load (l : Loc) : Atomic (rT := rT) (.load (.lit (.loc l))) := by
  intro σ e' σ' hpos
  have hd : (Exp.load (.lit (.loc l)) : Exp rT).decompItem = none := rfl
  rw [primStep_eq_headStep_of_decomp_nil hd] at hpos
  replace hpos := Possible.headStepSupport (possible_iff_pos.mpr hpos)
  cases hpos with
  | LoadS _ he' =>
    -- he' : e' = Exp.ofVal v. Exp.ofVal v = v.1, which is a value.
    rename_i v _
    subst he'
    exact v.2.toIsValue


theorem store (l : Loc) (v : Val rT) :
    Atomic (.store (.lit (.loc l)) v.1) := by
  intro σ e' σ' hpos
  have hv : v.1.toVal? = some v := Exp.toVal?_ofVal v
  have hd : (Exp.store (.lit (.loc l)) v.1).decompItem = none := by
    show (v.1.toVal?.casesOn _ _ : Option _) = none
    rw [hv]
    rfl
  rw [primStep_eq_headStep_of_decomp_nil hd] at hpos
  replace hpos := Possible.headStepSupport (possible_iff_pos.mpr hpos)
  cases hpos with
  | StoreS _ _ _ => exact IsVal.lit.toIsValue

theorem alloc (v : Val rT) : Atomic (.alloc v.1) := by
  intro σ e' σ' hpos
  have hv : v.1.toVal? = some v := Exp.toVal?_ofVal v
  have hd : (Exp.alloc v.1).decompItem = none := by
    show (v.1.toVal?.casesOn _ _ : Option _) = none
    rw [hv]
  rw [primStep_eq_headStep_of_decomp_nil hd] at hpos
  replace hpos := Possible.headStepSupport (possible_iff_pos.mpr hpos)
  cases hpos with
  | AllocS _ _ _ => exact IsVal.lit.toIsValue

theorem rand_unit (z : Int) : Atomic (rT := rT) (.rand (.lit (.int z)) (.lit .unit)) := by
  intro σ e' σ' hpos
  have hd : (Exp.rand (.lit (.int z)) (.lit .unit) : Exp rT).decompItem = none := rfl
  rw [primStep_eq_headStep_of_decomp_nil hd] at hpos
  replace hpos := Possible.headStepSupport (possible_iff_pos.mpr hpos)
  cases hpos with
  | RandNoTapeS _ _ _ => exact IsVal.lit.toIsValue
  | RandNonposS _ => exact IsVal.lit.toIsValue

theorem rand_lbl (z : Int) (l : Loc) :
    Atomic (rT := rT) (.rand (.lit (.int z)) (.lit (.lbl l))) := by
  intro σ e' σ' hpos
  have hd : (Exp.rand (.lit (.int z)) (.lit (.lbl l)) : Exp rT).decompItem = none := rfl
  rw [primStep_eq_headStep_of_decomp_nil hd] at hpos
  replace hpos := Possible.headStepSupport (possible_iff_pos.mpr hpos)
  cases hpos with
  | RandTapeS _ _ _ _ => exact IsVal.lit.toIsValue
  | RandTapeEmptyS _ _ _ _ _ _ => exact IsVal.lit.toIsValue
  | RandTapeOtherS _ _ _ _ _ _ => exact IsVal.lit.toIsValue
  | RandTapeNonposEmptyS _ _ _ => exact IsVal.lit.toIsValue
  | RandTapeNonposOtherS _ _ _ => exact IsVal.lit.toIsValue

end Atomic

end ProbLang
