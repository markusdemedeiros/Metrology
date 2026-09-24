module

public import Metrology.ProbLang.HeadStep
import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.CtxStep

@[expose] public section

/-! # Atomic Expressions -/

namespace ProbLang

variable {rT : Type _} [LawfulProbLangℝ rT]

/-- Atomic: Each atom that can be prim-stepped to is a value.

This is the *discrete* formulation, and it is vacuously true for the continuous
sampler `urand`: a diffuse measure gives every singleton zero mass, so there are
no atoms to constrain. Use `Atomic'` instead; `Atomic` survives only as a
convenient way to *prove* `Atomic'` for discrete redexes (`Atomic.toAtomic'`). -/
def Atomic (e : Exp rT) : Prop :=
  ∀ σ e' σ', 0 < primStep ⟨e, σ⟩ {⟨e', σ'⟩} → e'.isValue

/-- **Support-level atomicity.** The step measure is *concentrated* on the set of
value configurations: whatever `e` steps to is a value, up to a null set.

Unlike `Atomic` this says something real about diffuse measures, so it covers the
continuous sampler (`Atomic.urand'`). It is the form the program logic actually
consumes — see `Approxis.OpenInv.of_atomic`. -/
def Atomic' (e : Exp rT) : Prop :=
  ∀ σ, Concentrated (primStep ⟨e, σ⟩) { ρ | ρ.1.isValue }

namespace Atomic

theorem primStep_eq_headStep_of_decomp_nil
    {e : Exp rT} (hd : e.decompItem = none) (σ : State rT) :
    primStep ⟨e, σ⟩ = headStep ⟨e, σ⟩ := by
  have hde : e.decomp = ([], e) := by
    rw [Exp.decomp_unfold, hd]
  simp only [primStep, hde, Ectx.fillCfg_empty, MeasureTheory.Measure.map_id]

/-- **The discrete-to-support bridge.** For a redex that is not the continuous
sampler, atomicity of the step measure (`primStep_atomic`) says it lives on its
atom set, and `Atomic` says every atom is a value configuration. Composing the two
gives concentration on the value set.

This is the only place the discrete `e.decomp.2 ≠ .urand` side condition is needed,
and it is discharged here at concrete redexes — where `decomp` actually reduces —
rather than being threaded through the program logic. -/
theorem toAtomic' {e : Exp rT} (h : Atomic e) (hne : e.decomp.2 ≠ .urand) :
    Atomic' e := by
  intro σ
  refine Concentrated.mono ?_ (primStep_atomic e σ hne).concentrated_atoms
  rintro ⟨e', σ'⟩ hpos
  exact h σ e' σ' hpos

/-! ## Instances for the ops used by Compatibility -/

theorem load (l : Loc) : Atomic (rT := rT) pl(!#(.loc l)) := by
  intro σ e' σ' hpos
  have hd : (pl(!#(.loc l)) : Exp rT).decompItem = none := rfl
  rw [primStep_eq_headStep_of_decomp_nil hd] at hpos
  replace hpos := Possible.headStepSupport (possible_iff_pos.mpr hpos)
  cases hpos with
  | LoadS _ he' =>
    -- he' : e' = Exp.ofVal v. Exp.ofVal v = v.1, which is a value.
    rename_i v _
    subst he'
    exact v.2.toIsValue


theorem store (l : Loc) (v : Val rT) :
    Atomic (.store pl(#(.loc l)) v.1) := by
  intro σ e' σ' hpos
  have hv : v.1.toVal? = some v := Exp.toVal?_ofVal v
  have hd : (Exp.store pl(#(.loc l)) v.1).decompItem = none := by
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

theorem rand_unit (z : Int) : Atomic (rT := rT) (pl(rand(#(.int z), #(.unit)))) := by
  intro σ e' σ' hpos
  have hd : (pl(rand(#(.int z), #(.unit))) : Exp rT).decompItem = none := rfl
  rw [primStep_eq_headStep_of_decomp_nil hd] at hpos
  replace hpos := Possible.headStepSupport (possible_iff_pos.mpr hpos)
  cases hpos with
  | RandNoTapeS _ _ _ => exact IsVal.lit.toIsValue
  | RandNonposS _ => exact IsVal.lit.toIsValue

theorem rand_lbl (z : Int) (l : Loc) :
    Atomic (rT := rT) (pl(rand(#(.int z), #(.lbl l)))) := by
  intro σ e' σ' hpos
  have hd : (pl(rand(#(.int z), #(.lbl l))) : Exp rT).decompItem = none := rfl
  rw [primStep_eq_headStep_of_decomp_nil hd] at hpos
  replace hpos := Possible.headStepSupport (possible_iff_pos.mpr hpos)
  cases hpos with
  | RandTapeS _ _ _ _ => exact IsVal.lit.toIsValue
  | RandTapeEmptyS _ _ _ _ _ _ => exact IsVal.lit.toIsValue
  | RandTapeOtherS _ _ _ _ _ _ => exact IsVal.lit.toIsValue
  | RandTapeNonposEmptyS _ _ _ => exact IsVal.lit.toIsValue
  | RandTapeNonposOtherS _ _ _ => exact IsVal.lit.toIsValue

/-! ## `Atomic'` for the redexes the program logic opens invariants around

Each is the corresponding `Atomic` fact pushed through `Atomic.toAtomic'`. The
`decomp.2 ≠ .urand` obligation reduces by `rfl` here because the redex is a
concrete constructor. -/

theorem load' (l : Loc) : Atomic' (rT := rT) pl(!#(.loc l)) :=
  toAtomic' (load l) (by rw [Exp.decomp_snd_of_decompItem_none rfl]; nofun)

theorem store' (l : Loc) (v : Val rT) : Atomic' (.store pl(#(.loc l)) v.1) := by
  have hv : v.1.toVal? = some v := Exp.toVal?_ofVal v
  have hd : (Exp.store pl(#(.loc l)) v.1).decompItem = none := by
    show (v.1.toVal?.casesOn _ _ : Option _) = none
    rw [hv]
    rfl
  exact toAtomic' (store l v) (by rw [Exp.decomp_snd_of_decompItem_none hd]; nofun)

theorem alloc' (v : Val rT) : Atomic' (.alloc v.1) := by
  have hv : v.1.toVal? = some v := Exp.toVal?_ofVal v
  have hd : (Exp.alloc v.1).decompItem = none := by
    show (v.1.toVal?.casesOn _ _ : Option _) = none
    rw [hv]
  exact toAtomic' (alloc v) (by rw [Exp.decomp_snd_of_decompItem_none hd]; nofun)

theorem rand_unit' (z : Int) : Atomic' (rT := rT) (pl(rand(#(.int z), #(.unit)))) :=
  toAtomic' (rand_unit z) (by rw [Exp.decomp_snd_of_decompItem_none rfl]; nofun)

theorem rand_lbl' (z : Int) (l : Loc) :
    Atomic' (rT := rT) (pl(rand(#(.int z), #(.lbl l)))) :=
  toAtomic' (rand_lbl z l) (by rw [Exp.decomp_snd_of_decompItem_none rfl]; nofun)

/-- **The continuous sampler is `Atomic'`.** `urand` has no atoms at all, so
`Atomic` says nothing about it; but its step measure is a pushforward of `unifUnit`
along `r ↦ ⟨pl(#(.real r)), σ⟩`, whose entire image consists of value
configurations. Concentration holds because the bad set pulls back to `∅` — no
atomicity, no countability, no discreteness. -/
theorem urand' : Atomic' (rT := rT) .urand := by
  intro σ
  have hd : (pl(urand) : Exp rT).decompItem = none := rfl
  rw [primStep_eq_headStep_of_decomp_nil hd]
  show (Cfg.uniformReal σ) {ρ : Cfg rT | ρ.1.isValue}ᶜ = 0
  rw [Cfg.uniformReal, MeasureTheory.Measure.map_apply (by fun_prop) Cfg.isValue_measurableSet.compl]
  convert MeasureTheory.measure_empty (μ := LawfulProbLangℝ.unifUnit)
  ext r
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false, not_not]
  exact IsVal.lit.toIsValue

end Atomic

end ProbLang
