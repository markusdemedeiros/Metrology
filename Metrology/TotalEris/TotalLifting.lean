module

public import Metrology.TotalEris.TotalWeakestpre

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang
open scoped ENNReal

namespace ProbLang


variable {rT : Type _} [ProbLang.ProbLangℝ rT] -- [Countable rT]

namespace TotalEris
namespace ErisWpGS

variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]

/-! # Total-WP lifting lemmas

Port of `clutch/theories/eris/total_lifting.v`. These let us prove
`tgl_wp` triples by exhibiting an appropriate `glm` coupling. Mirrors
the partial-WP lifting in `Metrology/TotalEris/Lifting.lean`. -/

-- omit [Countable rT] in
/-- Lift a `glm`-shaped predicate into `tgl_wp`. Rocq:
`twp_lift_step_fupd_glm`. -/
theorem twp_lift_step_fupd_glm [Countable rT] {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : State rT) (ε₁ : ENNReal),
      (stateInterp σ₁ ∗ errInterp (rT := rT) ε₁) -∗
        |={E, ∅}=> glm e₁ σ₁ ε₁ (fun ρ ε₂ =>
          iprop(|={∅, E}=>
            stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ tglWp E ρ.expr Φ))) ⊢@{IProp GF}
      tglWp E e₁ Φ := by
  iintro HG
  iapply tglWp_unfold
  unfold tglWpPre
  iintro %σ %ε ⟨Hσ, Hε⟩
  rw [hv]
  iapply HG $$ %σ %ε
  isplitl [Hσ]; · iexact Hσ
  iexact Hε

/-- Lift a step rule that doesn't need an `err_interp` change.

Rocq: `twp_lift_step_fupd`. -/
theorem twp_lift_step_fupd [Countable rT] {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : State rT), stateInterp σ₁ -∗ |={E, ∅}=>
      (⌜Discrete.Reducible e₁ σ₁⌝) ∗
      ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜0 < primStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝) -∗
        |={∅}=> |={∅, E}=>
          stateInterp σ₂ ∗ tglWp E e₂ Φ) ⊢@{IProp GF}
      tglWp E e₁ Φ := by
  iintro H
  iapply twp_lift_step_fupd_glm hv
  iintro %σ₁ %ε₁ ⟨Hσ, Hε⟩
  imod H $$ %σ₁ Hσ with ⟨%Hred, HCont⟩
  imodintro
  iapply glm_prim_step
  iexists (fun ρ => 0 < primStep ⟨e₁, σ₁⟩ {ρ}), 0, (fun _ => ε₁), ε₁
  isplitr; · ipure_intro; exact Hred
  isplitr; · ipure_intro; intro _; exact _root_.le_refl _
  isplitr
  · ipure_intro
    -- `ε₁ * primStep(univ) ≤ ε₁ * 1 = ε₁` for the sub-probability measure `primStep`.
    rw [zero_add, MeasureTheory.lintegral_const]
    calc ε₁ * primStep ⟨e₁, σ₁⟩ Set.univ
        ≤ ε₁ * 1 := by gcongr; exact primStep_univ_le_one _
      _ = ε₁ := mul_one ε₁
  isplitr; · ipure_intro; exact Pgl.zero_positive _
  iintro %ρ %HR
  ispecialize HCont $$ %ρ.expr %ρ.state %HR
  imod HCont with HC
  imodintro
  iright
  imod HC with ⟨Hσ', HW⟩
  imodintro
  isplitl [Hσ']
  · iexact Hσ'
  isplitl [Hε]
  · iexact Hε
  iexact HW

/-- Lift an atomic-step (post-condition delivered on the value
of the stepped expression). Rocq: `twp_lift_atomic_step_fupd`. -/
theorem twp_lift_atomic_step_fupd [Countable rT] {E₁ : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : State rT), stateInterp σ₁ -∗ |={E₁}=>
      (⌜Discrete.Reducible e₁ σ₁⌝) ∗
      ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜0 < primStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝) -∗ |={E₁}=>
          stateInterp σ₂ ∗
          iprop(match e₂.toVal? with
                | some v => Φ v
                | none => iprop(False : IProp GF)))
      ⊢@{IProp GF} tglWp E₁ e₁ Φ := by
  iintro H
  iapply (twp_lift_step_fupd hv)
  iintro %σ₁ Hσ
  imod H $$ %σ₁ Hσ with ⟨%Hred, HCont⟩
  imod (BIFUpdate.subset (E1 := E₁) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  isplitr; · ipure_intro; exact Hred
  iintro %e₂ %σ₂ %Hstep
  imodintro
  imod Hclose
  ispecialize HCont $$ %e₂ %σ₂ %Hstep
  imod HCont with ⟨Hσ', HΦv⟩
  imodintro
  isplitl [Hσ']; · iexact Hσ'
  cases htv : e₂.toVal? with
  | some v =>
    iapply (tglWp_value_of_toVal htv)
    iexact HΦv
  | none =>
    iexfalso
    iexact HΦv

/-- Lift a pure (state-preserving, possibly-nondeterministic) reduction.
Rocq: `twp_lift_pure_step`. -/
theorem twp_lift_pure_step [Countable rT] {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none)
    (Hsafe : ∀ σ₁, Discrete.Reducible e₁ σ₁)
    (Hstep : ∀ σ₁ e₂ σ₂, 0 < primStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩} → σ₂ = σ₁) :
    iprop(|={E}=>
      ∀ (e₂ : Exp rT) (σ : State rT),
        (⌜0 < primStep ⟨e₁, σ⟩ {⟨e₂, σ⟩}⌝) -∗
        tglWp E e₂ Φ) ⊢@{IProp GF}
      tglWp E e₁ Φ := by
  iintro H
  iapply (twp_lift_step_fupd hv)
  iintro %σ₁ Hσ
  imod H with H
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  isplitr; · ipure_intro; exact Hsafe σ₁
  iintro %e₂ %σ₂ %Hstep'
  imodintro
  imod Hclose
  imodintro
  cases Hstep _ _ _ Hstep'
  isplitl [Hσ]; · iexact Hσ
  iapply H; ipure_intro; exact Hstep'

/-- Single deterministic pure step. Rocq: `twp_lift_pure_det_step`. -/
theorem twp_lift_pure_det_step [Countable rT] {E : CoPset} {Φ : Val rT → IProp GF} {e₁ e₂ : Exp rT}
    (hv : e₁.toVal? = none)
    (Hsafe : ∀ σ₁, Discrete.Reducible e₁ σ₁)
    (Hpuredet : ∀ σ₁ e₂' σ₂, 0 < primStep ⟨e₁, σ₁⟩ {⟨e₂', σ₂⟩} →
      σ₂ = σ₁ ∧ e₂' = e₂) :
    iprop(|={E}=> tglWp E e₂ Φ) ⊢@{IProp GF} tglWp E e₁ Φ := by
  iintro H
  iapply (twp_lift_pure_step hv Hsafe
    (fun σ e₂' σ₂ hstep => (Hpuredet σ e₂' σ₂ hstep).1))
  imod H with H
  imodintro
  iintro %e₂' %σ %Hstep
  obtain ⟨_, heq⟩ := Hpuredet σ e₂' σ Hstep
  subst heq
  iexact H

/-! ## Head-step bridges

The primitive WP laws prefer `headStep` over `primStep` because head steps
are easier to discriminate (no ambient context). The bridges below convert
between the two views. -/

/-- Atomic-step lifting via `headStep`. Rocq: `twp_lift_atomic_head_step`. -/
theorem twp_lift_atomic_head_step [Countable rT] {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : State rT), stateInterp σ₁ -∗ |={E}=>
      (⌜∃ ρ : Cfg rT, 0 < headStep ⟨e₁, σ₁⟩ {ρ}⌝) ∗
      ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜0 < headStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝) -∗ |={E}=>
          stateInterp σ₂ ∗
          iprop(match e₂.toVal? with
                | some v => Φ v
                | none => iprop(False : IProp GF)))
      ⊢@{IProp GF} tglWp E e₁ Φ := by
  iintro H
  iapply (twp_lift_atomic_step_fupd hv)
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ Hσ
  imod H with ⟨%Hhred, HCont⟩
  imodintro
  isplitr; · ipure_intro; exact Discrete.Reducible.of_head Hhred
  iintro %e₂ %σ₂ %Hpstep
  have heq : primStep ⟨e₁, σ₁⟩ = headStep ⟨e₁, σ₁⟩ := primStep_eq_headStep_discrete Hhred
  have hpos : 0 < headStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩} := heq ▸ Hpstep
  iapply HCont $$ %e₂ %σ₂ %hpos

/-- Pure-deterministic head-step lifting. Rocq: `twp_lift_pure_det_head_step`. -/
theorem twp_lift_pure_det_head_step [Countable rT] {E : CoPset} {Φ : Val rT → IProp GF} {e₁ e₂ : Exp rT}
    (hv : e₁.toVal? = none)
    (Hsafe : ∀ σ₁, ∃ ρ : Cfg rT, 0 < headStep ⟨e₁, σ₁⟩ {ρ})
    (Hdet : ∀ σ₁ e₂' σ₂, 0 < headStep ⟨e₁, σ₁⟩ {⟨e₂', σ₂⟩} → σ₂ = σ₁ ∧ e₂' = e₂) :
    iprop(|={E}=> tglWp E e₂ Φ) ⊢@{IProp GF} tglWp E e₁ Φ := by
  iapply twp_lift_pure_det_step hv (Hsafe := fun σ => Discrete.Reducible.of_head (Hsafe σ))
  intros σ e₂' σ₂ hp
  have heq : primStep ⟨e₁, σ⟩ = headStep ⟨e₁, σ⟩ := primStep_eq_headStep_discrete (Hsafe σ)
  exact Hdet σ e₂' σ₂ (heq ▸ hp)

/-! ## `PureExec_discrete` integration -/

/-- From a single `PureStep_discrete e₁ e₂` (deterministic, state-preserving, safe),
take one step. Used by the `n+1` case of `twp_pure_step_fupd`. -/
theorem twp_lift_pure_det_step_of_pureStep [Countable rT]
    {E : CoPset} {Φ : Val rT → IProp GF} {e₁ e₂ : Exp rT}
    (h : PureStep_discrete e₁ e₂) :
    iprop(|={E}=> tglWp E e₂ Φ) ⊢@{IProp GF} tglWp E e₁ Φ := by
  -- The first reducibility witness gives us a non-value status.
  have hv : e₁.toVal? = none := by
    obtain ⟨ρ, hρ⟩ := h.safe default
    exact Exp.toVal?_eq_none.mpr (Discrete.val_stuck hρ)
  iapply twp_lift_pure_det_step hv h.safe
  intros σ e₂' σ₂ hp
  -- `h.det σ` says `primStep ⟨e₁,σ⟩ {⟨e₂,σ⟩} = 1`. Combined with total mass
  -- ≤ 1, a positive-mass singleton other than ⟨e₂,σ⟩ would push the total
  -- past 1. So `⟨e₂',σ₂⟩ = ⟨e₂,σ⟩`.
  have htot := primStep_univ_le_one ⟨e₁, σ⟩
  have hpt := h.det σ
  by_contra hne
  have hother : (⟨e₂', σ₂⟩ : Cfg rT) ≠ ⟨e₂, σ⟩ := by
    intro heq
    cases heq
    exact hne ⟨rfl, rfl⟩
  have hadd : primStep ⟨e₁, σ⟩ ({⟨e₂', σ₂⟩} ∪ {⟨e₂, σ⟩} : Set (Cfg rT)) =
      primStep ⟨e₁, σ⟩ {⟨e₂', σ₂⟩} + primStep ⟨e₁, σ⟩ {⟨e₂, σ⟩} :=
    MeasureTheory.measure_union (by simp [hother]) (MeasurableSet.singleton _)
  have hsum_le : primStep ⟨e₁, σ⟩ {⟨e₂', σ₂⟩} + primStep ⟨e₁, σ⟩ {⟨e₂, σ⟩} ≤
      primStep ⟨e₁, σ⟩ Set.univ := by
    rw [← hadd]
    exact MeasureTheory.measure_mono (Set.subset_univ _)
  rw [hpt] at hsum_le
  have hsum_gt : 1 < primStep ⟨e₁, σ⟩ {⟨e₂', σ₂⟩} + 1 := by
    rw [add_comm]
    exact ENNReal.lt_add_right ENNReal.one_ne_top hp.ne'
  exact absurd (hsum_le.trans htot) (_root_.not_le.mpr hsum_gt)

/-- Take `n` pure-deterministic steps. Rocq: `twp_pure_step_fupd`. -/
theorem twp_pure_step_fupd [Countable rT]
    {E : CoPset} {Φ : Val rT → IProp GF} {n : ℕ} {e₁ e₂ : Exp rT}
    (φ : Prop) [HEx : PureExec_discrete φ n e₁ e₂] (Hφ : φ) :
    tglWp E e₂ Φ ⊢@{IProp GF} tglWp E e₁ Φ := by
  have Hex := HEx.pure_exec Hφ
  clear HEx
  induction n generalizing e₁ with
  | zero =>
    simp only [nsteps] at Hex
    subst Hex
    iintro H; iexact H
  | succ n ih =>
    obtain ⟨c, hstep, hrest⟩ := Hex
    iintro H
    iapply twp_lift_pure_det_step_of_pureStep hstep
    imodintro
    ihave Hih := ih hrest
    iapply Hih
    iexact H

end ErisWpGS
end TotalEris
end ProbLang
