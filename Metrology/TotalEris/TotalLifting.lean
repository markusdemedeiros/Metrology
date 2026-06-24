module

public import Metrology.TotalEris.TotalWeakestpre

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang
open scoped ENNReal

namespace ProbLang
namespace TotalEris
namespace ErisWpGS

variable {rT : Type _} [ProbLangℝ rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]

/-! # Total-WP lifting lemmas -/

theorem twp_lift_step_fupd_glm {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ ε₁, stateInterp σ₁ ∗ errInterp (rT := rT) ε₁ -∗
        |={E, ∅}=> glm' e₁ σ₁ ε₁ (fun ρ ε₂ => iprop%
          |={∅, E}=> stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ tglWp E ρ.expr Φ))
    ⊢@{IProp GF} tglWp E e₁ Φ := by
  iintro HG
  iapply tglWp_unfold
  unfold tglWpPre
  iintro %σ %ε ⟨Hσ, Hε⟩
  simp only [hv]
  iapply HG $$ %σ %ε
  iframe

theorem twp_lift_step_fupd_gen {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) (R : State rT → Cfg rT → Prop) (hRmeas : ∀ σ₁, MeasurableSet {ρ | R σ₁ ρ})
    (hconc : ∀ σ₁, Concentrated (primStep ⟨e₁, σ₁⟩) {ρ | R σ₁ ρ}) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E, ∅}=>
      ⌜Reducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜R σ₁ ⟨e₂, σ₂⟩⌝ -∗ |={∅}=> |={∅, E}=> stateInterp σ₂ ∗ tglWp E e₂ Φ)
    ⊢@{IProp GF} tglWp E e₁ Φ := by
  iintro H
  iapply twp_lift_step_fupd_glm hv
  iintro %σ₁ %ε₁ ⟨Hσ, Hε⟩
  imod H $$ %σ₁ Hσ with ⟨%Hred, HCont⟩
  imodintro
  iapply glm'_prim_step
  iexists (R σ₁), 0, (fun _ => ε₁), ε₁
  have hfr (ρ : Cfg rT) : (fun x ↦ ε₁) ρ ≤ ε₁ := _root_.le_refl _
  specialize hRmeas σ₁
  have hfr' : Pgl 0 (R σ₁) (primStep ⟨e₁, σ₁⟩) := Pgl.of_concentrated (hconc σ₁)
  iframe %Hred %hRmeas %hfr %hfr'
  isplitr
  · ipureintro
    calc  0 + ∫⁻ ρ, (fun _ ↦ ε₁) ρ ∂primStep ⟨e₁, σ₁⟩
        = ∫⁻ ρ, (fun _ ↦ ε₁) ρ ∂primStep ⟨e₁, σ₁⟩ := by grind
      _ = ε₁ * primStep ⟨e₁, σ₁⟩ .univ := by rw [MeasureTheory.lintegral_const]
      _ ≤ ε₁ * 1 := by gcongr; exact primStep_univ_le_one _
      _ = ε₁ := mul_one ε₁
  iintro %ρ %HR
  ispecialize HCont $$ %ρ.expr %ρ.state %HR
  imod HCont with HC
  imodintro
  iright
  imod HC with ⟨Hσ', HW⟩
  iframe

theorem twp_lift_step_fupd {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E, ∅}=>
      ⌜Reducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜Possible ⟨e₂, σ₂⟩ (primStep ⟨e₁, σ₁⟩)⌝ -∗
        |={∅}=> |={∅, E}=> stateInterp σ₂ ∗ tglWp E e₂ Φ)
    ⊢@{IProp GF} tglWp E e₁ Φ :=
  twp_lift_step_fupd_gen hv
    (fun σ₁ ρ => Possible ρ (primStep ⟨e₁, σ₁⟩))
    (fun σ₁ => measurableSet_possible_support)
    (fun σ₁ => by
      have hset : {ρ : Cfg rT | Possible ρ (primStep ⟨e₁, σ₁⟩)}
          = {ρ | 0 < primStep ⟨e₁, σ₁⟩ {ρ}} := Set.ext fun ρ => possible_iff_pos
      -- TODO: Make primStep_atomic use Possible instead
      rw [hset]; exact (primStep_atomic e₁ σ₁).concentrated_atoms)

theorem twp_lift_atomic_step_fupd {E₁ : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E₁}=>
      ⌜Reducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜Possible ⟨e₂, σ₂⟩ (primStep ⟨e₁, σ₁⟩)⌝ -∗ |={E₁}=>
          stateInterp σ₂ ∗ match e₂.toVal? with | some v => Φ v | none => iprop% False)
      ⊢@{IProp GF} tglWp E₁ e₁ Φ := by
  iintro H
  iapply twp_lift_step_fupd hv
  iintro %σ₁ Hσ
  imod H $$ %σ₁ Hσ with ⟨%Hred, HCont⟩
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  iframe %Hred
  iintro %e₂ %σ₂ %Hstep
  imodintro
  imod Hclose with -
  imod HCont $$ %e₂ %σ₂ %Hstep with ⟨Hσ', HΦv⟩
  imodintro
  iframe Hσ'
  cases htv : e₂.toVal? with
  | some v => iapply tglWp_value_of_toVal htv $$ [$]
  | none => iexfalso; iexact HΦv

theorem twp_lift_pure_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) (Hsafe : ∀ σ₁, Reducible e₁ σ₁)
    (Hstep : ∀ σ₁ e₂ σ₂, Possible (⟨e₂, σ₂⟩ : Cfg rT) (primStep ⟨e₁, σ₁⟩) → σ₂ = σ₁) : iprop%
    (|={E}=> ∀ e₂ σ, ⌜Possible ⟨e₂, σ⟩ (primStep ⟨e₁, σ⟩)⌝ -∗ tglWp E e₂ Φ)
    ⊢@{IProp GF} tglWp E e₁ Φ := by
  iintro H
  iapply twp_lift_step_fupd hv
  iintro %σ₁ Hσ
  imod H
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  specialize Hsafe σ₁
  iframe %Hsafe
  iintro %e₂ %σ₂ %Hstep'
  imodintro
  imod Hclose
  imodintro
  cases Hstep _ _ _ Hstep'
  iframe Hσ
  iapply H $$ %_ %_ %Hstep'

theorem twp_lift_pure_det_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ e₂ : Exp rT}
    (hv : e₁.toVal? = none) (Hsafe : ∀ σ₁, Reducible e₁ σ₁)
    (Hpuredet : ∀ σ₁ e₂' σ₂, Possible ⟨e₂', σ₂⟩ (primStep ⟨e₁, σ₁⟩) → σ₂ = σ₁ ∧ e₂' = e₂) : iprop%
    (|={E}=> tglWp E e₂ Φ) ⊢@{IProp GF} tglWp E e₁ Φ := by
  iintro H
  iapply twp_lift_pure_step hv Hsafe (fun σ e₂' σ₂ hstep => (Hpuredet σ e₂' σ₂ hstep).1)
  imod H
  imodintro
  iintro %e₂' %σ %Hstep
  obtain ⟨_, rfl⟩ := Hpuredet σ e₂' σ Hstep
  iexact H

theorem twp_lift_atomic_head_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E}=>
      ⌜HeadReducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜Possible ⟨e₂, σ₂⟩ (headStep ⟨e₁, σ₁⟩)⌝ -∗ |={E}=>
          stateInterp σ₂ ∗ match e₂.toVal? with | some v => Φ v | none => iprop% False)
      ⊢@{IProp GF} tglWp E e₁ Φ := by
  iintro H
  iapply twp_lift_atomic_step_fupd hv
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ Hσ
  imod H with ⟨%Hhred, HCont⟩
  rw [← primStep_eq_headStep Hhred]
  replace Hhred := reducible_of_headReducible Hhred
  imodintro
  iframe %Hhred
  iintro %e₂ %σ₂ %Hpstep
  iapply HCont $$ %e₂ %σ₂ %_
  exact Hpstep

theorem twp_lift_pure_det_head_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ e₂ : Exp rT}
    (hv : e₁.toVal? = none)
    (Hsafe : ∀ σ₁, ∃ ρ : Cfg rT, Possible ρ (headStep ⟨e₁, σ₁⟩))
    (Hdet : ∀ σ₁ e₂' σ₂, Possible (⟨e₂', σ₂⟩ : Cfg rT) (headStep ⟨e₁, σ₁⟩) → σ₂ = σ₁ ∧ e₂' = e₂) :
    iprop(|={E}=> tglWp E e₂ Φ) ⊢@{IProp GF} tglWp E e₁ Φ := by
  iapply twp_lift_pure_det_step hv (Hsafe := fun σ => .of_head ((Hsafe σ).elim fun _ hρ => hρ.ne_zero))
  refine fun σ e₂' σ₂ hp => Hdet σ e₂' σ₂ ?_
  rw [← primStep_eq_headStep ((Hsafe σ).elim fun _ hρ => hρ.ne_zero)]
  exact hp

/-! ## `PureExec_discrete` integration -/

theorem twp_lift_pure_det_step_of_pureStep {E : CoPset} {Φ : Val rT → IProp GF} {e₁ e₂ : Exp rT}
    (h : PureStep e₁ e₂) : iprop(|={E}=> tglWp E e₂ Φ) ⊢@{IProp GF} tglWp E e₁ Φ := by
  have hv : e₁.toVal? = none := Exp.toVal?_eq_none.mpr <| val_stuck <| h.safe default
  iapply twp_lift_pure_det_step hv h.safe
  intros σ e₂' σ₂ hp
  by_contra hne
  rw [h.det σ, possible_iff_pos, dirac_singleton_pos'] at hp
  have hother : (⟨e₂', σ₂⟩ : Cfg rT) ≠ ⟨e₂, σ⟩ := by
    rintro ⟨⟩; exact hne ⟨rfl, rfl⟩
  exact hother hp.symm

/-- `is_value` discharges the side conditions of ProbLang pure reduction steps.

A pure step's precondition `φ` is one of:
* `e.isValue` (`Nonempty (IsVal e)`) — built structurally from the `IsVal`
  constructors (`lit`/`lam`/`fix`/`inl`/`inr`/`pair`);
* `True` (e.g. `cond`); or
* the `∧`-conjunctions that `binop`/`unop`/`scrut`/`pair` steps carry — value-hood
  facts together with an evaluator equation `op.eval … = some …` closed by `rfl`.

This is the same logic the `twp_pure` elaborator runs inline; it is exposed here so
it can serve as the `autoParam` discharger for `twp_pure_step_fupd`'s precondition
(so explicit-endpoint pure steps need no hand-written `IsVal` witness), and so the
escape-hatch tactics (`twp_pure_at`) can reuse it. -/
syntax "is_value" : tactic
macro_rules
  | `(tactic| is_value) =>
    `(tactic| first
        | trivial
        | repeat' (first
            | rfl
            | exact ProbLang.IsVal.lit | exact ProbLang.IsVal.lam | exact ProbLang.IsVal.fix
            | apply ProbLang.IsVal.inl | apply ProbLang.IsVal.inr | apply ProbLang.IsVal.pair
            | refine ⟨?_, ?_⟩    -- split `∧` (binop/unop/scrut side condition)
            | refine ⟨?_⟩))      -- enter `Nonempty (IsVal …)`

theorem twp_pure_step_fupd {E : CoPset} {Φ : Val rT → IProp GF} {n : ℕ} {e₁ e₂ : Exp rT}
    (φ : Prop) [HEx : PureExec φ n e₁ e₂] (Hφ : φ := by is_value) :
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
    iapply ih hrest $$ [$]

end ErisWpGS
end TotalEris
end ProbLang
