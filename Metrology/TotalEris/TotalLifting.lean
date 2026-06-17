module

public import Metrology.TotalEris.TotalWeakestpre

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang
open scoped ENNReal

namespace ProbLang

variable {rT : Type _} [ProbLang.ProbLangℝ rT]

namespace TotalEris
namespace ErisWpGS

variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]

/-! # Total-WP lifting lemmas -/

theorem twp_lift_step_fupd_glm {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) : iprop%
    (∀ (σ₁ : State rT) (ε₁ : ENNReal), (stateInterp σ₁ ∗ errInterp (rT := rT) ε₁) -∗
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
    (∀ (σ₁ : State rT), stateInterp σ₁ -∗ |={E, ∅}=>
      ⌜Reducible e₁ σ₁⌝ ∗
      ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜R σ₁ (⟨e₂, σ₂⟩ : Cfg rT)⌝) -∗
        |={∅}=> |={∅, E}=> stateInterp σ₂ ∗ tglWp E e₂ Φ)
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
    (∀ (σ₁ : State rT), stateInterp σ₁ -∗ |={E, ∅}=>
      (⌜Reducible e₁ σ₁⌝) ∗
      ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜Possible (⟨e₂, σ₂⟩ : Cfg rT) (primStep ⟨e₁, σ₁⟩)⌝) -∗
        |={∅}=> |={∅, E}=>
          stateInterp σ₂ ∗ tglWp E e₂ Φ)
      ⊢@{IProp GF} tglWp E e₁ Φ :=
  twp_lift_step_fupd_gen hv
    (fun σ₁ ρ => Possible ρ (primStep ⟨e₁, σ₁⟩))
    (fun σ₁ => by
      have hset : {ρ : Cfg rT | Possible ρ (primStep ⟨e₁, σ₁⟩)}
          = {ρ | 0 < primStep ⟨e₁, σ₁⟩ {ρ}} := Set.ext fun ρ => possible_iff_pos
      rw [hset]; exact measurableSet_primStep_support e₁ σ₁)
    (fun σ₁ => by
      have hset : {ρ : Cfg rT | Possible ρ (primStep ⟨e₁, σ₁⟩)}
          = {ρ | 0 < primStep ⟨e₁, σ₁⟩ {ρ}} := Set.ext fun ρ => possible_iff_pos
      rw [hset]; exact (primStep_atomic e₁ σ₁).concentrated_atoms)

theorem twp_lift_atomic_step_fupd {E₁ : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) : iprop%
    (∀ (σ₁ : State rT), stateInterp σ₁ -∗ |={E₁}=>
      ⌜Reducible e₁ σ₁⌝ ∗
      ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜Possible (⟨e₂, σ₂⟩ : Cfg rT) (primStep ⟨e₁, σ₁⟩)⌝) -∗ |={E₁}=>
          stateInterp σ₂ ∗
          iprop(match e₂.toVal? with | some v => Φ v | none => iprop(False : IProp GF)))
      ⊢@{IProp GF} tglWp E₁ e₁ Φ := by
  iintro H
  iapply twp_lift_step_fupd hv
  iintro %σ₁ Hσ
  imod H $$ %σ₁ Hσ with ⟨%Hred, HCont⟩
  imod (BIFUpdate.subset (E1 := E₁) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  iframe %Hred
  iintro %e₂ %σ₂ %Hstep
  imodintro
  imod Hclose
  ispecialize HCont $$ %e₂ %σ₂ %Hstep
  imod HCont with ⟨Hσ', HΦv⟩
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
  imod H with H
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  isplitr; · ipureintro; exact Hsafe σ₁
  iintro %e₂ %σ₂ %Hstep'
  imodintro
  imod Hclose
  imodintro
  cases Hstep _ _ _ Hstep'
  isplitl [Hσ]; · iexact Hσ
  iapply H; ipureintro; exact Hstep'

theorem twp_lift_pure_det_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ e₂ : Exp rT}
    (hv : e₁.toVal? = none)
    (Hsafe : ∀ σ₁, Reducible e₁ σ₁)
    (Hpuredet : ∀ σ₁ e₂' σ₂, Possible (⟨e₂', σ₂⟩ : Cfg rT) (primStep ⟨e₁, σ₁⟩) →
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

theorem twp_lift_atomic_head_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : State rT), stateInterp σ₁ -∗ |={E}=>
      (⌜HeadReducible e₁ σ₁⌝) ∗
      ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜Possible (⟨e₂, σ₂⟩ : Cfg rT) (headStep ⟨e₁, σ₁⟩)⌝) -∗ |={E}=>
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
  isplitr
  · ipureintro
    exact reducible_of_headReducible Hhred
  iintro %e₂ %σ₂ %Hpstep
  have heq : primStep ⟨e₁, σ₁⟩ = headStep ⟨e₁, σ₁⟩ := by
    exact primStep_eq_headStep Hhred
  have hpos : Possible (⟨e₂, σ₂⟩ : Cfg rT) (headStep ⟨e₁, σ₁⟩) := heq ▸ Hpstep
  iapply HCont $$ %e₂ %σ₂ %hpos

theorem twp_lift_pure_det_head_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ e₂ : Exp rT}
    (hv : e₁.toVal? = none)
    (Hsafe : ∀ σ₁, ∃ ρ : Cfg rT, Possible ρ (headStep ⟨e₁, σ₁⟩))
    -- How is this used? Can it be changed to be the Dirac critereon?
    (Hdet : ∀ σ₁ e₂' σ₂, Possible (⟨e₂', σ₂⟩ : Cfg rT) (headStep ⟨e₁, σ₁⟩) → σ₂ = σ₁ ∧ e₂' = e₂) :
    iprop(|={E}=> tglWp E e₂ Φ) ⊢@{IProp GF} tglWp E e₁ Φ := by
  iapply twp_lift_pure_det_step hv
    (Hsafe := fun σ => Reducible.of_head ((Hsafe σ).elim fun _ hρ => hρ.ne_zero))
  intros σ e₂' σ₂ hp
  have heq : primStep ⟨e₁, σ⟩ = headStep ⟨e₁, σ⟩ :=
    primStep_eq_headStep ((Hsafe σ).elim fun _ hρ => hρ.ne_zero)
  exact Hdet σ e₂' σ₂ (heq ▸ hp)

/-! ## `PureExec_discrete` integration -/

theorem twp_lift_pure_det_step_of_pureStep
    {E : CoPset} {Φ : Val rT → IProp GF} {e₁ e₂ : Exp rT}
    (h : PureStep e₁ e₂) :
    iprop(|={E}=> tglWp E e₂ Φ) ⊢@{IProp GF} tglWp E e₁ Φ := by
  have hv : e₁.toVal? = none := Exp.toVal?_eq_none.mpr <| val_stuck <| h.safe default
  iapply twp_lift_pure_det_step hv h.safe
  intros σ e₂' σ₂ hp
  have hpt := h.det σ
  by_contra hne
  have hother : (⟨e₂', σ₂⟩ : Cfg rT) ≠ ⟨e₂, σ⟩ := by
    intro heq
    cases heq
    exact hne ⟨rfl, rfl⟩
  rw [hpt, possible_iff_pos, dirac_singleton_pos'] at hp
  exact hother hp.symm

theorem twp_pure_step_fupd
    {E : CoPset} {Φ : Val rT → IProp GF} {n : ℕ} {e₁ e₂ : Exp rT}
    (φ : Prop) [HEx : PureExec φ n e₁ e₂] (Hφ : φ) :
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
