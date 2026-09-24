module

public import Metrology.Approxis.AppWeakestpre

@[expose] public section


/-! # Lifting lemmas translating operational semantics rules into program-logic rules. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS

/-! For the Approxis layer, carry the abstract real type `rT` as a section variable. -/


variable {rT : Type _} [ProbLang.LawfulProbLangℝ rT]

namespace ProbLang.ApproxisWpGS

variable {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) GF]

theorem wp_lift_prim_steps_coupl_adv {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ e₁' σ₁' ε,
      (stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε) -∗
        |={E, ∅}=>
        ∃ (X : Cfg rT → Cfg rT → ENNReal) (ε₁ ε₂ : ENNReal),
          ⌜ε₁ + ε₂ ≤ ε⌝ ∗
          ⌜Reducible e₁ σ₁⌝ ∗
          ⌜Reducible e₁' σ₁'⌝ ∗
          ⌜∀ ρ₁ ρ₂, X ρ₁ ρ₂ ≤ 1⌝ ∗
          ⌜ExpCoupl ε₁ X (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)⌝ ∗
          (∀ e₂ σ₂ e₂' σ₂', ▷ |={∅, E}=>
            stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₂', σ₂'⟩ ∗
              errInterp (rT := rT) (X ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + ε₂) ∗ wp E e₂ Φ)) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply (wp_lift_step_prog_couple Hv)
  iintro %σ₁ %e₁' %σ₁' %ε Hpre
  ispecialize H $$ %σ₁ %e₁' %σ₁' %ε Hpre
  imod H with ⟨%X, %ε₁, %ε₂, %Hεsum, %Hred, %Hred', %Hbnd, %Hcpl, H⟩
  imodintro
  iapply progCoupl_steps_adv Hεsum Hred Hred' Hbnd Hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' !> !>
  iapply H $$ %e₂ %σ₂ %e₂' %σ₂'

theorem wp_lift_prim_steps_coupl_adv' {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ e₁' σ₁' ε,
      (stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε) -∗
        |={E, ∅}=>
        ∃ (X : Cfg rT → Cfg rT → ENNReal),
          ⌜Reducible e₁ σ₁⌝ ∗
          ⌜Reducible e₁' σ₁'⌝ ∗
          ⌜∀ ρ₁ ρ₂, X ρ₁ ρ₂ ≤ 1⌝ ∗
          ⌜ExpCoupl ε X (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)⌝ ∗
          (∀ e₂ σ₂ e₂' σ₂', ▷ |={∅, E}=>
            stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₂', σ₂'⟩ ∗
              errInterp (rT := rT) (X ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) ∗ wp E e₂ Φ)) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply (wp_lift_step_prog_couple Hv)
  iintro %σ₁ %e₁' %σ₁' %ε Hpre
  ispecialize H $$ %σ₁ %e₁' %σ₁' %ε Hpre
  imod H with ⟨%X, %Hred, %Hred', %Hbnd, %Hcpl, H⟩
  imodintro
  iapply progCoupl_steps_adv' Hred Hred' Hbnd Hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' !> !>
  iapply H $$ %e₂ %σ₂ %e₂' %σ₂'

/-- The continuation may bail out if `X(ρ₂) + ε₂ ≥ 1`, saturating the error budget. -/
theorem wp_lift_prim_steps_coupl_adv_err_le_1 {E : CoPset} {e₁ : Exp rT}
    {Φ : Val rT → IProp GF} (Hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ e₁' σ₁' ε,
      (stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε) -∗
        |={E, ∅}=>
        ∃ (X : Cfg rT → Cfg rT → ENNReal) (ε₁ ε₂ : ENNReal),
          ⌜ε₁ + ε₂ ≤ ε⌝ ∗
          ⌜Reducible e₁ σ₁⌝ ∗
          ⌜Reducible e₁' σ₁'⌝ ∗
          ⌜∀ ρ₁ ρ₂, X ρ₁ ρ₂ ≤ 1⌝ ∗
          ⌜ExpCoupl ε₁ X (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)⌝ ∗
          (∀ e₂ σ₂ e₂' σ₂', ▷ |={∅, E}=>
            ⌜1 ≤ X ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + ε₂⌝ ∨
            (stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₂', σ₂'⟩ ∗
              errInterp (rT := rT) (X ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + ε₂) ∗ wp E e₂ Φ))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  -- Unlike the two lemmas above we stay at the `specCoupl` layer: the `1 ≤ ε` bail-out
  -- is `specCoupl_err_ge_1`, which is unavailable once we commit to `progCoupl` alone.
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε Hpre
  ispecialize H $$ %σ₁ %e₁' %σ₁' %ε Hpre
  imod H with ⟨%X, %ε₁, %ε₂, %Hεsum, %Hred, %Hred', %Hbnd, %Hcpl, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply progCoupl_steps_adv Hεsum Hred Hred' Hbnd Hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' !> !>
  ispecialize H $$ %e₂ %σ₂ %e₂' %σ₂'
  by_cases hle : (X ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + ε₂ : ENNReal) < 1
  · iapply specCoupl_ret
    imod H
    icases H with (%Hge | H)
    · exact absurd hle (_root_.not_lt.mpr Hge)
    · imodintro
      iexact H
  · iapply specCoupl_err_ge_1 (_root_.not_lt.mp hle)

/-- Couple two *erasable* state distributions without taking a program step. -/
theorem wp_couple_erasables {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} : iprop%
    (∀ σ₁ e₁' σ₁' ε,
      (stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε) -∗
        |={E, ∅}=>
        ∃ (R : State rT → State rT → Prop)
          (μ₁ μ₁' : MeasureTheory.Measure (State rT)),
          ⌜ErasableExpr μ₁ σ₁⌝ ∗ ⌜ErasableExpr μ₁' σ₁'⌝ ∗
          ⌜AddCoupl 0 {p : State rT × State rT | R p.1 p.2} μ₁ μ₁'⌝ ∗
          (∀ σ₂ σ₂', ⌜R σ₂ σ₂'⌝ -∗ |={∅, E}=>
            stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₂'⟩ ∗
              errInterp (rT := rT) ε ∗ wp E e Φ)) ⊢@{IProp GF} wp E e Φ := by
  iintro H
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %ε Hpre
  ispecialize H $$ %σ₁ %e₁' %σ₁' %ε Hpre
  imod H with ⟨%R, %μ₁, %μ₁', %Her, %Her', %Hcpl, H⟩
  imodintro
  iapply specCoupl_erasables (by rw [zero_add]) Hcpl Her Her'
  iintro %σ₂ %σ₂' %HR !>
  iapply specCoupl_ret
  iapply H $$ %σ₂ %σ₂' %HR

end ProbLang.ApproxisWpGS
