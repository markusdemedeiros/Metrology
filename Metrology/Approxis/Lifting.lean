module

public import Metrology.Approxis.AppWeakestpre

@[expose] public section

set_option linter.discrete false

/-! # Lifting lemmas translating operational semantics rules into program-logic rules. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS

/-! For the Approxis layer, carry the abstract real type `rT` as a section variable. -/


variable {rT : Type _} [ProbLang.ProbLangℝ rT] [MeasurableSingletonClass rT]

namespace ProbLang.ApproxisWpGS

variable {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) GF]

theorem wp_lift_prim_steps_coupl_adv {E : CoPset} {e₁ : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : (State rT)) (e₁' : (Exp rT)) (σ₁' : (State rT)) (ε : ENNReal),
      (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε) -∗
        |={E, ∅}=>
        ∃ (X : (Cfg rT) → (Cfg rT) → ENNReal) (ε₁ ε₂ : ENNReal),
          (⌜ε₁ + ε₂ ≤ ε⌝) ∗
          (⌜Reducible e₁ σ₁⌝) ∗
          (⌜Reducible e₁' σ₁'⌝) ∗
          (⌜∀ ρ₁ ρ₂, X ρ₁ ρ₂ ≤ 1⌝) ∗
          (⌜∀ (h₁ h₂ : (Cfg rT) → ENNReal),
              Measurable h₁ → Measurable h₂ →
              (∀ a, h₁ a ≤ 1) → (∀ b, h₂ b ≤ 1) →
              (∀ a b, h₁ a ≤ h₂ b + X a b) →
              (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩)) ≤
                (∫⁻ b, h₂ b ∂(primStep ⟨e₁', σ₁'⟩)) + ε₁⌝) ∗
          (∀ (e₂ : (Exp rT)) (σ₂ : (State rT)) (e₂' : (Exp rT)) (σ₂' : (State rT)),
            iprop(▷ |={∅, E}=>
              stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₂', σ₂'⟩ ∗
                errInterp (rT := rT) (X ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + ε₂) ∗ wp E e₂ Φ))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  ispecialize H $$ %σ₁ %e₁' %σ₁' %ε [Hσ Hs Hε]
  · isplitl [Hσ]; · iassumption
    isplitl [Hs] <;> iassumption
  imod H with ⟨%X, %ε₁, %ε₂, %Hεsum, %Hred, %Hred', %Hbnd, %Hcpl, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply (progCoupl_steps_adv (Z := fun e₃ σ₃ e₃' σ₃' ε₃ =>
    iprop(▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
      iprop(|={∅, E}=>
        stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗ errInterp (rT := rT) ε₄ ∗
          wp E e₃ Φ)))) Hεsum Hred Hred' Hbnd Hcpl)
  iintro %e₂ %σ₂ %e₂' %σ₂'
  imodintro
  iintro !>
  iapply specCoupl_ret
  ispecialize H $$ %e₂ %σ₂ %e₂' %σ₂'
  iexact H

theorem wp_lift_prim_steps_coupl_adv' {E : CoPset} {e₁ : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : (State rT)) (e₁' : (Exp rT)) (σ₁' : (State rT)) (ε : ENNReal),
      (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε) -∗
        |={E, ∅}=>
        ∃ (X : (Cfg rT) → (Cfg rT) → ENNReal),
          (⌜Reducible e₁ σ₁⌝) ∗
          (⌜Reducible e₁' σ₁'⌝) ∗
          (⌜∀ ρ₁ ρ₂, X ρ₁ ρ₂ ≤ 1⌝) ∗
          (⌜∀ (h₁ h₂ : (Cfg rT) → ENNReal),
              Measurable h₁ → Measurable h₂ →
              (∀ a, h₁ a ≤ 1) → (∀ b, h₂ b ≤ 1) →
              (∀ a b, h₁ a ≤ h₂ b + X a b) →
              (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩)) ≤
                (∫⁻ b, h₂ b ∂(primStep ⟨e₁', σ₁'⟩)) + ε⌝) ∗
          (∀ (e₂ : (Exp rT)) (σ₂ : (State rT)) (e₂' : (Exp rT)) (σ₂' : (State rT)),
            iprop(▷ |={∅, E}=>
              stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₂', σ₂'⟩ ∗
                errInterp (rT := rT) (X ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) ∗ wp E e₂ Φ))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  ispecialize H $$ %σ₁ %e₁' %σ₁' %ε [Hσ Hs Hε]
  · isplitl [Hσ]; · iassumption
    isplitl [Hs] <;> iassumption
  imod H with ⟨%X, %Hred, %Hred', %Hbnd, %Hcpl, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply (progCoupl_steps_adv' (Z := fun e₃ σ₃ e₃' σ₃' ε₃ =>
    iprop(▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
      iprop(|={∅, E}=>
        stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗ errInterp (rT := rT) ε₄ ∗
          wp E e₃ Φ)))) Hred Hred' Hbnd Hcpl)
  iintro %e₂ %σ₂ %e₂' %σ₂'
  imodintro
  iintro !>
  iapply specCoupl_ret
  ispecialize H $$ %e₂ %σ₂ %e₂' %σ₂'
  iexact H

/-- The continuation may bail out if `X(ρ₂) + ε₂ ≥ 1`, saturating the error budget. -/
theorem wp_lift_prim_steps_coupl_adv_err_le_1 {E : CoPset} {e₁ : (Exp rT)}
    {Φ : (Val rT) → IProp GF} (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : (State rT)) (e₁' : (Exp rT)) (σ₁' : (State rT)) (ε : ENNReal),
      (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε) -∗
        |={E, ∅}=>
        ∃ (X : (Cfg rT) → (Cfg rT) → ENNReal) (ε₁ ε₂ : ENNReal),
          (⌜ε₁ + ε₂ ≤ ε⌝) ∗
          (⌜Reducible e₁ σ₁⌝) ∗
          (⌜Reducible e₁' σ₁'⌝) ∗
          (⌜∀ ρ₁ ρ₂, X ρ₁ ρ₂ ≤ 1⌝) ∗
          (⌜∀ (h₁ h₂ : (Cfg rT) → ENNReal),
              Measurable h₁ → Measurable h₂ →
              (∀ a, h₁ a ≤ 1) → (∀ b, h₂ b ≤ 1) →
              (∀ a b, h₁ a ≤ h₂ b + X a b) →
              (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩)) ≤
                (∫⁻ b, h₂ b ∂(primStep ⟨e₁', σ₁'⟩)) + ε₁⌝) ∗
          (∀ (e₂ : (Exp rT)) (σ₂ : (State rT)) (e₂' : (Exp rT)) (σ₂' : (State rT)),
            iprop(▷ |={∅, E}=>
              (⌜ 1 ≤ X ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + ε₂ ⌝) ∨
              (stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₂', σ₂'⟩ ∗
                errInterp (rT := rT) (X ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + ε₂) ∗ wp E e₂ Φ)))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  ispecialize H $$ %σ₁ %e₁' %σ₁' %ε [Hσ Hs Hε]
  · isplitl [Hσ]; · iassumption
    isplitl [Hs] <;> iassumption
  imod H with ⟨%X, %ε₁, %ε₂, %Hεsum, %Hred, %Hred', %Hbnd, %Hcpl, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply (progCoupl_steps_adv (Z := fun e₃ σ₃ e₃' σ₃' ε₃ =>
    iprop(▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
      iprop(|={∅, E}=>
        stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗ errInterp (rT := rT) ε₄ ∗
          wp E e₃ Φ)))) Hεsum Hred Hred' Hbnd Hcpl)
  iintro %e₂ %σ₂ %e₂' %σ₂'
  imodintro
  iintro !>
  ispecialize H $$ %e₂ %σ₂ %e₂' %σ₂'
  by_cases hle : (X ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + ε₂ : ENNReal) < 1
  · iapply specCoupl_ret
    imod H
    icases H with (%Hge | ⟨Hσ', Hs', Hε', Hwp'⟩)
    · exact absurd Hge (by exact fun h => absurd (h.trans_lt hle) (lt_irrefl _))
    · imodintro
      isplitl [Hσ']; · iassumption
      isplitl [Hs']; · iassumption
      isplitl [Hε']; · iassumption
      iassumption
  · iapply specCoupl_err_ge_1 (_root_.not_lt.mp hle)

end ProbLang.ApproxisWpGS
