import Metrology.Approxis.AppWeakestpre

/-!
# Lifting Lemmas

Lifting lemmas that translate operational semantics rules into program logic rules.

## Port status (2026-04-24)

Of the 17 lifting lemmas in `clutch/theories/approxis/lifting.v`, **14 are
already ported directly into `Metrology/Approxis/AppWeakestpre.lean`** (they
were written there alongside the WP definition rather than being split out):

- `wp_lift_step_couple`, `wp_lift_step_spec_couple`, `wp_lift_step_prog_couple`
- `wp_lift_step_later`, `wp_lift_step`
- `wp_lift_prim_steps_coupl`, `wp_lift_prim_step_l_dret`, `wp_lift_prim_step_l_erasable`
- `wp_lift_pure_step`, `wp_lift_atomic_step_fupd`, `wp_lift_atomic_step`
- `wp_lift_pure_det_step`, `wp_pure_step_fupd`, `wp_pure_step_later`

This file supplies the remaining 3 adversarial-error variants, which
require `progCoupl_steps_adv` / `progCoupl_steps_adv'` and compute the
per-configuration error `X` on the WP continuation.

## Rocq source
`clutch/theories/approxis/lifting.v`
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS

namespace ProbLang.ApproxisWpGS

variable {GF : BundledGFunctors} [ApproxisWpGS GF]

/-- `wp_lift_prim_steps_coupl_adv` — one-LHS-step against a coupled RHS
primStep with an adversarial per-configuration error `X`, subject to
`X ≤ 1` and an additive `ε₂` slack. Mirrors `wp_lift_prim_steps_coupl_adv`
(lifting.v:231–262). -/
theorem wp_lift_prim_steps_coupl_adv {E : CoPset} {e₁ : Exp} {Φ : Val → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : State) (e₁' : Exp) (σ₁' : State) (ε : ENNReal),
      (stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗ errInterp ε) -∗
        |={E, ∅}=>
        ∃ (X : Cfg → Cfg → ENNReal) (ε₁ ε₂ : ENNReal),
          (⌜ε₁ + ε₂ ≤ ε⌝) ∗
          (⌜Reducible e₁ σ₁⌝) ∗
          (⌜Reducible e₁' σ₁'⌝) ∗
          (⌜∀ ρ₁ ρ₂, X ρ₁ ρ₂ ≤ 1⌝) ∗
          (⌜∀ (h₁ h₂ : Cfg → ENNReal),
              (∀ a, h₁ a ≤ 1) → (∀ b, h₂ b ≤ 1) →
              (∀ a b, h₁ a ≤ h₂ b + X a b) →
              (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩)) ≤
                (∫⁻ b, h₂ b ∂(primStep ⟨e₁', σ₁'⟩)) + ε₁⌝) ∗
          (∀ (e₂ : Exp) (σ₂ : State) (e₂' : Exp) (σ₂' : State),
            iprop(▷ |={∅, E}=>
              stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₂', σ₂'⟩ ∗
                errInterp (X ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + ε₂) ∗ wp E e₂ Φ))) ⊢@{IProp GF}
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
        stateInterp σ₄ ∗ SpecUpdateGS.specInterp ρ'' ∗ errInterp ε₄ ∗
          wp E e₃ Φ)))) Hεsum Hred Hred' Hbnd Hcpl)
  iintro %e₂ %σ₂ %e₂' %σ₂'
  imodintro
  iintro !>
  iapply specCoupl_ret
  ispecialize H $$ %e₂ %σ₂ %e₂' %σ₂'
  iexact H

/-- `wp_lift_prim_steps_coupl_adv'` — like `wp_lift_prim_steps_coupl_adv` but
with the entire error budget `ε` absorbed into `X` (no additive slack).
Mirrors `wp_lift_prim_steps_coupl_adv'` (lifting.v:265–295). -/
theorem wp_lift_prim_steps_coupl_adv' {E : CoPset} {e₁ : Exp} {Φ : Val → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : State) (e₁' : Exp) (σ₁' : State) (ε : ENNReal),
      (stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗ errInterp ε) -∗
        |={E, ∅}=>
        ∃ (X : Cfg → Cfg → ENNReal),
          (⌜Reducible e₁ σ₁⌝) ∗
          (⌜Reducible e₁' σ₁'⌝) ∗
          (⌜∀ ρ₁ ρ₂, X ρ₁ ρ₂ ≤ 1⌝) ∗
          (⌜∀ (h₁ h₂ : Cfg → ENNReal),
              (∀ a, h₁ a ≤ 1) → (∀ b, h₂ b ≤ 1) →
              (∀ a b, h₁ a ≤ h₂ b + X a b) →
              (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩)) ≤
                (∫⁻ b, h₂ b ∂(primStep ⟨e₁', σ₁'⟩)) + ε⌝) ∗
          (∀ (e₂ : Exp) (σ₂ : State) (e₂' : Exp) (σ₂' : State),
            iprop(▷ |={∅, E}=>
              stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₂', σ₂'⟩ ∗
                errInterp (X ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) ∗ wp E e₂ Φ))) ⊢@{IProp GF}
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
        stateInterp σ₄ ∗ SpecUpdateGS.specInterp ρ'' ∗ errInterp ε₄ ∗
          wp E e₃ Φ)))) Hred Hred' Hbnd Hcpl)
  iintro %e₂ %σ₂ %e₂' %σ₂'
  imodintro
  iintro !>
  iapply specCoupl_ret
  ispecialize H $$ %e₂ %σ₂ %e₂' %σ₂'
  iexact H

/-- `wp_lift_prim_steps_coupl_adv_err_le_1` — like `wp_lift_prim_steps_coupl_adv`
but the continuation may *bail out* if `X(ρ₂) + ε₂ ≥ 1` (in which case the
remaining error budget is saturated). Mirrors `wp_lift_prim_steps_coupl_adv_err_le_1`
(lifting.v:298–340). -/
theorem wp_lift_prim_steps_coupl_adv_err_le_1 {E : CoPset} {e₁ : Exp}
    {Φ : Val → IProp GF} (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : State) (e₁' : Exp) (σ₁' : State) (ε : ENNReal),
      (stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗ errInterp ε) -∗
        |={E, ∅}=>
        ∃ (X : Cfg → Cfg → ENNReal) (ε₁ ε₂ : ENNReal),
          (⌜ε₁ + ε₂ ≤ ε⌝) ∗
          (⌜Reducible e₁ σ₁⌝) ∗
          (⌜Reducible e₁' σ₁'⌝) ∗
          (⌜∀ ρ₁ ρ₂, X ρ₁ ρ₂ ≤ 1⌝) ∗
          (⌜∀ (h₁ h₂ : Cfg → ENNReal),
              (∀ a, h₁ a ≤ 1) → (∀ b, h₂ b ≤ 1) →
              (∀ a b, h₁ a ≤ h₂ b + X a b) →
              (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩)) ≤
                (∫⁻ b, h₂ b ∂(primStep ⟨e₁', σ₁'⟩)) + ε₁⌝) ∗
          (∀ (e₂ : Exp) (σ₂ : State) (e₂' : Exp) (σ₂' : State),
            iprop(▷ |={∅, E}=>
              (⌜ 1 ≤ X ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + ε₂ ⌝) ∨
              (stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₂', σ₂'⟩ ∗
                errInterp (X ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + ε₂) ∗ wp E e₂ Φ)))) ⊢@{IProp GF}
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
        stateInterp σ₄ ∗ SpecUpdateGS.specInterp ρ'' ∗ errInterp ε₄ ∗
          wp E e₃ Φ)))) Hεsum Hred Hred' Hbnd Hcpl)
  iintro %e₂ %σ₂ %e₂' %σ₂'
  imodintro
  iintro !>
  ispecialize H $$ %e₂ %σ₂ %e₂' %σ₂'
  -- Case-split on the disjunction in the continuation.
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
