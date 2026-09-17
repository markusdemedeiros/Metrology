module

public import Metrology.Approxis.PrimitiveLaws

@[expose] public section

/-!
# Continuous sampler rules

WP rules for ProbLang's *diffuse* sampler `urand`, which lies outside the
discrete fragment: `unifUnit` may have no atoms, so every atom-based step rule
(`wp_lift_atomic_step`, `progCoupl_step_l`, …) is vacuous for it.

This file deliberately carries **no `[Countable rT]`** in its variable block, so
everything here is machine-checked to hold for a diffuse real type. It is the
landing place for further continuous rules.

The rules are built on the `_concentrated` family in `AppWeakestpre.lean`, which
replaces "land on an atom" by "land in a measurable set carrying the step
measure" (`ProbLang.Concentrated`).
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS
open scoped AppGS

namespace ProbLang

variable {rT : Type _} [ProbLang.ProbLangℝ rT] [MeasurableSingletonClass rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ApproxisGS rT hlc GF]

/-- **`wp_urand` — a WP rule for the continuous sampler.**

This is the payoff of the `_concentrated` generalization: `urand` samples from a
*diffuse* measure, so it has no atoms and every atom-based step rule is vacuous
for it. Here the carrying set is the real-literal image
`{⟨.lit (.real r), σ₁⟩ | r ∈ unifUnitSupport}`, which `primStep ⟨urand, σ₁⟩`
lives on by `concentratedOn_map`, and which is measurable because the injection
`r ↦ ⟨.lit (.real r), σ₁⟩` is a `MeasurableEmbedding`.

Note the absence of `[Countable rT]`: the whole point is that this rule holds for
a diffuse `rT`. Follows the same shape as `TotalEris.twp_urand_exp`, minus the
error credits (a plain atomic lift spends none). -/
theorem wp_urand {E : CoPset} {Φ : (Val rT) → IProp GF} :
    iprop(▷ ∀ (r : rT), (⌜r ∈ ProbLangℝ.unifUnitSupport⌝) -∗ Φ (.real r : Val rT))
      ⊢@{IProp GF} wp E (Exp.urand) Φ := by
  iintro HΦ
  have Hnv : (Exp.urand : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  have hhead : ∀ σ₁ : State rT, HeadReducible (Exp.urand : Exp rT) σ₁ :=
    fun σ₁ => show Cfg.uniformReal σ₁ ≠ 0 from MeasureTheory.IsProbabilityMeasure.ne_zero _
  have hps : ∀ σ₁ : State rT, primStep (⟨Exp.urand, σ₁⟩ : Cfg rT)
      = (ProbLangℝ.unifUnit (T := rT)).map (fun r : rT => (⟨.lit (.real r), σ₁⟩ : Cfg rT)) :=
    fun σ₁ => primStep_eq_headStep
      (Exp.decompItem_none_of_lc_headReducible (by is_lc) (hhead σ₁))
  have hg : ∀ σ₁ : State rT, Measurable (fun r : rT => (⟨.lit (.real r), σ₁⟩ : Cfg rT)) :=
    fun σ₁ => Cfg.measurable_iff.mpr
      ⟨Exp.lit.measurable.comp BaseLit.real.measurable, measurable_const⟩
  have hgemb : ∀ σ₁ : State rT,
      MeasurableEmbedding (fun r : rT => (⟨.lit (.real r), σ₁⟩ : Cfg rT)) := fun σ₁ => by
    have hcomp : (fun r : rT => (⟨.lit (.real r), σ₁⟩ : Cfg rT))
        = Cfg.measurableEquivProd.symm ∘ (fun e : Exp rT => (e, σ₁))
            ∘ Exp.lit ∘ BaseLit.real := rfl
    rw [hcomp]
    exact Cfg.measurableEquivProd.symm.measurableEmbedding.comp
      ((measurableEmbedding_prod_mk_right σ₁).comp
        (Exp.lit.measurableEmbedding.comp BaseLit.real.measurableEmbedding))
  have hrange : ∀ σ₁ : State rT,
      {ρ : Cfg rT | ∃ r : rT, ρ = (⟨.lit (.real r), σ₁⟩ : Cfg rT)
          ∧ r ∈ ProbLangℝ.unifUnitSupport}
      = (fun r : rT => (⟨.lit (.real r), σ₁⟩ : Cfg rT)) '' ProbLangℝ.unifUnitSupport :=
    fun σ₁ => by
      ext ρ; simp only [Set.mem_image, Set.mem_setOf_eq]
      exact ⟨fun ⟨r, h, hr⟩ => ⟨r, hr, h.symm⟩, fun ⟨r, hr, h⟩ => ⟨r, h.symm, hr⟩⟩
  have hSmeas : ∀ σ₁ : State rT, MeasurableSet
      {ρ : Cfg rT | ∃ r : rT, ρ = (⟨.lit (.real r), σ₁⟩ : Cfg rT)
          ∧ r ∈ ProbLangℝ.unifUnitSupport} := fun σ₁ => by
    rw [hrange σ₁]
    exact (hgemb σ₁).measurableSet_image.mpr ProbLangℝ.unifUnitSupportMeasurable
  have hSconc : ∀ σ₁ : State rT, Concentrated (primStep ⟨Exp.urand, σ₁⟩)
      {ρ : Cfg rT | ∃ r : rT, ρ = (⟨.lit (.real r), σ₁⟩ : Cfg rT)
          ∧ r ∈ ProbLangℝ.unifUnitSupport} := fun σ₁ => by
    rw [hps σ₁, hrange σ₁]
    exact concentratedOn_map (hg σ₁)
      ((hgemb σ₁).measurableSet_image.mpr ProbLangℝ.unifUnitSupportMeasurable)
      ProbLangℝ.unifUnitIsConcentrated
  iapply (wp_lift_atomic_step_concentrated (S := fun σ₁ =>
    {ρ : Cfg rT | ∃ r : rT, ρ = (⟨.lit (.real r), σ₁⟩ : Cfg rT)
      ∧ r ∈ ProbLangℝ.unifUnitSupport}) Hnv hSmeas hSconc)
  iintro %σ₁ Hσ
  imodintro
  isplitr
  · ipureintro
    exact reducible_of_headReducible (by is_lc) (hhead σ₁)
  iintro !> %e₂ %σ₂ %Hmem
  obtain ⟨r, heq, hr⟩ := Hmem
  cases heq
  imodintro
  simp only [approxisWpGS_stateInterp_eq, Exp.toVal?_lit]
  isplitl [Hσ]; · iexact Hσ
  iapply HΦ $$ %r
  ipureintro
  exact hr

end ProbLang
