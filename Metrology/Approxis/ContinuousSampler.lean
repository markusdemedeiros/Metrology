module

public import Metrology.Approxis.PrimitiveLaws
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Approxis.CouplingRules
public import Metrology.Approxis.AppRelRules

@[expose] public section

/-!
# Continuous sampler rules

WP rules for ProbLang's *diffuse* sampler `urand`, which lies outside the
discrete fragment: `unifUnit` may have no atoms, so every atom-based step rule
(`wp_lift_atomic_step`, `wp_lift_atomic_head_step`, …) is vacuous for it.

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

variable {rT : Type _} [ProbLang.ProbLangℝ rT]

/-! ## The real-literal injection

`urand` steps to `Cfg.uniformReal σ`, the pushforward of `unifUnit` along the
real-literal injection `r ↦ ⟨#(.real r), σ⟩`. Both rules below need that
injection to be a measurable embedding, and need its image of `unifUnitSupport`
to be the measurable set the step measure lives on. -/

theorem Cfg.measurable_realLit (σ : State rT) :
    Measurable (fun r : rT => (⟨pl(#(.real r)), σ⟩ : Cfg rT)) :=
  Cfg.measurable_iff.mpr ⟨Exp.lit.measurable.comp BaseLit.real.measurable, measurable_const⟩

-- Definitionally `Cfg.measurableEquivProd.symm ∘ (·, σ) ∘ Exp.lit ∘ BaseLit.real`,
-- so it inherits `MeasurableEmbedding` from those four.
theorem Cfg.measurableEmbedding_realLit (σ : State rT) :
    MeasurableEmbedding (fun r : rT => (⟨pl(#(.real r)), σ⟩ : Cfg rT)) :=
  Cfg.measurableEquivProd.symm.measurableEmbedding.comp
    ((measurableEmbedding_prod_mk_right σ).comp
      (Exp.lit.measurableEmbedding.comp BaseLit.real.measurableEmbedding))

theorem Cfg.realLit_image_eq (σ : State rT) :
    {ρ : Cfg rT | ∃ r : rT, ρ = (⟨pl(#(.real r)), σ⟩ : Cfg rT) ∧ r ∈ ProbLangℝ.unifUnitSupport}
      = (fun r : rT => (⟨pl(#(.real r)), σ⟩ : Cfg rT)) '' ProbLangℝ.unifUnitSupport := by
  ext ρ
  simp only [Set.mem_image, Set.mem_setOf_eq]
  exact ⟨fun ⟨r, h, hr⟩ => ⟨r, hr, h.symm⟩, fun ⟨r, hr, h⟩ => ⟨r, h.symm, hr⟩⟩

theorem Cfg.measurableSet_realLit_image (σ : State rT) :
    MeasurableSet {ρ : Cfg rT | ∃ r : rT, ρ = (⟨pl(#(.real r)), σ⟩ : Cfg rT)
      ∧ r ∈ ProbLangℝ.unifUnitSupport} := by
  rw [Cfg.realLit_image_eq]
  exact (Cfg.measurableEmbedding_realLit σ).measurableSet_image.mpr
    ProbLangℝ.unifUnitSupportMeasurable

theorem headReducible_urand (σ : State rT) : HeadReducible (pl(urand) : Exp rT) σ :=
  show Cfg.uniformReal σ ≠ 0 from MeasureTheory.IsProbabilityMeasure.ne_zero _

theorem reducible_urand (σ : State rT) : Reducible (pl(urand) : Exp rT) σ :=
  reducible_of_headReducible (by is_lc) (headReducible_urand σ)

theorem primStep_urand (σ : State rT) :
    primStep (⟨pl(urand), σ⟩ : Cfg rT) = Cfg.uniformReal σ :=
  primStep_eq_headStep
    (Exp.decompItem_none_of_lc_headReducible (by is_lc) (headReducible_urand σ))

/-- `urand`'s step measure lives on the real-literal image: this is what replaces
"lands on an atom" for the diffuse sampler. -/
theorem Cfg.concentrated_primStep_urand (σ : State rT) :
    Concentrated (primStep (⟨pl(urand), σ⟩ : Cfg rT))
      {ρ : Cfg rT | ∃ r : rT, ρ = (⟨pl(#(.real r)), σ⟩ : Cfg rT)
        ∧ r ∈ ProbLangℝ.unifUnitSupport} := by
  rw [primStep_urand σ, Cfg.uniformReal, Cfg.realLit_image_eq]
  exact concentratedOn_map (Cfg.measurable_realLit σ)
    ((Cfg.measurableEmbedding_realLit σ).measurableSet_image.mpr
      ProbLangℝ.unifUnitSupportMeasurable)
    ProbLangℝ.unifUnitIsConcentrated

section Unary
variable {hlc : HasLC} {GF : BundledGFunctors} [ApproxisGS rT hlc GF]

/-- **`wp_urand` — a WP rule for the continuous sampler.**

This is the payoff of the `_concentrated` generalization: `urand` samples from a
*diffuse* measure, so it has no atoms and every atom-based step rule is vacuous
for it. Here the carrying set is the real-literal image
`{⟨pl(#(.real r)), σ₁⟩ | r ∈ unifUnitSupport}`, which `primStep ⟨urand, σ₁⟩`
lives on by `concentratedOn_map`, and which is measurable because the injection
`r ↦ ⟨pl(#(.real r)), σ₁⟩` is a `MeasurableEmbedding`.

Note the absence of `[Countable rT]`: the whole point is that this rule holds for
a diffuse `rT`. Follows the same shape as `TotalEris.twp_urand_exp`, minus the
error credits (a plain atomic lift spends none). -/
theorem wp_urand {E : CoPset} {Φ : Val rT → IProp GF} :
    iprop(▷ ∀ (r : rT), (⌜r ∈ ProbLangℝ.unifUnitSupport⌝) -∗ Φ (.real r : Val rT))
      ⊢@{IProp GF} wp E pl(urand) Φ := by
  iintro HΦ
  iapply (wp_lift_atomic_step_concentrated
    (S := fun σ => {ρ : Cfg rT | ∃ r : rT, ρ = (⟨pl(#(.real r)), σ⟩ : Cfg rT)
      ∧ r ∈ ProbLangℝ.unifUnitSupport})
    Exp.urand_toVal?_eq_none Cfg.measurableSet_realLit_image Cfg.concentrated_primStep_urand)
  iintro %σ₁ Hσ !>
  isplitr
  · ipureintro; exact reducible_urand σ₁
  iintro !> %e₂ %σ₂ %Hmem
  obtain ⟨r, heq, hr⟩ := Hmem
  cases heq
  imodintro
  simp only [Exp.toVal?_lit]
  iframe Hσ
  iapply HΦ $$ %r %hr

/-! ## Relational coupling of two continuous samplers

`wp_urand` is unary-flavoured: it says what a single `urand` produces. Approxis is
a *relational* logic, so continuous refinement needs a way to couple two `urand`s.

The discrete analogue (`Cfg.uniform_addCoupl_bij`) gets its bijection for free —
a bijection of a finite set preserves counting measure, so the proof is a
`Finset.sum_bij` reindexing. The continuous version needs a genuine hypothesis:
`f` must be **measure-preserving** for `unifUnit`. Given that, the reindexing is
`MeasurePreserving.lintegral_comp`, and the proof is actually shorter. -/

/-- Continuous-uniform coupling under a measure-preserving map: `Cfg.uniformReal σ`
and `Cfg.uniformReal σ'` are exactly coupled (at error `0`) along
`{(⟨#r, σ⟩, ⟨#(f r), σ'⟩) | r}`.

Countability-free analogue of `Cfg.uniform_addCoupl_bij`. Note `f` need not be a
bijection on the nose — measure preservation is exactly what the argument uses. -/
theorem Cfg.uniformReal_addCoupl_bij (σ σ' : State rT) (f : rT → rT)
    (hmp : MeasureTheory.MeasurePreserving f
      (ProbLangℝ.unifUnit (T := rT)) (ProbLangℝ.unifUnit (T := rT))) :
    AddCoupl 0
      {p : Cfg rT × Cfg rT | ∃ r : rT, r ∈ ProbLangℝ.unifUnitSupport ∧
        p.1 = (⟨pl(#(.real r)), σ⟩ : Cfg rT) ∧ p.2 = (⟨pl(#(.real (f r))), σ'⟩ : Cfg rT)}
      (Cfg.uniformReal σ) (Cfg.uniformReal σ') := by
  rintro ⟨φ, Hφm, Hφb⟩ ⟨ψ, Hψm, Hψb⟩ Hle
  simp only [add_zero]
  show ∫⁻ c, φ c ∂(Cfg.uniformReal σ) ≤ ∫⁻ c, ψ c ∂(Cfg.uniformReal σ')
  rw [Cfg.uniformReal, Cfg.uniformReal,
      MeasureTheory.lintegral_map Hφm (Cfg.measurable_realLit σ),
      MeasureTheory.lintegral_map Hψm (Cfg.measurable_realLit σ')]
  -- Reindex the RHS along `f`; this is where measure preservation is spent.
  have hψ' : Measurable (fun r : rT => ψ (⟨pl(#(.real r)), σ'⟩ : Cfg rT)) :=
    Hψm.comp (Cfg.measurable_realLit σ')
  rw [← hmp.lintegral_comp hψ']
  -- `unifUnit` lives on its support, so the pointwise bound is only needed there.
  have hae : ∀ᵐ r ∂(ProbLangℝ.unifUnit (T := rT)), r ∈ ProbLangℝ.unifUnitSupport :=
    MeasureTheory.ae_iff.mpr ProbLangℝ.unifUnitIsConcentrated
  refine MeasureTheory.lintegral_mono_ae ?_
  filter_upwards [hae] with r hr
  exact Hle ⟨r, hr, rfl, rfl⟩

/-- **`wp_couple_urand_urand`** — couple the program's `urand` against the spec's
`urand` along a measure-preserving `f`. The continuous analogue of
`wp_couple_rand_rand`, and the rule that makes continuous *refinement* expressible. -/
theorem wp_couple_urand_urand (f : rT → rT)
    (hmp : MeasureTheory.MeasurePreserving f
      (ProbLangℝ.unifUnit (T := rT)) (ProbLangℝ.unifUnit (T := rT)))
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) :
    iprop((⤇ K.fill pl(urand)) ∗
        (∀ (r : rT), (⌜r ∈ ProbLangℝ.unifUnitSupport⌝) -∗
          (⤇ K.fill (pl(#(.real (f r))))) -∗ Φ (.real r : Val rT)))
      ⊢@{IProp GF} wp E pl(urand) Φ := by
  iintro ⟨Hj, Hcnt⟩
  iapply (wp_lift_prim_steps_coupl Exp.urand_toVal?_eq_none)
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree $$ Hs Hj
  subst Heq
  imod (BIFUpdate.subset Std.LawfulSet.empty_subset) with Hclose
  imodintro
  let R : Cfg rT → Cfg rT → Prop := fun c₁ c₂ =>
    ∃ r : rT, r ∈ ProbLangℝ.unifUnitSupport
      ∧ c₁ = (⟨pl(#(.real r)), σ₁⟩ : Cfg rT)
      ∧ c₂ = (⟨K.fill (pl(#(.real (f r)))), σ₁'⟩ : Cfg rT)
  iexists R, 0, ε
  isplitr; · ipureintro; rw [zero_add]
  isplitr; · ipureintro; exact reducible_urand σ₁
  isplitr; · ipureintro; exact Reducible.fill K (reducible_urand σ₁')
  isplitr
  · ipureintro
    rw [primStep_urand σ₁, primStep_fill Exp.urand_not_isValue, primStep_urand σ₁']
    have hKm : Measurable (fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT)) := by
      measurability
    have hmap : AddCoupl 0 {p : Cfg rT × Cfg rT | R p.1 p.2}
        ((Cfg.uniformReal σ₁).map id)
        ((Cfg.uniformReal σ₁').map (fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT))) :=
      AddCoupl.map _ _ measurable_id hKm (by rintro a b ⟨r, hr, rfl, rfl⟩; exact ⟨r, hr, rfl, rfl⟩)
        (Cfg.uniformReal_addCoupl_bij σ₁ σ₁' f hmp)
    rwa [MeasureTheory.Measure.map_id] at hmap
  iintro %e₂ %σ₂ %e₂' %σ₂' %HR
  obtain ⟨r, hrsupp, heq1, heq2⟩ := HR
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq2
  iintro !> !>
  imod specProg_update
    (e3 := K.fill (pl(#(.real (f r))))) $$ Hs Hj with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  iframe Hσ Hs' Hε
  iapply (wp_value_of_toVal rfl)
  iapply Hcnt $$ %r %hrsupp Hj'

end Unary

/-! ## The relational rule

`wp_couple_urand_urand` lifted to `refines`, mirroring `refines_couple_rands_lr`.
This is the rule a continuous refinement proof actually applies. -/

section Relational
variable {hlc : HasLC} {GF : BundledGFunctors} [IR : ApproxisRGS rT hlc GF]

/-- **`refines_couple_urands_lr`** — couple the two sides' `urand` samples along a
measure-preserving `f`, then continue with the sampled values related by `f`.

Continuous analogue of `refines_couple_rands_lr`. Note there is no
`⌜0 ≤ n ∧ n < z⌝` side condition: the continuous sampler's range constraint is
carried by `f`'s measure preservation instead. -/
theorem refines_couple_urands_lr {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF}
    (f : rT → rT)
    (hmp : MeasureTheory.MeasurePreserving f
      (ProbLangℝ.unifUnit (T := rT)) (ProbLangℝ.unifUnit (T := rT))) :
    iprop(∀ (r : rT), (⌜r ∈ ProbLangℝ.unifUnitSupport⌝) -∗
            refines E (K.fill pl(#(.real r))) (K'.fill (pl(#(.real (f r))))) A)
      ⊢@{IProp GF}
        refines E (K.fill pl(urand)) (K'.fill pl(urand)) A := by
  iintro Hcnt
  unfold refines
  iintro %K2 %ε Hj Hna Herr Hpos
  ihave Hj' : iprop(⤇ (K2.comp K').fill (pl(urand) : Exp rT)) $$ [Hj]
  · rw [← Ectx.fill_comp]; iexact Hj
  iapply ApproxisWpGS.wp_bind
  iapply (wp_couple_urand_urand f hmp (K2.comp K') ⊤
    (fun v => wp ⊤ (K.fill (Exp.ofVal v))
      (fun v => iprop(∃ v' ε',
        (⤇ K2.fill v'.1) ∗ naOwnP ⊤ ∗ (↯ ε') ∗ (⌜(0 : ENNReal) < ε'⌝) ∗ A.car v v'))))
  iframe Hj'
  iintro %r %hrsupp HKres
  ihave HKres' : iprop(⤇ K2.fill (K'.fill (pl(#(.real (f r))) : Exp rT))) $$ [HKres]
  · rw [Ectx.fill_comp]; iexact HKres
  ispecialize Hcnt $$ %r %hrsupp
  -- `iapply` matches syntactically, so the `Exp.ofVal`/literal defeq must be rewritten away.
  rw [show Exp.ofVal (.real r : Val rT) = pl(#(.real r)) from rfl]
  iapply Hcnt $$ %K2 %ε HKres' Hna Herr Hpos

end Relational

end ProbLang
