module

public import Metrology.Approxis.PrimitiveLaws
public import Metrology.Approxis.CouplingRules
public import Metrology.Approxis.AppRelRules

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

section Unary
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
        p.1 = (⟨.lit (.real r), σ⟩ : Cfg rT) ∧ p.2 = (⟨.lit (.real (f r)), σ'⟩ : Cfg rT)}
      (Cfg.uniformReal σ) (Cfg.uniformReal σ') := by
  classical
  have hg : ∀ τ : State rT, Measurable (fun r : rT => (⟨.lit (.real r), τ⟩ : Cfg rT)) :=
    fun τ => Cfg.measurable_iff.mpr
      ⟨Exp.lit.measurable.comp BaseLit.real.measurable, measurable_const⟩
  rintro ⟨φ, Hφm, Hφb⟩ ⟨ψ, Hψm, Hψb⟩ Hle
  simp only [add_zero]
  show ∫⁻ c, φ c ∂(Cfg.uniformReal σ) ≤ ∫⁻ c, ψ c ∂(Cfg.uniformReal σ')
  rw [Cfg.uniformReal, Cfg.uniformReal,
      MeasureTheory.lintegral_map Hφm (hg σ),
      MeasureTheory.lintegral_map Hψm (hg σ')]
  -- Reindex the RHS along `f`; this is where measure preservation is spent.
  have hψ' : Measurable (fun r : rT => ψ (⟨.lit (.real r), σ'⟩ : Cfg rT)) :=
    Hψm.comp (hg σ')
  rw [← hmp.lintegral_comp hψ']
  -- `unifUnit` lives on its support, so the pointwise bound is only needed there.
  have hae : ∀ᵐ r ∂(ProbLangℝ.unifUnit (T := rT)), r ∈ ProbLangℝ.unifUnitSupport := by
    rw [MeasureTheory.ae_iff]
    exact ProbLangℝ.unifUnitIsConcentrated
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
    iprop((⤇ K.fill Exp.urand) ∗
        (∀ (r : rT), (⌜r ∈ ProbLangℝ.unifUnitSupport⌝) -∗
          (⤇ K.fill (.lit (.real (f r)))) -∗ Φ (.real r : Val rT)))
      ⊢@{IProp GF} wp E Exp.urand Φ := by
  iintro ⟨Hj, Hcnt⟩
  have Hv : (Exp.urand : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  have Hnval : ¬ (Exp.urand : Exp rT).isValue := fun ⟨w⟩ => nomatch w
  have hhead : ∀ τ : State rT, HeadReducible (Exp.urand : Exp rT) τ :=
    fun τ => show Cfg.uniformReal τ ≠ 0 from MeasureTheory.IsProbabilityMeasure.ne_zero _
  have hps : ∀ τ : State rT, primStep (⟨Exp.urand, τ⟩ : Cfg rT) = Cfg.uniformReal τ :=
    fun τ => primStep_eq_headStep
      (Exp.decompItem_none_of_lc_headReducible (by is_lc) (hhead τ))
  have hred : ∀ τ : State rT, Reducible (Exp.urand : Exp rT) τ :=
    fun τ => reducible_of_headReducible (by is_lc) (hhead τ)
  iapply (wp_lift_prim_steps_coupl Hv)
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  let R : Cfg rT → Cfg rT → Prop := fun c₁ c₂ =>
    ∃ r : rT, r ∈ ProbLangℝ.unifUnitSupport
      ∧ c₁ = (⟨.lit (.real r), σ₁⟩ : Cfg rT)
      ∧ c₂ = (⟨K.fill (.lit (.real (f r))), σ₁'⟩ : Cfg rT)
  iexists R, 0, ε
  isplitr; · ipureintro; rw [zero_add]
  isplitr; · ipureintro; exact hred σ₁
  isplitr; · ipureintro; exact Reducible.fill K (hred σ₁')
  isplitr
  · ipureintro
    rw [hps σ₁, primStep_fill Hnval, hps σ₁']
    have Hbase := Cfg.uniformReal_addCoupl_bij σ₁ σ₁' f hmp
    have hKm : Measurable (fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT)) := by
      measurability
    have hmap : AddCoupl 0
        {p : Cfg rT × Cfg rT | R p.1 p.2}
        ((Cfg.uniformReal σ₁).map id)
        ((Cfg.uniformReal σ₁').map (fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT))) := by
      refine AddCoupl.map (f := id)
        (g := fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT))
        measurable_id hKm ?_ Hbase
      rintro a b ⟨r, hr, rfl, rfl⟩
      exact ⟨r, hr, rfl, rfl⟩
    rw [MeasureTheory.Measure.map_id] at hmap
    exact hmap
  iintro %e₂ %σ₂ %e₂' %σ₂' %HR
  obtain ⟨r, hrsupp, heq1, heq2⟩ := HR
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq2
  imodintro
  iintro !>
  ihave HUpd := specProg_update (GF := GF)
    (e3 := K.fill (.lit (.real (f r)))) $$ Hs Hj
  imod HUpd with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  isplitl [Hσ]; · iexact Hσ
  isplitl [Hs']; · iexact Hs'
  isplitl [Hε]; · iexact Hε
  iapply (wp_value_of_toVal (v := (.real r : Val rT)) rfl)
  iapply Hcnt $$ %r %hrsupp
  iexact Hj'

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
            refines E (K.fill (.lit (.real r))) (K'.fill (.lit (.real (f r)))) A)
      ⊢@{IProp GF}
        refines E (K.fill Exp.urand) (K'.fill Exp.urand) A := by
  iintro Hcnt
  unfold refines
  iintro %K2 %ε Hj Hna Herr Hpos
  have hfc : K2.fill (K'.fill (Exp.urand : Exp rT)) =
      (K2.comp K').fill (Exp.urand : Exp rT) := Ectx.fill_comp K2 K' _
  ihave Hj' : iprop(⤇ (K2.comp K').fill (Exp.urand : Exp rT)) $$ [Hj]
  · rw [← hfc]; iexact Hj
  iapply ApproxisWpGS.wp_bind (K := K)
  iapply (wp_couple_urand_urand f hmp (K2.comp K') ⊤
    (fun v => wp ⊤ (K.fill (Exp.ofVal v))
      (fun v => iprop(∃ v' ε',
        (⤇ K2.fill v'.1) ∗ naOwnP ⊤ ∗ (↯ ε') ∗ (⌜(0 : ENNReal) < ε'⌝) ∗ A.car v v'))))
  isplitl [Hj']; · iexact Hj'
  iintro %r %hrsupp HKres
  have hfcN : K2.fill (K'.fill (Exp.lit (.real (f r)) : Exp rT)) =
      (K2.comp K').fill (Exp.lit (.real (f r)) : Exp rT) := Ectx.fill_comp K2 K' _
  ihave HKres' : iprop(⤇ K2.fill (K'.fill (.lit (.real (f r)) : Exp rT))) $$ [HKres]
  · rw [hfcN]; iexact HKres
  ispecialize Hcnt $$ %r %hrsupp
  have hfillN : Exp.ofVal (.real r : Val rT) = Exp.lit (.real r) := rfl
  rw [hfillN]
  iapply Hcnt $$ %K2 %ε HKres' Hna Herr Hpos

/-! ### Countability-free RHS stepping

The spec side steps through `step_pure`, which bottoms out in
`pexecN_of_PureExec` — gated on `Countable rT` only because it routes through
`DetExec_discrete`. On the measure-theoretic `PureStep` the same induction goes
through directly, via the already-continuous `pexecN_1_of_DetStep_cts`. -/

/-- `pexecN n ⟨e1,σ⟩ = dirac ⟨e2,σ⟩` for a `PureExec`, countability-free. -/
theorem pexecN_of_PureExec_cts {φ : Prop} {n : ℕ} {e1 e2 : Exp rT}
    [h : PureExec φ n e1 e2] (σ : State rT) (hφ : φ) :
    pexecN n (⟨e1, σ⟩ : Cfg rT) = MeasureTheory.Measure.dirac ⟨e2, σ⟩ := by
  have hs := h.pure_exec hφ
  clear h
  induction n generalizing e1 with
  | zero => simp only [nsteps] at hs; subst hs; rfl
  | succ k ih =>
    obtain ⟨c, hstep, hrest⟩ := hs
    rw [show k + 1 = 1 + k from Nat.add_comm _ _, pexecN_plus,
        pexecN_1_of_DetStep_cts (ρ' := (⟨c, σ⟩ : Cfg rT)) ⟨hstep.safe σ, hstep.det σ⟩,
        MeasureTheory.Measure.dirac_bind pexecN_measurable, ih hrest]

/-- `step_pure` on `PureExec`, countability-free. -/
theorem step_pure' {E : CoPset} (K : Ectx rT) {e e' : Exp rT} {φ : Prop} {n : ℕ}
    (Hφ : φ) [Hex : PureExec φ n e e'] :
    iprop(⤇ (K.fill e)) ⊢@{IProp GF} specUpdate rT E iprop(⤇ (K.fill e')) := by
  have HexK : PureExec φ n (K.fill e) (K.fill e') := PureExec.fill K
  iintro HK
  unfold specUpdate
  iintro %ρ Hρ
  obtain ⟨_, σ⟩ := ρ
  ihave %Heq := specAuth_specFrag_agree (GF := GF) $$ Hρ HK
  subst Heq
  imod specProg_update $$ Hρ HK with ⟨HρNew, HKNew⟩
  imodintro
  iexists (⟨K.fill e', σ⟩ : Cfg rT), n
  isplitr
  · ipureintro; exact pexecN_of_PureExec_cts (h := HexK) σ Hφ
  isplitl [HρNew] <;> iassumption

/-- `refines_pure_l'` — LHS pure step, countability-free.

Copy of `refines_pure_l` on the measure-theoretic `PureExec` rather than
`PureExec_discrete`, so it applies at a diffuse `rT` (where `PureExec.toDiscrete`
is unavailable because `ℝ` is not countable). -/
theorem refines_pure_l' {E : CoPset} {K : Ectx rT} {e e' t : Exp rT} {A : lrel rT GF}
    {φ : Prop} {n : ℕ} [Hex : PureExec φ n e e'] (Hφ : φ) :
    Nat.repeat (fun Q : IProp GF => iprop(▷ Q)) n (refines E (K.fill e') t A)
      ⊢@{IProp GF} refines E (K.fill e) t A := by
  have HexK : PureExec φ n (K.fill e) (K.fill e') := PureExec.fill K
  unfold refines
  iintro H
  iintro %K' %ε HK Hna Herr Hpos
  iapply (wp_pure_step_later' (Hex := HexK) Hφ)
  ihave H0 : iprop(▷^[n] (∀ (K₂ : Ectx rT) (ε₂ : ENNReal),
      (⤇ K₂.fill t) -∗ (naOwnP E) -∗ (↯ ε₂) -∗ (⌜(0 : ENNReal) < ε₂⌝) -∗
      wp ⊤ (K.fill e') (fun v => iprop(∃ v' ε',
        (⤇ K₂.fill v'.1) ∗ naOwnP ⊤ ∗ (↯ ε') ∗ (⌜(0 : ENNReal) < ε'⌝) ∗ A.car v v')))) $$ [H]
  · rw [← nat_repeat_later_eq_laterN]; iexact H
  rw [nat_repeat_later_eq_laterN]
  ihave H1 := (BI.laterN_forall n).mp $$ H0
  ispecialize H1 $$ %K'
  ihave H2 := (BI.laterN_forall n).mp $$ H1
  ispecialize H2 $$ %ε
  ihave H3 := BI.laterN_wand n $$ H2
  ihave HKLater : iprop(▷^[n] (⤇ K'.fill t)) $$ [HK]
  · iapply BI.laterN_intro n; iexact HK
  ispecialize H3 $$ HKLater
  ihave H4 := BI.laterN_wand n $$ H3
  ihave HnaLater : iprop(▷^[n] naOwnP E) $$ [Hna]
  · iapply BI.laterN_intro n; iexact Hna
  ispecialize H4 $$ HnaLater
  ihave H5 := BI.laterN_wand n $$ H4
  ihave HerrLater : iprop(▷^[n] (↯ ε)) $$ [Herr]
  · iapply BI.laterN_intro n; iexact Herr
  ispecialize H5 $$ HerrLater
  ihave H6 := BI.laterN_wand n $$ H5
  ihave HposLater : iprop(▷^[n] ⌜(0 : ENNReal) < ε⌝) $$ [Hpos]
  · iapply BI.laterN_intro n; iexact Hpos
  ispecialize H6 $$ HposLater
  iexact H6

/-- `refines_pure_r'` — RHS pure step, countability-free. -/
theorem refines_pure_r' {E : CoPset} {K : Ectx rT} {e e' t : Exp rT} {A : lrel rT GF}
    {φ : Prop} {n : ℕ} [Hex : PureExec φ n e e'] (Hφ : φ) :
    refines E t (K.fill e') A ⊢@{IProp GF} refines E t (K.fill e) A := by
  unfold refines
  iintro H
  iintro %K' %ε Hj Hna Herr Hpos
  have hfc : K'.fill (K.fill e) = (K'.comp K).fill e := Ectx.fill_comp K' K e
  have hfc' : K'.fill (K.fill e') = (K'.comp K).fill e' := Ectx.fill_comp K' K e'
  rw [hfc]
  ihave HStep := step_pure' (E := ⊤) (K'.comp K) (Hex := Hex) Hφ $$ Hj
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤) (E2 := ⊤) Std.LawfulSet.subset_refl)
  isplitl [HStep]; · iexact HStep
  iintro HK'
  ihave HK'' : iprop(⤇ K'.fill (K.fill e')) $$ [HK']
  · rw [hfc']; iexact HK'
  iapply specUpdate_ret
  iapply H $$ %K' %ε HK'' Hna Herr Hpos

end Relational

end ProbLang
