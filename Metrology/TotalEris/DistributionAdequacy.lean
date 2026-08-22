module

public import Metrology.TotalEris.TotalAdequacy
public import Metrology.TotalEris.ErrorRules
public import Iris.Instances.Lib.WSat
public import Iris.Instances.Lib.LaterCredits
public import Iris.Instances.Lib.Invariants

/-!
# Distribution adequacy for TotalEris

If an expression `e` satisfies a *distribution* specification against a
probability measure `μ` on `ℝ` — a `twp_G2`-style triple which, for every
measurable `[0,1]`-bounded `F : ℝ → ℝ≥0∞`, gives

    ↯(∫⁻ y, F y ∂μ)  -∗  twp e {{ v. ↯(F (g v)) }}

where `g v` extracts a real out of the returned value `v` — then `e` is
distributed as `μ`: the pushforward of its limiting execution measure along `g`
equals `μ` (`twp_dist_adequacy'`).

The extraction `g` is an arbitrary *measurable* function `Exp ℝ → ℝ` of the
returned expression; it need **not** be an operation of the object language.
This matters for samplers like the continuous Gaussian, whose returned value is
a pair `(x, k)` (the object language has no real addition), while the sampled
real is `x + k`.

The argument instantiates `F` with the indicator of a complementary ray `Sᶜ`.
The residual credit `↯(𝟙_{Sᶜ}(g v))` collapses (via `↯1 ⊢ False`) to the pure
postcondition `⌜g v ∈ S⌝`, so total adequacy `twp_tgl` yields the lower bound
`μ S ≤ Pr[g(result) ∈ S]`. Applying this to `S` and `Sᶜ`, and using that the
execution measure is proper (total mass `1`), forces both lower bounds to
equalities — pinning the CDF of `g(result)` to that of `μ`.
`MeasureTheory.Measure.ext_of_Iic` upgrades CDF equality to measure equality.

`twp_dist_adequacy` is the special case where the value *is* a real literal and
`g` is the real projection `realOfExp`.
-/

@[expose] public section

open Iris Iris.Std Iris.BI Iris.ProofMode OFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal

namespace ProbLang
namespace TotalEris

variable {GF : BundledGFunctors}

/-! ## General distribution adequacy, parameterised by a real extraction `gExp` -/

section General

-- The (meta-level) real value extracted from a returned expression.
variable (gExp : Exp ℝ → ℝ)

/-- The set of configurations that have terminated at a value whose extracted
real `gExp v.fst` lies in `S`. This is exactly the set inside `Tgl _ (· ∈ S) _`. -/
def RSet' (S : Set ℝ) : Set (Cfg ℝ) :=
  {ρ : Cfg ℝ | ∃ v : Val ℝ, ρ.expr = Exp.ofVal v ∧ gExp v.fst ∈ S}

open MeasureTheory in
/-- A distribution specification of `e` against `μ` with extraction `gExp`: for
every measurable `[0,1]`-bounded `F`, the expected-value credit `↯(∫⁻ F dμ)`
proves a total triple returning a value `v` with residual credit `↯(F (gExp v.fst))`. -/
def IsDistSpec' (e : Exp ℝ) (μ : Measure ℝ) : Prop :=
  ∀ (F : ℝ → ℝ≥0∞), Measurable F → (∀ x, F x ≤ 1) →
    ∀ [ErisGS ℝ .hasNoLC GF], iprop(↯ (∫⁻ y, F y ∂μ)) ⊢@{IProp GF}
      tglWp ⊤ e (fun (v : Val ℝ) => iprop(↯ (F (gExp v.fst))))

variable {gExp}

theorem measurableSet_gExp_mem (hgExp : Measurable gExp) {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet {v : Val ℝ | gExp v.fst ∈ S} :=
  Val.fst.measurable (hgExp hS)

theorem measurableSet_RSet' (hgExp : Measurable gExp) {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet (RSet' gExp S) :=
  measurableSet_TglCfgSet (measurableSet_gExp_mem hgExp hS)

theorem RSet'_union (A B : Set ℝ) : RSet' gExp (A ∪ B) = RSet' gExp A ∪ RSet' gExp B := by
  ext ρ
  simp only [RSet', Set.mem_setOf_eq, Set.mem_union]
  grind

/-- `RSet' S = (gExp ∘ ·.expr)⁻¹'(S) ∩ {returns a value}`: on value configs the
config-level extraction `gExp ρ.expr` agrees with `gExp v.fst`. -/
theorem RSet'_eq_preimage (S : Set ℝ) :
    RSet' gExp S = (fun ρ : Cfg ℝ => gExp ρ.expr) ⁻¹' S ∩ RSet' gExp Set.univ := by
  ext ρ
  simp only [RSet', Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_univ, and_true]
  constructor
  · rintro ⟨v, he, hr⟩
    exact ⟨by rw [he]; exact hr, v, he⟩
  · rintro ⟨hmem, v, he⟩
    exact ⟨v, he, by rw [he] at hmem; exact hmem⟩

open MeasureTheory in
/-- **Ray instance.** Instantiating `IsDistSpec'` at `F = 𝟙_{Sᶜ}` and collapsing
the residual credit `↯(𝟙_{Sᶜ}(gExp v.fst))` via `↯1 ⊢ False` gives a pure total
triple: starting from `↯(μ Sᶜ)`, `e` terminates at a value with `gExp v.fst ∈ S`. -/
theorem ray_pure_wp' (e : Exp ℝ) (μ : Measure ℝ)
    (hspec : IsDistSpec' (GF := GF) gExp e μ) {S : Set ℝ} (hS : MeasurableSet S) :
    ∀ [ErisGS ℝ .hasNoLC GF], iprop(↯ (μ Sᶜ)) ⊢@{IProp GF}
      tglWp ⊤ e (fun (v : Val ℝ) => iprop(⌜gExp v.fst ∈ S⌝)) := by
  intro _
  iintro Hε
  iapply (ErisWpGS.tglWp_mono
    (Φ := fun (v : Val ℝ) => iprop(↯ (Sᶜ.indicator (fun _ => 1) (gExp v.fst)))) ?weak)
  case weak =>
    intro v
    iintro Hcr
    by_cases hr : gExp v.fst ∈ S
    · ipureintro; exact hr
    · iexfalso
      iapply ErrorCredit.contradict $$ Hcr
      simp [Set.indicator_of_mem (show gExp v.fst ∈ Sᶜ from hr)]
  iapply (hspec (Sᶜ.indicator (fun _ => 1)) (measurable_const.indicator hS.compl) ?le1)
  case le1 => intro x; by_cases hx : x ∈ Sᶜ <;> simp [Set.indicator, hx]
  rw [lintegral_indicator_const hS.compl, one_mul]
  iexact Hε

open MeasureTheory in
/-- **General distribution adequacy.** A distribution spec against a probability
measure `μ` on `ℝ`, with a measurable real extraction `gExp`, forces the limiting
execution of `e` to be distributed as `μ`: the pushforward of `limExec` along
`gExp ∘ (·.expr)` equals `μ`. -/
theorem twp_dist_adequacy' [AppPreGS ℝ GF] [ECPreGS GF] [InvGpreS GF]
    (hgExp : Measurable gExp) (e : Exp ℝ) (σ : State ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hspec : IsDistSpec' (GF := GF) gExp e μ) :
    (limExec ⟨e, σ⟩).map (fun ρ => gExp ρ.expr) = μ := by
  have hmg : Measurable (fun ρ : Cfg ℝ => gExp ρ.expr) := hgExp.comp Cfg.measurable_expr
  have hUniv_le : (limExec ⟨e, σ⟩) Set.univ ≤ 1 :=
    limExec_leq_mass (fun n => execN_univ_le_one n ⟨e, σ⟩)
  -- **Ray lower bound**: for any measurable `S`, `μ S ≤ Pr[gExp(result) ∈ S]`.
  have hlower : ∀ (S : Set ℝ), MeasurableSet S → μ S ≤ (limExec ⟨e, σ⟩) (RSet' gExp S) := by
    intro S hS
    have htgl : Tgl (limExec ⟨e, σ⟩) (fun v => gExp v.fst ∈ S) (μ Sᶜ) :=
      twp_tgl (σ := σ) (measurableSet_gExp_mem hgExp hS) (ray_pure_wp' e μ hspec hS)
    have hsum : μ S + μ Sᶜ = 1 := prob_add_prob_compl hS
    have hcompl : (1 : ℝ≥0∞) - μ Sᶜ = μ S := by
      rw [← hsum, ENNReal.add_sub_cancel_right (measure_ne_top _ _)]
    have h1 : 1 - μ Sᶜ ≤ (limExec ⟨e, σ⟩) (RSet' gExp S) := htgl
    rwa [hcompl] at h1
  have hRSetUniv1 : (limExec ⟨e, σ⟩) (RSet' gExp Set.univ) = 1 := by
    refine le_antisymm ((measure_mono (Set.subset_univ _)).trans hUniv_le) ?_
    have := hlower Set.univ MeasurableSet.univ
    rwa [measure_univ] at this
  -- **Pinning**: the complementary lower bounds are forced to equalities.
  have hpin : ∀ (S : Set ℝ), MeasurableSet S → (limExec ⟨e, σ⟩) (RSet' gExp S) = μ S := by
    intro S hS
    have hle1 := hlower S hS
    have hle2 := hlower Sᶜ hS.compl
    have hmeas2 : MeasurableSet (RSet' gExp Sᶜ) := measurableSet_RSet' hgExp hS.compl
    have hdisj : Disjoint (RSet' gExp S) (RSet' gExp Sᶜ) := by
      rw [Set.disjoint_left]
      rintro ρ ⟨v, he, hs⟩ ⟨v', he', hs'⟩
      exact (show gExp ρ.expr ∈ Sᶜ by rw [he']; exact hs') (by rw [he]; exact hs)
    have hunion : RSet' gExp S ∪ RSet' gExp Sᶜ = RSet' gExp Set.univ := by
      rw [← RSet'_union, Set.union_compl_self]
    have hsum_lim : (limExec ⟨e, σ⟩) (RSet' gExp S) + (limExec ⟨e, σ⟩) (RSet' gExp Sᶜ)
        = (limExec ⟨e, σ⟩) (RSet' gExp Set.univ) := by
      rw [← measure_union hdisj hmeas2, hunion]
    have hsum_one : (limExec ⟨e, σ⟩) (RSet' gExp S) + (limExec ⟨e, σ⟩) (RSet' gExp Sᶜ) = 1 := by
      rw [hsum_lim, hRSetUniv1]
    have hy_ne : (limExec ⟨e, σ⟩) (RSet' gExp Sᶜ) ≠ (⊤ : ℝ≥0∞) :=
      ne_top_of_le_ne_top ENNReal.one_ne_top ((measure_mono (Set.subset_univ _)).trans hUniv_le)
    have hμsum : μ S + μ Sᶜ = 1 := prob_add_prob_compl hS
    have hx_le : (limExec ⟨e, σ⟩) (RSet' gExp S) ≤ μ S := by
      have hsum_le : (limExec ⟨e, σ⟩) (RSet' gExp S) + (limExec ⟨e, σ⟩) (RSet' gExp Sᶜ)
          ≤ μ S + (limExec ⟨e, σ⟩) (RSet' gExp Sᶜ) := by
        rw [hsum_one]
        calc (1 : ℝ≥0∞) = μ S + μ Sᶜ := hμsum.symm
          _ ≤ μ S + (limExec ⟨e, σ⟩) (RSet' gExp Sᶜ) := by gcongr
      exact (ENNReal.add_le_add_iff_right hy_ne).mp hsum_le
    exact le_antisymm hx_le hle1
  -- The execution measure is proper.
  haveI hprob : IsProbabilityMeasure (limExec ⟨e, σ⟩) := by
    refine ⟨le_antisymm hUniv_le ?_⟩
    calc (1 : ℝ≥0∞) = (limExec ⟨e, σ⟩) (RSet' gExp Set.univ) := hRSetUniv1.symm
      _ ≤ (limExec ⟨e, σ⟩) Set.univ := measure_mono (Set.subset_univ _)
  -- The non-returning configs are null.
  have hnull : (limExec ⟨e, σ⟩) (RSet' gExp Set.univ)ᶜ = 0 := by
    rw [measure_compl (measurableSet_RSet' hgExp MeasurableSet.univ) (measure_ne_top _ _),
      measure_univ, hRSetUniv1, tsub_self]
  -- Intersecting with the conull "returns a value" set is measure-preserving.
  have hconull : ∀ (A : Set ℝ),
      (limExec ⟨e, σ⟩) ((fun ρ => gExp ρ.expr) ⁻¹' A ∩ RSet' gExp Set.univ)
        = (limExec ⟨e, σ⟩) ((fun ρ => gExp ρ.expr) ⁻¹' A) := by
    intro A
    refine le_antisymm (measure_mono Set.inter_subset_left) ?_
    set P := (fun ρ : Cfg ℝ => gExp ρ.expr) ⁻¹' A
    have hsub : P ⊆ (P ∩ RSet' gExp Set.univ) ∪ (P ∩ (RSet' gExp Set.univ)ᶜ) := by
      simp [← Set.inter_union_distrib_left]
    calc (limExec ⟨e, σ⟩) P
        ≤ (limExec ⟨e, σ⟩) ((P ∩ RSet' gExp Set.univ) ∪ (P ∩ (RSet' gExp Set.univ)ᶜ)) :=
          measure_mono hsub
      _ ≤ (limExec ⟨e, σ⟩) (P ∩ RSet' gExp Set.univ)
            + (limExec ⟨e, σ⟩) (P ∩ (RSet' gExp Set.univ)ᶜ) := measure_union_le _ _
      _ = (limExec ⟨e, σ⟩) (P ∩ RSet' gExp Set.univ) := by
          rw [measure_mono_null Set.inter_subset_right hnull, add_zero]
  -- CDF equality of the pushforward and `μ`.
  have hIic : ∀ b : ℝ,
      ((limExec ⟨e, σ⟩).map (fun ρ => gExp ρ.expr)) (Set.Iic b) = μ (Set.Iic b) := by
    intro b
    rw [Measure.map_apply hmg measurableSet_Iic, ← hconull (Set.Iic b), ← RSet'_eq_preimage]
    exact hpin (Set.Iic b) measurableSet_Iic
  haveI : IsProbabilityMeasure ((limExec ⟨e, σ⟩).map (fun ρ => gExp ρ.expr)) :=
    Measure.isProbabilityMeasure_map hmg.aemeasurable
  exact Measure.ext_of_Iic _ _ hIic

end General

/-! ## Bare-real special case

The real projection `realOfExp : Exp ℝ → ℝ` reads the payload of a real literal
(junk `0` otherwise). When the sampler returns a real literal directly, this is
the natural extraction. -/

/-- The real-literal embedding `r ↦ .lit (.real r)` into expressions. -/
def realEmb : ℝ → Exp ℝ := fun r => Exp.lit (.real r)

open MeasureTheory in
theorem measurableEmbedding_realEmb : MeasurableEmbedding realEmb :=
  Exp.lit.measurableEmbedding.comp BaseLit.real.measurableEmbedding

/-- Extract the real payload of an expression (junk `0` off the real literals),
as a measurable extension of the identity along `realEmb`. -/
noncomputable def realOfExp : Exp ℝ → ℝ := Function.extend realEmb id (fun _ => 0)

open MeasureTheory in
theorem measurable_realOfExp : Measurable realOfExp :=
  measurableEmbedding_realEmb.measurable_extend measurable_id measurable_const

@[simp]
theorem realOfExp_real (r : ℝ) : realOfExp (Exp.lit (.real r)) = r := by
  show Function.extend realEmb id (fun _ => 0) (realEmb r) = r
  rw [measurableEmbedding_realEmb.injective.extend_apply]; rfl

open MeasureTheory in
/-- **Distribution adequacy (bare-real case).** If `e`'s returned value is a real
literal `.real r` carrying credit `↯(F r)`, `e` is distributed as `μ`. -/
theorem twp_dist_adequacy [AppPreGS ℝ GF] [ECPreGS GF] [InvGpreS GF]
    (e : Exp ℝ) (σ : State ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hspec : IsDistSpec' (GF := GF) realOfExp e μ) :
    (limExec ⟨e, σ⟩).map (fun ρ => realOfExp ρ.expr) = μ :=
  twp_dist_adequacy' measurable_realOfExp e σ μ hspec

end TotalEris
end ProbLang
