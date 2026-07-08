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
equals `μ` (`twp_dist_adequacyG`).

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

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS MeasureTheory HeapView Auth
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
def RSetG (S : Set ℝ) : Set (Cfg ℝ) :=
  {ρ : Cfg ℝ | ∃ v : Val ℝ, ρ.expr = Exp.ofVal v ∧ gExp v.fst ∈ S}

/-- A distribution specification of `e` against `μ` with extraction `gExp`: for
every measurable `[0,1]`-bounded `F`, the expected-value credit `↯(∫⁻ F dμ)`
proves a total triple returning a value `v` with residual credit `↯(F (gExp v.fst))`. -/
def IsDistSpecG (e : Exp ℝ) (μ : Measure ℝ) : Prop :=
  ∀ (F : ℝ → ℝ≥0∞), Measurable F → (∀ x, F x ≤ 1) →
    ∀ [ErisGS ℝ .hasNoLC GF], iprop(↯ (∫⁻ y, F y ∂μ)) ⊢@{IProp GF}
      tglWp ⊤ e (fun (v : Val ℝ) => iprop(↯ (F (gExp v.fst))))

variable {gExp}

theorem measurableSet_φG (hgExp : Measurable gExp) {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet {v : Val ℝ | gExp v.fst ∈ S} :=
  Val.fst.measurable (hgExp hS)

theorem measurableSet_RSetG (hgExp : Measurable gExp) {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet (RSetG gExp S) :=
  measurableSet_TglCfgSet (measurableSet_φG hgExp hS)

theorem RSetG_union (A B : Set ℝ) : RSetG gExp (A ∪ B) = RSetG gExp A ∪ RSetG gExp B := by
  ext ρ
  simp only [RSetG, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨v, he, hr | hr⟩
    · exact Or.inl ⟨v, he, hr⟩
    · exact Or.inr ⟨v, he, hr⟩
  · rintro (⟨v, he, hr⟩ | ⟨v, he, hr⟩)
    · exact ⟨v, he, Or.inl hr⟩
    · exact ⟨v, he, Or.inr hr⟩

/-- `RSetG S = (gExp ∘ ·.expr)⁻¹'(S) ∩ {returns a value}`: on value configs the
config-level extraction `gExp ρ.expr` agrees with `gExp v.fst`. -/
theorem RSetG_eq_preimage (S : Set ℝ) :
    RSetG gExp S = (fun ρ : Cfg ℝ => gExp ρ.expr) ⁻¹' S ∩ RSetG gExp Set.univ := by
  ext ρ
  simp only [RSetG, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_univ, and_true]
  constructor
  · rintro ⟨v, he, hr⟩
    exact ⟨by rw [he]; exact hr, v, he⟩
  · rintro ⟨hmem, v, he⟩
    exact ⟨v, he, by rw [he] at hmem; exact hmem⟩

/-- **Ray instance.** Instantiating `IsDistSpecG` at `F = 𝟙_{Sᶜ}` and collapsing
the residual credit `↯(𝟙_{Sᶜ}(gExp v.fst))` via `↯1 ⊢ False` gives a pure total
triple: starting from `↯(μ Sᶜ)`, `e` terminates at a value with `gExp v.fst ∈ S`. -/
theorem ray_pure_wpG (e : Exp ℝ) (μ : Measure ℝ)
    (Hg2 : IsDistSpecG (GF := GF) gExp e μ) {S : Set ℝ} (hS : MeasurableSet S) :
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
      have hmem : gExp v.fst ∈ Sᶜ := by simpa using hr
      simp [Set.indicator_of_mem hmem]
  have hInt : ∫⁻ y, Sᶜ.indicator (fun _ => 1) y ∂μ = μ Sᶜ := by
    rw [lintegral_indicator_const hS.compl, one_mul]
  iapply (Hg2 (Sᶜ.indicator (fun _ => 1)) (measurable_const.indicator hS.compl) ?le1)
  case le1 => intro x; by_cases hx : x ∈ Sᶜ <;> simp [Set.indicator, hx]
  rw [hInt]
  iexact Hε

/-- **General distribution adequacy.** A distribution spec against a probability
measure `μ` on `ℝ`, with a measurable real extraction `gExp`, forces the limiting
execution of `e` to be distributed as `μ`: the pushforward of `limExec` along
`gExp ∘ (·.expr)` equals `μ`. -/
theorem twp_dist_adequacyG [AppPreGS ℝ GF] [ECPreGS GF] [InvGpreS GF]
    (hgExp : Measurable gExp) (e : Exp ℝ) (σ : State ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (Hg2 : IsDistSpecG (GF := GF) gExp e μ) :
    (limExec ⟨e, σ⟩).map (fun ρ => gExp ρ.expr) = μ := by
  have hmg : Measurable (fun ρ : Cfg ℝ => gExp ρ.expr) := hgExp.comp Cfg.measurable_expr
  have hUniv_le : (limExec ⟨e, σ⟩) Set.univ ≤ 1 :=
    limExec_leq_mass (fun n => execN_univ_le_one n ⟨e, σ⟩)
  -- **Ray lower bound**: for any measurable `S`, `μ S ≤ Pr[gExp(result) ∈ S]`.
  have lb : ∀ (S : Set ℝ), MeasurableSet S → μ S ≤ (limExec ⟨e, σ⟩) (RSetG gExp S) := by
    intro S hS
    have htgl : Tgl (limExec ⟨e, σ⟩) (fun v => gExp v.fst ∈ S) (μ Sᶜ) :=
      twp_tgl (σ := σ) (measurableSet_φG hgExp hS) (ray_pure_wpG e μ Hg2 hS)
    have hsum : μ S + μ Sᶜ = 1 := by rw [measure_add_measure_compl hS, measure_univ]
    have hcompl : (1 : ℝ≥0∞) - μ Sᶜ = μ S := by
      rw [← hsum, ENNReal.add_sub_cancel_right (measure_ne_top _ _)]
    have h1 : 1 - μ Sᶜ ≤ (limExec ⟨e, σ⟩) (RSetG gExp S) := htgl
    rwa [hcompl] at h1
  -- **Pinning**: the complementary lower bounds are forced to equalities.
  have pin : ∀ (S : Set ℝ), MeasurableSet S → (limExec ⟨e, σ⟩) (RSetG gExp S) = μ S := by
    intro S hS
    have hle1 := lb S hS
    have hle2 := lb Sᶜ hS.compl
    have hmeas2 : MeasurableSet (RSetG gExp Sᶜ) := measurableSet_RSetG hgExp hS.compl
    have hdisj : Disjoint (RSetG gExp S) (RSetG gExp Sᶜ) := by
      rw [Set.disjoint_left]
      rintro ρ ⟨v, he, hs⟩ ⟨v', he', hs'⟩
      have h1 : gExp ρ.expr ∈ S := by rw [he]; exact hs
      have h2 : gExp ρ.expr ∈ Sᶜ := by rw [he']; exact hs'
      exact h2 h1
    have hunion : RSetG gExp S ∪ RSetG gExp Sᶜ = RSetG gExp Set.univ := by
      rw [← RSetG_union, Set.union_compl_self]
    have hsum_lim : (limExec ⟨e, σ⟩) (RSetG gExp S) + (limExec ⟨e, σ⟩) (RSetG gExp Sᶜ)
        = (limExec ⟨e, σ⟩) (RSetG gExp Set.univ) := by
      rw [← measure_union hdisj hmeas2, hunion]
    have huniv1 : (limExec ⟨e, σ⟩) (RSetG gExp Set.univ) = 1 := by
      refine _root_.le_antisymm ((measure_mono (Set.subset_univ _)).trans hUniv_le) ?_
      have := lb Set.univ MeasurableSet.univ; rwa [measure_univ] at this
    have hxy1 : (limExec ⟨e, σ⟩) (RSetG gExp S) + (limExec ⟨e, σ⟩) (RSetG gExp Sᶜ) = 1 := by
      rw [hsum_lim, huniv1]
    have hy_ne : (limExec ⟨e, σ⟩) (RSetG gExp Sᶜ) ≠ (⊤ : ℝ≥0∞) :=
      ne_top_of_le_ne_top ENNReal.one_ne_top ((measure_mono (Set.subset_univ _)).trans hUniv_le)
    have hμsum : μ S + μ Sᶜ = 1 := by rw [measure_add_measure_compl hS, measure_univ]
    have hx_le : (limExec ⟨e, σ⟩) (RSetG gExp S) ≤ μ S := by
      have step : (limExec ⟨e, σ⟩) (RSetG gExp S) + (limExec ⟨e, σ⟩) (RSetG gExp Sᶜ)
          ≤ μ S + (limExec ⟨e, σ⟩) (RSetG gExp Sᶜ) := by
        rw [hxy1]
        calc (1 : ℝ≥0∞) = μ S + μ Sᶜ := hμsum.symm
          _ ≤ μ S + (limExec ⟨e, σ⟩) (RSetG gExp Sᶜ) := by gcongr
      exact (ENNReal.add_le_add_iff_right hy_ne).mp step
    exact _root_.le_antisymm hx_le hle1
  -- The execution measure is proper.
  have hRSetUniv1 : (limExec ⟨e, σ⟩) (RSetG gExp Set.univ) = 1 := by
    have := pin Set.univ MeasurableSet.univ; rwa [measure_univ] at this
  haveI hprob : IsProbabilityMeasure (limExec ⟨e, σ⟩) := by
    refine ⟨_root_.le_antisymm hUniv_le ?_⟩
    calc (1 : ℝ≥0∞) = (limExec ⟨e, σ⟩) (RSetG gExp Set.univ) := hRSetUniv1.symm
      _ ≤ (limExec ⟨e, σ⟩) Set.univ := measure_mono (Set.subset_univ _)
  -- The non-returning configs are null.
  have hnull : (limExec ⟨e, σ⟩) (RSetG gExp Set.univ)ᶜ = 0 := by
    rw [measure_compl (measurableSet_RSetG hgExp MeasurableSet.univ) (measure_ne_top _ _),
      measure_univ, hRSetUniv1, tsub_self]
  -- Intersecting with the conull "returns a value" set is measure-preserving.
  have hconull : ∀ (A : Set ℝ),
      (limExec ⟨e, σ⟩) ((fun ρ => gExp ρ.expr) ⁻¹' A ∩ RSetG gExp Set.univ)
        = (limExec ⟨e, σ⟩) ((fun ρ => gExp ρ.expr) ⁻¹' A) := by
    intro A
    refine _root_.le_antisymm (measure_mono Set.inter_subset_left) ?_
    set P := (fun ρ : Cfg ℝ => gExp ρ.expr) ⁻¹' A with hP
    have hsub : P ⊆ (P ∩ RSetG gExp Set.univ) ∪ (P ∩ (RSetG gExp Set.univ)ᶜ) := by
      intro x hx
      by_cases h : x ∈ RSetG gExp Set.univ
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    calc (limExec ⟨e, σ⟩) P
        ≤ (limExec ⟨e, σ⟩) ((P ∩ RSetG gExp Set.univ) ∪ (P ∩ (RSetG gExp Set.univ)ᶜ)) :=
          measure_mono hsub
      _ ≤ (limExec ⟨e, σ⟩) (P ∩ RSetG gExp Set.univ)
            + (limExec ⟨e, σ⟩) (P ∩ (RSetG gExp Set.univ)ᶜ) := measure_union_le _ _
      _ = (limExec ⟨e, σ⟩) (P ∩ RSetG gExp Set.univ) + 0 := by
          rw [measure_mono_null Set.inter_subset_right hnull]
      _ = (limExec ⟨e, σ⟩) (P ∩ RSetG gExp Set.univ) := add_zero _
  -- CDF equality of the pushforward and `μ`.
  have key : ∀ b : ℝ,
      ((limExec ⟨e, σ⟩).map (fun ρ => gExp ρ.expr)) (Set.Iic b) = μ (Set.Iic b) := by
    intro b
    rw [Measure.map_apply hmg measurableSet_Iic, ← hconull (Set.Iic b), ← RSetG_eq_preimage]
    exact pin (Set.Iic b) measurableSet_Iic
  haveI : IsProbabilityMeasure ((limExec ⟨e, σ⟩).map (fun ρ => gExp ρ.expr)) :=
    Measure.isProbabilityMeasure_map hmg.aemeasurable
  exact Measure.ext_of_Iic _ _ key

end General

/-! ## Bare-real special case

The real projection `realOfExp : Exp ℝ → ℝ` reads the payload of a real literal
(junk `0` otherwise). When the sampler returns a real literal directly, this is
the natural extraction. -/

/-- The real-literal embedding `r ↦ .lit (.real r)` into expressions. -/
def realEmb : ℝ → Exp ℝ := fun r => Exp.lit (.real r)

theorem measurableEmbedding_realEmb : MeasurableEmbedding realEmb :=
  Exp.lit.measurableEmbedding.comp BaseLit.real.measurableEmbedding

/-- Extract the real payload of an expression (junk `0` off the real literals),
as a measurable extension of the identity along `realEmb`. -/
noncomputable def realOfExp : Exp ℝ → ℝ := Function.extend realEmb id (fun _ => 0)

theorem measurable_realOfExp : Measurable realOfExp :=
  measurableEmbedding_realEmb.measurable_extend measurable_id measurable_const

@[simp]
theorem realOfExp_real (r : ℝ) : realOfExp (Exp.lit (.real r)) = r := by
  show Function.extend realEmb id (fun _ => 0) (realEmb r) = r
  rw [measurableEmbedding_realEmb.injective.extend_apply]; rfl

/-- **Distribution adequacy (bare-real case).** If `e`'s returned value is a real
literal `.real r` carrying credit `↯(F r)`, `e` is distributed as `μ`. -/
theorem twp_dist_adequacy [AppPreGS ℝ GF] [ECPreGS GF] [InvGpreS GF]
    (e : Exp ℝ) (σ : State ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Hg2 : IsDistSpecG (GF := GF) realOfExp e μ) :
    (limExec ⟨e, σ⟩).map (fun ρ => realOfExp ρ.expr) = μ :=
  twp_dist_adequacyG measurable_realOfExp e σ μ Hg2

end TotalEris
end ProbLang
