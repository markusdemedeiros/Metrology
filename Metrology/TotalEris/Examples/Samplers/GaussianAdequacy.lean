module

public import Metrology.TotalEris.DistributionAdequacy
public import Metrology.TotalEris.Examples.Samplers.Gauss

/-!
# Distribution adequacy for the continuous Gaussian sampler

We instantiate the general distribution-adequacy theorem `twp_dist_adequacyG` for
the continuous Gaussian sampler `G2`.

`G2 ()` returns a *pair* `(x, k)` with `x ∈ [0,1)` and `k : ℕ`; the sampled real
is `x + k` (the object language has no real addition, so the value is kept split
into its fractional and integer parts). The meta-level extraction
`gExp_gauss : Exp ℝ → ℝ` recovers `x + k`.

The target law `gaussMeasure` is the pushforward of the `G2`-mixture along
`x ↦ x + k`: a probability measure on `[0,∞)` (its total mass is `1` by
`G2μ_total`). The final corollary `gauss_distributed` states that the limiting
execution of `G2`, projected through `gExp_gauss`, is exactly `gaussMeasure`.

The single remaining obligation `gauss_distSpec` is the change-of-variables that
rewrites the mixture credit of `twp_G2` (indexed by `(k, x)`) as `∫⁻ · ∂gaussMeasure`
and matches the pair postcondition against `gExp_gauss`. It is isolated as a
`sorry` here.
-/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.Examples ProbLang.TotalEris.ErisWpGS MeasureTheory HeapView Auth
open scoped AppGS ENNReal

namespace ProbLang
namespace TotalEris
namespace Examples

/-! ## The Gaussian real extraction `(x, k) ↦ x + k` -/

/-- Embed an integer as an integer-literal expression. -/
def intEmb : ℤ → Exp ℝ := fun m => Exp.lit (.int m)

theorem measurableEmbedding_intEmb : MeasurableEmbedding intEmb :=
  Exp.lit.measurableEmbedding.comp BaseLit.int.measurableEmbedding

/-- Embed a `(real, int)` pair as the value `G2` returns: `(.real x, .int m)`. -/
def pairEmb : ℝ × ℤ → Exp ℝ := fun p => Exp.pair (realEmb p.1) (intEmb p.2)

theorem measurableEmbedding_pairEmb : MeasurableEmbedding pairEmb :=
  Exp.pair.measurableEmbedding.comp
    (measurableEmbedding_realEmb.prodMap measurableEmbedding_intEmb)

/-- The sampled real value `x + k` extracted from `G2`'s pair `(x, k)`
(junk `0` off such pairs). -/
noncomputable def gExp_gauss : Exp ℝ → ℝ :=
  Function.extend pairEmb (fun p => p.1 + (p.2 : ℝ)) (fun _ => 0)

theorem measurable_gExp_gauss : Measurable gExp_gauss :=
  measurableEmbedding_pairEmb.measurable_extend (by fun_prop) measurable_const

@[simp]
theorem gExp_gauss_pair (x : ℝ) (m : ℤ) :
    gExp_gauss (Exp.pair (Exp.lit (.real x)) (Exp.lit (.int m))) = x + (m : ℝ) := by
  show Function.extend pairEmb (fun p => p.1 + (p.2 : ℝ)) (fun _ => 0) (pairEmb (x, m)) = _
  rw [measurableEmbedding_pairEmb.injective.extend_apply]

/-! ## The target Gaussian measure -/

/-- The law of the `G2` sample `x + k`: the mixture of `unifUnit`-weighted-by-`G2μ k`
laws pushed forward along `x ↦ x + k`. A probability measure on `[0,∞)`. -/
noncomputable def gaussMeasure : Measure ℝ :=
  Measure.sum fun k : ℕ =>
    ((ProbLangℝ.unifUnit (T := ℝ)).withDensity (G2μ k)).map (fun x => x + (k : ℝ))

instance : IsProbabilityMeasure gaussMeasure := by
  constructor
  rw [gaussMeasure, Measure.sum_apply _ MeasurableSet.univ]
  have hk : ∀ k : ℕ,
      (((ProbLangℝ.unifUnit (T := ℝ)).withDensity (G2μ k)).map (fun x => x + (k : ℝ))) Set.univ
        = ∫⁻ x, G2μ k x ∂(ProbLangℝ.unifUnit (T := ℝ)) := by
    intro k
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp_rw [hk]
  exact G2μ_total

/-! ## Adequacy -/

variable {GF : BundledGFunctors.{0,0,0}}

/-- The Gaussian sampler `G2` satisfies the distribution specification against
`gaussMeasure` with extraction `gExp_gauss`.

**Remaining obligation.** Instantiate `twp_G2` at `F k x := F' (x + k)` and:
* rewrite its mixture credit `∑ₖ ∫₀¹ G2μ k x · F'(x+k) dx` as `∫⁻ y, F' y ∂gaussMeasure`
  (change of variables `y = x + k`: `lintegral_sum` + `lintegral_map` + `lintegral_withDensity`);
* weaken the pair postcondition `∃ k r, ⌜v = (.real r, .int k)⌝ ∗ ↯(F k r)` to
  `↯(F' (gExp_gauss v.fst))` via `gExp_gauss_pair` and `tglWp_mono`. -/
theorem gauss_distSpec : IsDistSpecG (GF := GF) gExp_gauss Examples.G2 gaussMeasure := by
  sorry

/-- **Distribution adequacy for the continuous Gaussian.** The limiting execution
of `G2`, read through the real extraction `x + k`, is distributed exactly as
`gaussMeasure`. -/
theorem gauss_distributed [AppPreGS ℝ GF] [ECPreGS GF] [InvGpreS GF] (σ : State ℝ) :
    (limExec ⟨Examples.G2, σ⟩).map (fun ρ => gExp_gauss ρ.expr) = gaussMeasure :=
  twp_dist_adequacyG (GF := GF) measurable_gExp_gauss Examples.G2 σ gaussMeasure
    (gauss_distSpec (GF := GF))

end Examples
end TotalEris
end ProbLang
