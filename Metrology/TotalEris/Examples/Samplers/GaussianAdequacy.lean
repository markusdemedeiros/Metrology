module

public import Metrology.TotalEris.DistributionAdequacy
public import Metrology.TotalEris.Examples.Samplers.Gauss

/-!
# Distribution adequacy for the continuous Gaussian sampler

We instantiate the general distribution-adequacy theorem `twp_dist_adequacyG` for
the continuous Gaussian sampler `G2 ()`.

`G2 ()` returns a *pair* `(x, k)` with `x ∈ [0,1)` and `k : ℕ`; the sampled real
is `x + k` (the object language has no real addition, so the value is kept split
into its fractional and integer parts). The meta-level extraction
`gaussOfExp : Exp ℝ → ℝ` recovers `x + k`.

The target law `gaussMeasure` is the pushforward of the `G2`-mixture along
`x ↦ x + k`: a probability measure on `[0,∞)` (total mass `1` by `G2μ_total`).
The final corollary `gauss_distributed` states that the limiting execution of
`G2 ()`, projected through `gaussOfExp`, is exactly `gaussMeasure`.
-/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.Examples ProbLang.TotalEris.ErisWpGS MeasureTheory HeapView Auth
open scoped AppGS ENNReal

namespace ProbLang
namespace TotalEris
namespace Examples

/-! ## The Gaussian real extraction `(x, k) ↦ x + k` -/

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
noncomputable def gaussOfExp : Exp ℝ → ℝ :=
  Function.extend pairEmb (fun p => p.1 + (p.2 : ℝ)) (fun _ => 0)

theorem measurable_gaussOfExp : Measurable gaussOfExp :=
  measurableEmbedding_pairEmb.measurable_extend (by fun_prop) measurable_const

@[simp]
theorem gaussOfExp_pair (x : ℝ) (m : ℤ) :
    gaussOfExp (Exp.pair (Exp.lit (.real x)) (Exp.lit (.int m))) = x + (m : ℝ) := by
  simp only [gaussOfExp, measurableEmbedding_pairEmb.injective.extend_apply]

/-! ## The target Gaussian measure -/

theorem measurable_G2μ (k : ℕ) : Measurable (G2μ k) := by fun_prop

/-- The law of the `G2` sample `x + k`: the mixture of `unifUnit`-weighted-by-`G2μ k`
laws pushed forward along `x ↦ x + k`. A probability measure on `[0,∞)`. -/
noncomputable def gaussMeasure : Measure ℝ :=
  Measure.sum fun k : ℕ =>
    ((ProbLangℝ.unifUnit (T := ℝ)).withDensity (G2μ k)).map (fun x => x + (k : ℝ))

instance : IsProbabilityMeasure gaussMeasure := by
  constructor
  rw [gaussMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact G2μ_total

/-- Change of variables: the credit `∫⁻ · ∂gaussMeasure` is the `G2` mixture credit
`G2_CreditV` of `F' k r := F (r + k)`. -/
theorem gauss_credit_eq (F : ℝ → ℝ≥0∞) (hFm : Measurable F) :
    ∫⁻ y, F y ∂gaussMeasure = G2_CreditV (fun k r => F (r + k)) := by
  rw [gaussMeasure, lintegral_sum_measure, G2_CreditV]
  refine tsum_congr fun k => by
    rw [lintegral_map hFm (by fun_prop),
      lintegral_withDensity_eq_lintegral_mul _ (measurable_G2μ k) (by fun_prop)]

/-! ## Adequacy -/

variable {GF : BundledGFunctors.{0,0,0}}

/-- The Gaussian sampler `G2 ()` satisfies the distribution specification against
`gaussMeasure` with extraction `gaussOfExp`. -/
theorem gauss_distSpec :
    IsDistSpecG (GF := GF) gaussOfExp (pl(&G2 #.unit)) gaussMeasure := by
  intro F hFm hF1 _
  iintro Hε
  iapply ErisWpGS.tglWp_wand
  isplitl [Hε]
  · -- WP branch: instantiate `twp_G2` at `F' k r := F (r + k)`, feeding `Hε` as its credit.
    iapply (twp_G2 (GF := GF) ⊤ (fun k r => F (r + k)) 1
      (fun x k _ _ => hF1 _) (fun k => hFm.comp (measurable_id.add_const _)))
    rw [← gauss_credit_eq F hFm]
    iexact Hε
  · -- Weakening branch: the pair postcondition ⇒ `↯(F (gaussOfExp v.fst))`.
    iintro %v ⟨%k, %r, %hrange, %hpair, Hcr⟩
    have hg : gaussOfExp v.fst = r + (k : ℝ) := by
      simp only [hpair, gaussOfExp_pair, Int.ofNat_eq_natCast]
    rw [hg]
    iexact Hcr

/-- **Distribution adequacy for the continuous Gaussian.** The limiting execution
of `G2 ()`, read through the real extraction `x + k`, is distributed exactly as
`gaussMeasure`. -/
theorem gauss_distributed [AppPreGS ℝ GF] [ECPreGS GF] [InvGpreS GF] (σ : State ℝ) :
    (limExec ⟨pl(&G2 #.unit), σ⟩).map (fun ρ => gaussOfExp ρ.expr) = gaussMeasure :=
  twp_dist_adequacyG (GF := GF) measurable_gaussOfExp (pl(&G2 #.unit)) σ gaussMeasure
    (gauss_distSpec (GF := GF))

end Examples
end TotalEris
end ProbLang
