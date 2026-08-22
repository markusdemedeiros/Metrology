module

public import Metrology.TotalEris.DistributionAdequacy
public import Metrology.TotalEris.Examples.Samplers.Gauss

@[expose] public section

/-! # Distribution adequacy for the continuous Gaussian sampler -/

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris ProbLang.TotalEris.Examples
  ProbLang.TotalEris.ErisWpGS MeasureTheory
open scoped AppGS ENNReal

namespace ProbLang
namespace TotalEris
namespace Examples

section extraction

def intEmb : ℤ → Exp ℝ := fun m => Exp.lit (.int m)

theorem measurableEmbedding_intEmb : MeasurableEmbedding intEmb :=
  Exp.lit.measurableEmbedding.comp BaseLit.int.measurableEmbedding

def pairEmb : ℝ × ℤ → Exp ℝ := fun p => Exp.pair (realEmb p.1) (intEmb p.2)

theorem measurableEmbedding_pairEmb : MeasurableEmbedding pairEmb :=
  Exp.pair.measurableEmbedding.comp
    (measurableEmbedding_realEmb.prodMap measurableEmbedding_intEmb)

noncomputable def gaussOfExp : Exp ℝ → ℝ :=
  Function.extend pairEmb (fun p => p.1 + (p.2 : ℝ)) (fun _ => 0)

theorem measurable_gaussOfExp : Measurable gaussOfExp :=
  measurableEmbedding_pairEmb.measurable_extend (by fun_prop) measurable_const

@[simp]
theorem gaussOfExp_pair (x : ℝ) (m : ℤ) :
    gaussOfExp (Exp.pair (Exp.lit (.real x)) (Exp.lit (.int m))) = x + (m : ℝ) := by
  exact measurableEmbedding_pairEmb.injective.extend_apply _ _ (x, m)

end extraction

section targetMeasure

theorem measurable_g2pdf (k : ℕ) : Measurable (G2pdf k) := by unfold G2pdf; fun_prop

noncomputable def gaussMeasure : Measure ℝ :=
  Measure.sum fun k : ℕ =>
    ((ProbLangℝ.unifUnit (T := ℝ)).withDensity (G2pdf k)).map (fun x => x + (k : ℝ))

instance : IsProbabilityMeasure gaussMeasure := by
  constructor
  rw [gaussMeasure, Measure.sum_apply _ MeasurableSet.univ, ← G2pdf_total]
  exact tsum_congr fun k => by
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

theorem gauss_credit_eq (F : ℝ → ℝ≥0∞) (hFm : Measurable F) :
    ∫⁻ y, F y ∂gaussMeasure = G2CreditV (fun k r => F (r + k)) := by
  rw [gaussMeasure, lintegral_sum_measure, G2CreditV]
  exact tsum_congr fun k => by
    rw [lintegral_map hFm (by fun_prop),
      lintegral_withDensity_eq_lintegral_mul _ (measurable_g2pdf k) (by fun_prop)]
    simp only [Pi.mul_apply]

end targetMeasure

section adequacy

variable {GF : BundledGFunctors.{0,0,0}}

theorem gauss_distSpec :
    IsDistSpec' (GF := GF) gaussOfExp (pl(&G2 #.unit)) gaussMeasure := by
  intro F hFm _ _
  iintro Hε
  iapply ErisWpGS.tglWp_wand
  isplitl [Hε]
  · iapply (twp_G2 (GF := GF) ⊤ (fun k r => F (r + k))
      (fun k => hFm.comp (measurable_id.add_const _)))
    rw [← gauss_credit_eq F hFm]
    iexact Hε
  · iintro %v ⟨%k, %r, -, %hpair, Hcr⟩
    have hval : gaussOfExp v.fst = r + (k : ℝ) := by
      simp only [hpair, gaussOfExp_pair, Int.ofNat_eq_natCast, Int.cast_natCast]
    rw [hval]
    iexact Hcr

theorem gauss_distributed [AppPreGS ℝ GF] [ECPreGS GF] [InvGpreS GF] (σ : State ℝ) :
    (limExec ⟨pl(&G2 #.unit), σ⟩).map (fun ρ => gaussOfExp ρ.expr) = gaussMeasure :=
  twp_dist_adequacy' (GF := GF) measurable_gaussOfExp (pl(&G2 #.unit)) σ gaussMeasure
    (gauss_distSpec (GF := GF))

end adequacy

end Examples
end TotalEris
end ProbLang
