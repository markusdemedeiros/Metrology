module

public import Metrology.TotalEris.DistributionAdequacy
public import Metrology.TotalEris.Examples.Samplers.Gaussian

@[expose] public section

/-! # Distribution adequacy for the standard Gaussian sampler

`Gaussian.lean` proves the weakest-precondition spec `twp_Gauss` and identifies
the expected credit with the standard-Gaussian expectation
(`gauss_credit_eq_gaussianReal`). This file turns that into an adequacy
statement: the limiting execution of `Gauss`, read as a real, is distributed
exactly as `gaussianReal 0 1`.

The sampler returns a bare real literal, so the extraction is the plain real
projection `realOfExp` and the bare-real `twp_dist_adequacy` applies directly.
-/

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris ProbLang.TotalEris.Examples
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {GF : BundledGFunctors.{0,0,0}}

open MeasureTheory ProbabilityTheory in
/-- `Gauss` meets the distribution specification for `gaussianReal 0 1`, reading
the sampled real straight off the returned literal. -/
theorem gauss_std_distSpec :
    IsDistSpec' (GF := GF) realOfExp (pl(&Gauss #.unit)) (gaussianReal 0 1) := by
  intro F hFm _ _
  iintro Hε
  iapply ErisWpGS.tglWp_wand
  isplitl [Hε]
  · iapply (twp_Gauss (GF := GF) ⊤ F hFm)
    iapply (ErrorCredit.ext (gauss_credit_eq_gaussianReal F hFm))
    iexact Hε
  · iintro %v ⟨%y, %hy, Hcy⟩
    rw [hy, realOfExp_real]
    iexact Hcy

open MeasureTheory ProbabilityTheory in
/-- **The sampler is a standard Gaussian sampler.** The limiting execution of
`Gauss`, read as a real, is distributed exactly as `N(0,1)`. -/
theorem gauss_std_distributed [AppPreGS ℝ GF] [ECPreGS GF] [InvGpreS GF] (σ : State ℝ) :
    (limExec ⟨pl(&Gauss #.unit), σ⟩).map (fun ρ => realOfExp ρ.expr) = gaussianReal 0 1 :=
  twp_dist_adequacy (GF := GF) (pl(&Gauss #.unit)) σ (gaussianReal 0 1)
    (gauss_std_distSpec (GF := GF))

end

end Examples
end TotalEris
end ProbLang
