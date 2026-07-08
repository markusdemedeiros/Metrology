module

public import Metrology.TotalEris
public import Metrology.ProbLang.Reals
public import Metrology.TotalEris.Examples.Gaussian.NegExp

@[expose] public section

/-!
# Laplace sampler — port of `laplace.v` (Gauss's sister)

* `NegExpSymm ()` symmetrises `NegExp`: it draws a sign bit and a
  negative-exponential magnitude `(vz, vr)`, returning `(b, (vz, vr))`.
* `NegExpSymmC ()` reconstructs the signed real `±(vz + vr)`.
* `Laplace0 logε` scales that sample by `2^logε` to get a mean-0 Laplace
  variate; `Laplace logε μ` shifts it by `μ`.

Under `urand` the lazy-real-expr layer collapses: `IsApprox cont r` becomes
`cont = .real r` (the value *is* the real), and `ToLazyReal`/`R_plus`/`R_mulPow`
become ordinary real arithmetic on direct real values.

⚠️ `R_mulPow` multiplies a real by `2^logε` at runtime, which needs a real
power-of-two operation — a *second* proof-phase language extension, analogous
to the real `<` needed by `RealDecrTrial`. It is stubbed below via the
unspecified helper `R_pow2`.

**Status: stub.** Programs and specifications only; every proof is `sorry`.
Fixed at `rT = ℝ`.
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [ErisGS ℝ hlc GF]

/-! ## PMF / credits -/

/-- Mean-0 Laplace density with scale `ε`. Rocq `Laplace0_μ`:
`ε · (exp(-|ε·x|) / 2)`. -/
def Laplace0μ (ε x : ℝ) : ℝ := ε * (Real.exp (-|ε * x|) / 2)

open MeasureTheory in
/-- Rocq `Laplace0_CreditV`: `∫_ℝ Laplace0_μ ε x · F x dx`. -/
def Laplace0_CreditV (ε : ℝ) (F : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x, .ofReal (Laplace0μ ε x) * F x ∂(volume : Measure ℝ)

/-- Laplace density shifted to mean `μ`. Rocq `Laplace_μ`:
`Laplace0_μ ε (x - μ)`. -/
def Laplaceμ (ε μ x : ℝ) : ℝ := Laplace0μ ε (x - μ)

open MeasureTheory in
/-- Rocq `Laplace_CreditV`: `∫_ℝ Laplace_μ ε μ x · F x dx`. -/
def Laplace_CreditV (ε μ : ℝ) (F : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x, .ofReal (Laplaceμ ε μ x) * F x ∂(volume : Measure ℝ)

/-! ## Programs

Rocq:
```
NegExpSymm  := λ "e",  let: "v" := NegExp #0 in let: "b" := rand #1 in ("b", "v").
NegExpSymmC := λ "_",  let: "s" := NegExpSymm #() in ToLazyReal "s".
Laplace0    := λ "logε", let: "sR" := NegExpSymmC #() in R_mulPow "sR" "logε".
Laplace     := λ "logε" "μ", let: "s" := Laplace0 "logε" in R_plus "μ" "s".
```
(`rand #1` — clutch's `{0,1}` coin — becomes ProbLang `rand #2`.) -/

@[pl_fold]
def NegExpSymm : Exp ℝ := pl%
  fun e,
    let v := &NegExp #0;
    let b := rand(#2, #.unit);
    (b, v)

/-- Reconstruct the signed real from `(b, (vz, vr))`: `±(vz + vr)`
(urand collapse of Rocq `ToLazyReal ∘ bzu_to_R`). -/
@[pl_fold]
def NegExpSymmC : Exp ℝ := pl%
  fun _u,
    let s := &NegExpSymm #.unit;
    let! (b, zu) := s;
    let! (z, u) := zu;
    (if b = #0 then z + u else -(z + u))

/-- Real addition (urand collapse of Rocq `R_plus`). -/
@[pl_fold]
def R_plus : Exp ℝ := pl% fun a, fun b, a + b

/-- Multiply a real by `2^logε` (urand collapse of Rocq `R_mulPow`). The
`2^logε` factor is produced by the unspecified helper `R_pow2` — see the
module-level ⚠️ note (needs a real power-of-two language op). -/
@[pl_fold]
def R_mulPow : Exp ℝ := pl% fun r, fun logε, r * (R_pow2 logε)

@[pl_fold]
def Laplace0 : Exp ℝ := pl%
  fun logε,
    let sR := &NegExpSymmC #.unit;
    &R_mulPow sR logε

@[pl_fold]
def Laplace : Exp ℝ := pl%
  fun logε, fun mu,
    let s := &Laplace0 logε;
    &R_plus mu s

/-! ## Specifications -/

/-- Rocq `wp_Laplace0`: `Laplace0 logε` samples a mean-0 Laplace variate at
scale `2^logε`. `IsApprox cont r` collapses to `cont = .real r`. -/
theorem twp_Laplace0 (E : CoPset) (F : ℝ → ℝ≥0∞) (M : ℝ≥0∞) (logε : ℤ)
    (Hnn : ∀ r, F r ≤ M) :
    ⊢@{IProp GF} ↯ (Laplace0_CreditV ((2 : ℝ) ^ logε) F) -∗
      tglWp E pl(&Laplace0 #(.int logε))
        (fun cont : Val ℝ => iprop(∃ r : ℝ, ⌜cont.1 = .lit (.real r)⌝ ∗ ↯ (F r))) := by
  sorry

/-- Rocq `wp_Laplace`: `Laplace logε μ` samples a Laplace variate with mean `μ`
and scale `2^logε`. The lazy-real mean `μcont` / `IsApprox μcont μ` becomes the
real value `.real μ`. -/
theorem twp_Laplace (E : CoPset) (F : ℝ → ℝ≥0∞) (M : ℝ≥0∞) (logε : ℤ) (μ : ℝ)
    (Hnn : ∀ r, F r ≤ M) :
    ⊢@{IProp GF} ↯ (Laplace_CreditV ((2 : ℝ) ^ logε) μ F) -∗
      tglWp E pl(&Laplace #(.int logε) #(.real μ))
        (fun cont : Val ℝ => iprop(∃ r : ℝ, ⌜cont.1 = .lit (.real r)⌝ ∗ ↯ (F r))) := by
  sorry

end
end Examples
end TotalEris
end ProbLang
