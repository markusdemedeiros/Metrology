module

public import Metrology.TotalEris
public import Metrology.ProbLang.Reals

@[expose] public section

/-!
# Real decreasing trial — continuous-uniform port

Port of `clutch/theories/eris/examples/real_decr_trial.v`, redesigned to use
the total continuous-Eris uniform sampler `urand` (see `Examples/Irrational.lean`)
instead of lazy reals / infinite tapes.

In the Rocq development a *lazy real* `lazy_real v r` is a heap value `v`
holding a chunked binary tape whose infinite binary expansion is the real
`r ∈ [0,1)`; `init ()` samples such a real one bit at a time and `cmp`
compares two of them lazily. Because continuous Eris can sample a real in a
single step, the whole lazy-real apparatus collapses:

  * `init ()`                          ⟶  `urand`
  * `cmp y x = #(-1)`  (i.e. `y < x`)  ⟶  the real comparison `y < x`
  * `wp_lazy_real_presample_adv_comp`  ⟶  `twp_urand_exp`
  * the predicate `lazy_real v r`      ⟶  the value **is** the real: `.real r`

Consequently a "lazy real argument" `(x, rx)` with `lazy_real x rx` becomes a
single real value `x : ℝ` (its own denotation), and the `0 ≤ rx ≤ 1` side
condition is kept as a hypothesis.

We work at the concrete real type `rT = ℝ` (as `Examples/Irrational.lean`
does): the specifications mention `0 ≤ x ≤ 1` and the program compares reals,
both of which need an order on the real type. Generalising to an abstract
`rT` requires the planned `ProbLangℝ` real-order extension.

**Status: stub.** Programs and specifications only; every proof is `sorry`.
The math definitions (`RealDecrTrialμ`, `RealDecrTrialCreditV`,
`RealDecrTrialg`) are written out; the supporting analytic lemmas and the WP
specs are `sorry`.

⚠️ The program uses the real comparison `y < x`, whose *operational* rule
(`BinOp.eval` on `.real` operands) does not exist yet — it is proof-phase
task #1 (extend `ProbLangℝ` with a decidable/measurable order and add the
`BinOp.eval` real cases). The stub still elaborates because `pl%` maps `<` to
`Exp.binop .lt` without needing the evaluator.
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [ErisGS ℝ hlc GF]

/-! ## PMF -/

/-- PMF for `DecrTrial` started at `N = 0`. Rocq `RealDecrTrial_μ0`:
`x^n / n! - x^(n+1) / (n+1)!`. -/
def RealDecrTrialμ0 (x : ℝ) (n : ℕ) : ℝ≥0∞ :=
  .ofReal (x ^ n / n.factorial - x ^ (n + 1) / (n + 1).factorial)

/-- PMF for `DecrTrial` started at `N = i`. Rocq `RealDecrTrial_μ`:
`[i ≤ n] · μ0 x (n - i)`. -/
def RealDecrTrialμ (x : ℝ) (i n : ℕ) : ℝ≥0∞ :=
  if i ≤ n then RealDecrTrialμ0 x (n - i) else 0

/-- Rocq `RealDecrTrial_μ_not_supp`. -/
theorem RealDecrTrialμ_not_supp {x : ℝ} {i n : ℕ} (H : n < i) :
    RealDecrTrialμ x i n = 0 := by sorry

/-- Rocq `RealDecrTrial_μ_supp`. -/
theorem RealDecrTrialμ_supp {x : ℝ} {i n : ℕ} (H : i ≤ n) :
    RealDecrTrialμ x i n = RealDecrTrialμ0 x (n - i) := by sorry

/-- Rocq `RealDecrTrial_μ_base`. -/
theorem RealDecrTrialμ_base {x : ℝ} {n : ℕ} :
    RealDecrTrialμ x 0 n = RealDecrTrialμ0 x n := by sorry

/-! ## Credits -/

/-- Expected number of credits to run `DecrTrial i x`. Rocq
`RealDecrTrial_CreditV`: `∑ₙ μ x i n · F n`. -/
def RealDecrTrialCreditV (F : ℕ → ℝ≥0∞) (i : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, RealDecrTrialμ x i n * F n

/-- Per-sample credit-distribution function. Rocq `g`:
`[y ≤ x] · CreditV F (i+1) y  +  [y ≥ x] · F i`. -/
def RealDecrTrialg (F : ℕ → ℝ≥0∞) (i : ℕ) (x : ℝ) : ℝ → ℝ≥0∞ := fun y =>
  (if y ≤ x then RealDecrTrialCreditV F (i + 1) y else 0) +
  (if x ≤ y then F i else 0)

/-- Rocq `CreditV_nonneg` — trivial in `ℝ≥0∞`, kept for parity. -/
theorem RealDecrTrialCreditV_nonneg (F : ℕ → ℝ≥0∞) (i : ℕ) (x : ℝ) :
    0 ≤ RealDecrTrialCreditV F i x := zero_le'

section Wp

open MeasureTheory in
/-- Credit conservation. Rocq `g_expectation` states
`is_RInt (g F N x) 0 1 (CreditV F N x)`; restated here as a `lintegral` over
the uniform-unit measure — this is exactly the hypothesis `twp_urand_exp`
consumes when distributing `↯(CreditV F N x)` across the freshly sampled real. -/
theorem RealDecrTrialg_lintegral {F : ℕ → ℝ≥0∞} {M : ℝ≥0∞} {N : ℕ} {x : ℝ}
    (Hx : 0 ≤ x ∧ x ≤ 1) (Hbound : ∀ n, F n ≤ M) :
    ∫⁻ y, RealDecrTrialg F N x y ∂(ProbLangℝ.unifUnit (T := ℝ)) =
      RealDecrTrialCreditV F N x := by
  sorry

end Wp

/-! ## Program

Rocq `lazyDecrR`:
```
rec: "trial" "N" "x" :=
  let: "y" := init #() in
  if: (cmp "y" "x" = #(-1)) then "trial" ("N" + #1) "y"   (* y < x *)
                            else "N".
```
Under `urand`, `init ()` becomes `urand` and `cmp y x = -1` becomes `y < x`. -/
@[pl_fold]
def DecrTrial : Exp ℝ := pl%
  rec trial N x :=
    let y := urand;
    if y < x then trial (N + #1) y else N

/-! ## Specification

Rocq `wp_lazyDecrR_gen`:
```
∀ N x rx, lazy_real x rx ∗ ⌜0 ≤ rx ≤ 1⌝ ∗ ↯(CreditV F N rx) -∗
  WP lazyDecrR #N x {{ z, ∃ n, ⌜z = #n⌝ ∗ ↯(F n) ∗ lazy_real x rx }}
```
Under `urand` the `lazy_real x rx` predicate disappears (the value is the real
`x`), so both it and the returned copy drop out of the triple. -/
theorem twp_DecrTrial (E : CoPset) (F : ℕ → ℝ≥0∞) (M : ℝ≥0∞) (Hnn : ∀ n, F n ≤ M)
    (N : ℕ) (x : ℝ) (Hx : 0 ≤ x ∧ x ≤ 1) :
    ⊢@{IProp GF} ↯ (RealDecrTrialCreditV F N x) -∗
      tglWp E pl(&DecrTrial #(.int (N : ℤ)) #(.real x))
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  sorry

end
end Examples
end TotalEris
end ProbLang
