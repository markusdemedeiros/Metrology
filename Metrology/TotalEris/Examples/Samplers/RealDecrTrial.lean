module

public import Metrology.TotalEris
public import Metrology.ProbLang.Reals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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
    RealDecrTrialμ x i n = 0 := by
  simp only [RealDecrTrialμ, if_neg (Nat.not_le.mpr H)]

/-- Rocq `RealDecrTrial_μ_supp`. -/
theorem RealDecrTrialμ_supp {x : ℝ} {i n : ℕ} (H : i ≤ n) :
    RealDecrTrialμ x i n = RealDecrTrialμ0 x (n - i) := by
  simp only [RealDecrTrialμ, if_pos H]

/-- Rocq `RealDecrTrial_μ_base`. -/
theorem RealDecrTrialμ_base {x : ℝ} {n : ℕ} :
    RealDecrTrialμ x 0 n = RealDecrTrialμ0 x n := by
  simp only [RealDecrTrialμ, Nat.zero_le, if_pos, Nat.sub_zero]

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
/-- The amplified per-sample credit: the ordinary `RealDecrTrialg` plus a
termination top-up `k·ε_term` on the recursion region `{y < x}`. -/
def RealDecrTrialgAmp (F : ℕ → ℝ≥0∞) (N : ℕ) (x : ℝ) (c : ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  fun y => RealDecrTrialg F N x y + (if y < x then c else 0)

/-! ## Measurability

The credit-distribution functions fed to `twp_urand_exp'` are Borel measurable:
`μ0` is `ofReal` of a polynomial, `μ` toggles it by an `x`-independent guard, `CreditV`
is a `tsum` of such terms, and `g`/`gAmp` glue them with interval indicators. -/

theorem RealDecrTrialμ0_measurable (n : ℕ) :
    Measurable (fun x : ℝ => RealDecrTrialμ0 x n) :=
  ENNReal.measurable_ofReal.comp (by fun_prop)

theorem RealDecrTrialμ_measurable (i n : ℕ) :
    Measurable (fun x : ℝ => RealDecrTrialμ x i n) := by
  unfold RealDecrTrialμ
  by_cases h : i ≤ n
  · simpa only [h, if_true] using RealDecrTrialμ0_measurable (n - i)
  · simpa only [h, if_false] using measurable_const

theorem RealDecrTrialCreditV_measurable (F : ℕ → ℝ≥0∞) (i : ℕ) :
    Measurable (fun x : ℝ => RealDecrTrialCreditV F i x) :=
  Measurable.ennreal_tsum fun n => (RealDecrTrialμ_measurable i n).mul_const (F n)

theorem RealDecrTrialg_measurable (F : ℕ → ℝ≥0∞) (i : ℕ) (x : ℝ) :
    Measurable (RealDecrTrialg F i x) := by
  unfold RealDecrTrialg
  refine Measurable.add ?_ ?_
  · exact Measurable.ite measurableSet_Iic (RealDecrTrialCreditV_measurable F (i + 1))
      measurable_const
  · exact Measurable.ite measurableSet_Ici measurable_const measurable_const

theorem RealDecrTrialgAmp_measurable (F : ℕ → ℝ≥0∞) (N : ℕ) (x : ℝ) (c : ℝ≥0∞) :
    Measurable (RealDecrTrialgAmp F N x c) :=
  (RealDecrTrialg_measurable F N x).add
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)

open MeasureTheory in
/-- `∫⁻` of `ofReal ∘ g` over `[0,t]` is `ofReal` of the interval integral (for nonneg
continuous `g`). The reusable `lintegral ↔ intervalIntegral` bridge. -/
theorem lintegral_ofReal_Icc {t : ℝ} (ht : 0 ≤ t) {g : ℝ → ℝ} (hg : Continuous g)
    (hgn : ∀ r ∈ Set.Icc (0 : ℝ) t, 0 ≤ g r) :
    ∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (g r) ∂volume = ENNReal.ofReal (∫ r in (0 : ℝ)..t, g r) := by
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg.integrableOn_Icc
        (ae_restrict_of_forall_mem measurableSet_Icc hgn),
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]

/-! ## Credit conservation (`g_expectation`)

The single analytic fact behind `DecrTrial`: the uniform average of `g` over the
fresh sample equals the credit `CreditV`. The Rocq proof is `is_RInt (g F N x) 0 1
(CreditV F N x)`; here it is a `lintegral` over `unifUnit = volume.restrict [0,1]`.
Everything is `ENNReal.ofReal` of a polynomial, so the load-bearing steps are Tonelli
(`lintegral_tsum`) and one interval integral of `μ0`. -/

/-- `CreditV` reindexed as a shift: drop the `i ≤ n` guard by summing over `m = n - i`. -/
theorem RealDecrTrialCreditV_reindex (F : ℕ → ℝ≥0∞) (i : ℕ) (x : ℝ) :
    RealDecrTrialCreditV F i x = ∑' m : ℕ, RealDecrTrialμ0 x m * F (i + m) := by
  unfold RealDecrTrialCreditV
  rw [← (add_right_injective i).tsum_eq (f := fun n => RealDecrTrialμ x i n * F n) ?supp]
  · exact tsum_congr fun m => by
      rw [RealDecrTrialμ_supp (Nat.le_add_right i m), Nat.add_sub_cancel_left]
  · intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    have hin : i ≤ n := by
      by_contra h
      exact hn (by rw [RealDecrTrialμ_not_supp (by omega), zero_mul])
    exact ⟨n - i, by show i + (n - i) = n; omega⟩

open MeasureTheory in
/-- The `μ0` interval integral: `∫₀ᵗ (yᵐ/m! − y^{m+1}/(m+1)!) dy = t^{m+1}/(m+1)! − t^{m+2}/(m+2)!`. -/
theorem RealDecrTrialμ0_real_integral (m : ℕ) (t : ℝ) :
    ∫ y in (0 : ℝ)..t, (y ^ m / (m.factorial : ℝ) - y ^ (m + 1) / ((m + 1).factorial : ℝ))
      = t ^ (m + 1) / ((m + 1).factorial : ℝ) - t ^ (m + 2) / ((m + 2).factorial : ℝ) := by
  have h0 : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have e3 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have e4 : ((m : ℝ) + 2) ≠ 0 := by positivity
  rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_div, intervalIntegral.integral_div,
      integral_pow, integral_pow, zero_pow (by omega), zero_pow (by omega),
      show ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) by
        rw [Nat.factorial_succ]; push_cast; ring,
      show ((m + 2).factorial : ℝ) = ((m : ℝ) + 2) * (((m : ℝ) + 1) * (m.factorial : ℝ)) by
        rw [show m + 2 = (m + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ];
        push_cast; ring]
  push_cast
  field_simp
  ring

open MeasureTheory in
/-- The `μ0` Lebesgue integral over `[0,x]`: it advances the index by one. -/
theorem RealDecrTrialμ0_setLIntegral {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) (m : ℕ) :
    ∫⁻ y in Set.Icc 0 x, RealDecrTrialμ0 y m ∂volume = RealDecrTrialμ0 x (m + 1) := by
  have hcont : Continuous fun y : ℝ =>
      y ^ m / (m.factorial : ℝ) - y ^ (m + 1) / ((m + 1).factorial : ℝ) := by fun_prop
  have hm0 : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc 0 x)]
      fun y : ℝ => y ^ m / (m.factorial : ℝ) - y ^ (m + 1) / ((m + 1).factorial : ℝ) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun y hy => ?_)
    show (0 : ℝ) ≤ y ^ m / (m.factorial : ℝ) - y ^ (m + 1) / ((m + 1).factorial : ℝ)
    have hy0 : 0 ≤ y := hy.1
    have hy1 : y ≤ 1 := _root_.le_trans hy.2 hx.2
    have hf1 : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hrw : y ^ (m + 1) / ((m + 1).factorial : ℝ)
        = (y ^ m / (m.factorial : ℝ)) * (y / ((m : ℝ) + 1)) := by
      rw [hf1, pow_succ]; field_simp
    rw [sub_nonneg, hrw]
    have hnn1 : 0 ≤ y ^ m / (m.factorial : ℝ) := by positivity
    have hyle : y / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) m]
    exact mul_le_of_le_one_right hnn1 hyle
  simp only [RealDecrTrialμ0]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc) hnn,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx.1,
      RealDecrTrialμ0_real_integral]

open MeasureTheory in
/-- Credit conservation. Rocq `g_expectation` states `is_RInt (g F N x) 0 1
(CreditV F N x)`; restated here as a `lintegral` over the uniform-unit measure —
exactly the hypothesis `twp_urand_exp` consumes when distributing
`↯(CreditV F N x)` across the freshly sampled real. -/
theorem RealDecrTrialg_lintegral {F : ℕ → ℝ≥0∞} {M : ℝ≥0∞} {N : ℕ} {x : ℝ}
    (Hx : 0 ≤ x ∧ x ≤ 1) (Hbound : ∀ n, F n ≤ M) :
    ∫⁻ y, RealDecrTrialg F N x y ∂(ProbLangℝ.unifUnit (T := ℝ)) =
      RealDecrTrialCreditV F N x := by
  obtain ⟨hx0, hx1⟩ := Hx
  have hset2 : Set.Ici x ∩ Set.Icc (0 : ℝ) 1 = Set.Icc x 1 := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
    exact ⟨fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, _root_.le_trans hx0 h1, h2⟩⟩
  have hset1 : Set.Iic x ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 x := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun ⟨h2, h1, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, _root_.le_trans h2 hx1⟩⟩
  show ∫⁻ y, RealDecrTrialg F N x y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = _
  simp only [RealDecrTrialg]
  rw [lintegral_add_left
        (Measurable.ite measurableSet_Iic (RealDecrTrialCreditV_measurable F (N + 1))
          measurable_const)]
  -- Part 2: the `[x ≤ y]·F N` term integrates to `F N · ofReal (1-x) = F N · μ0 x 0`.
  have hpart2 : (∫⁻ y, (if x ≤ y then F N else 0) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      = F N * RealDecrTrialμ0 x 0 := by
    rw [show (fun y => if x ≤ y then F N else 0)
          = (Set.Ici x).indicator (fun _ => F N) from by
        ext y; rw [Set.indicator_apply]; simp [Set.mem_Ici],
      lintegral_indicator measurableSet_Ici, setLIntegral_const,
      Measure.restrict_apply measurableSet_Ici, hset2, Real.volume_Icc]
    rw [RealDecrTrialμ0]; norm_num
  -- Part 1: the `[y ≤ x]·CreditV F (N+1) y` term.
  have hpart1 : (∫⁻ y, (if y ≤ x then RealDecrTrialCreditV F (N + 1) y else 0)
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      = ∑' m : ℕ, RealDecrTrialμ0 x (m + 1) * F (N + 1 + m) := by
    rw [show (fun y => if y ≤ x then RealDecrTrialCreditV F (N + 1) y else 0)
          = (Set.Iic x).indicator (RealDecrTrialCreditV F (N + 1)) from by
        ext y; rw [Set.indicator_apply]; simp [Set.mem_Iic],
      lintegral_indicator measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic, hset1]
    simp only [RealDecrTrialCreditV_reindex]
    rw [lintegral_tsum (fun m => ((RealDecrTrialμ0_measurable m).mul_const (F (N + 1 + m))).aemeasurable)]
    exact tsum_congr fun m => by
      rw [lintegral_mul_const _ (RealDecrTrialμ0_measurable m),
        RealDecrTrialμ0_setLIntegral ⟨hx0, hx1⟩ m]
  rw [hpart1, hpart2, RealDecrTrialCreditV_reindex,
      tsum_eq_zero_add' (f := fun m => RealDecrTrialμ0 x m * F (N + m)) ENNReal.summable,
      Nat.add_zero,
      add_comm (∑' m : ℕ, RealDecrTrialμ0 x (m + 1) * F (N + 1 + m)) (F N * RealDecrTrialμ0 x 0),
      mul_comm (F N) (RealDecrTrialμ0 x 0)]
  congr 1
  exact tsum_congr fun m => by rw [show N + (m + 1) = N + 1 + m from by omega]

open MeasureTheory in
/-- The amplified integral: the extra `[y < x]·c` term contributes `c · ofReal x`
(the measure of the recursion region `[0,x)`). -/
theorem RealDecrTrialgAmp_lintegral {F : ℕ → ℝ≥0∞} {M : ℝ≥0∞} {N : ℕ} {x : ℝ} {c : ℝ≥0∞}
    (Hx : 0 ≤ x ∧ x ≤ 1) (Hbound : ∀ n, F n ≤ M) :
    ∫⁻ y, RealDecrTrialgAmp F N x c y ∂(ProbLangℝ.unifUnit (T := ℝ)) =
      RealDecrTrialCreditV F N x + c * ENNReal.ofReal x := by
  obtain ⟨hx0, hx1⟩ := Hx
  have hset : Set.Iio x ∩ Set.Icc (0 : ℝ) 1 = Set.Ico 0 x := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
    exact ⟨fun ⟨h2, h1, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, _root_.le_trans h2.le hx1⟩⟩
  show ∫⁻ y, RealDecrTrialgAmp F N x c y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = _
  simp only [RealDecrTrialgAmp]
  rw [lintegral_add_left (RealDecrTrialg_measurable F N x)]
  congr 1
  · exact RealDecrTrialg_lintegral ⟨hx0, hx1⟩ Hbound
  · rw [show (fun y => if y < x then c else 0) = (Set.Iio x).indicator (fun _ => c) from by
          ext y; rw [Set.indicator_apply]; simp [Set.mem_Iio],
        lintegral_indicator measurableSet_Iio, setLIntegral_const,
        Measure.restrict_apply measurableSet_Iio, hset, Real.volume_Ico, sub_zero]

/-! ### Parity of the `DecrTrial` result

The `DecrTrial` process started at `0` returns an **even** count with probability
`exp(-x)` and an **odd** count with probability `1 - exp(-x)`: the even/odd sums of the
telescoping `μ0` densities are the `cosh ∓ sinh = exp(∓x)` series. This is the closed form
(`Hclosed`) consumed by `NegExp`/`HalfBernNegExp`. -/

/-- Each `μ0` real value is nonnegative on `[0,1]` (`y^m/m!` dominates `y^{m+1}/(m+1)!`). -/
theorem RealDecrTrialμ0_real_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    0 ≤ x ^ n / (n.factorial : ℝ) - x ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hf1 : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hrw : x ^ (n + 1) / ((n + 1).factorial : ℝ)
      = (x ^ n / (n.factorial : ℝ)) * (x / ((n : ℝ) + 1)) := by
    rw [hf1, pow_succ]; field_simp
  rw [sub_nonneg, hrw]
  have hnn1 : 0 ≤ x ^ n / (n.factorial : ℝ) := by positivity
  have hyle : x / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
  exact mul_le_of_le_one_right hnn1 hyle

/-- Even- and odd-indexed telescoping sums of `μ0` real values: `exp(-x)` and `1 - exp(-x)`. -/
theorem RealDecrTrialμ0_real_parity (x : ℝ) :
    (∑' k : ℕ, (x ^ (2 * k) / ((2 * k).factorial : ℝ) - x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))
      = Real.exp (-x))
    ∧ (∑' k : ℕ, (x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)
        - x ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ)) = 1 - Real.exp (-x)) := by
  have hexp : ∀ y : ℝ, ∑' n, y ^ n / (n.factorial : ℝ) = Real.exp y := fun y => by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hinj2 : Function.Injective (fun k : ℕ => 2 * k) := fun i j h => by first | omega | (dsimp only at h; omega)
  have hinj2' : Function.Injective (fun k : ℕ => 2 * k + 1) := fun i j h => by
    first | omega | (dsimp only at h; omega)
  have he : Summable (fun k => x ^ (2 * k) / ((2 * k).factorial : ℝ)) :=
    (Real.summable_pow_div_factorial x).comp_injective hinj2
  have ho : Summable (fun k => x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) :=
    (Real.summable_pow_div_factorial x).comp_injective hinj2'
  -- `C - S = exp (-x)` (only the difference is needed).
  have hsub : (∑' k, x ^ (2 * k) / ((2 * k).factorial : ℝ))
      - (∑' k, x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) = Real.exp (-x) := by
    have hbe : Summable (fun k => (-x) ^ (2 * k) / ((2 * k).factorial : ℝ)) :=
      (Real.summable_pow_div_factorial (-x)).comp_injective hinj2
    have hbo : Summable (fun k => (-x) ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) :=
      (Real.summable_pow_div_factorial (-x)).comp_injective hinj2'
    have key : (∑' k, (-x) ^ (2 * k) / ((2 * k).factorial : ℝ))
        + (∑' k, (-x) ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) = Real.exp (-x) := by
      rw [← hexp (-x)]
      exact tsum_even_add_odd (f := fun n => (-x) ^ n / (n.factorial : ℝ)) hbe hbo
    have hE : (∑' k, (-x) ^ (2 * k) / ((2 * k).factorial : ℝ))
        = ∑' k, x ^ (2 * k) / ((2 * k).factorial : ℝ) :=
      tsum_congr fun k => by rw [Even.neg_pow (⟨k, by ring⟩ : Even (2 * k)) x]
    have hO : (∑' k, (-x) ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))
        = - ∑' k, x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
      rw [← tsum_neg]; exact tsum_congr fun k => by
        rw [Odd.neg_pow (⟨k, by ring⟩ : Odd (2 * k + 1)) x]; ring
    rw [hE, hO] at key; linarith
  have ho2' : Summable (fun k => x ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ)) :=
    (Real.summable_pow_div_factorial x).comp_injective (fun i j h => by first | omega | (dsimp only at h; omega))
  refine ⟨?_, ?_⟩
  · have hsplit : (∑' k : ℕ, (x ^ (2 * k) / ((2 * k).factorial : ℝ)
          - x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)))
        = (∑' k, x ^ (2 * k) / ((2 * k).factorial : ℝ))
          - ∑' k, x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := he.tsum_sub ho
    rw [hsplit]; linarith [hsub]
  · -- odd telescoping: `S - (C - a₀) = 1 - exp(-x)`, with `a₀ = 1`.
    have hshift : (∑' k, x ^ (2 * k) / ((2 * k).factorial : ℝ))
        = 1 + ∑' k, x ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ) := by
      rw [show (∑' k, x ^ (2 * k) / ((2 * k).factorial : ℝ))
            = x ^ (2 * 0) / ((2 * 0).factorial : ℝ)
              + ∑' k, x ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ) from he.tsum_eq_zero_add,
          show (∑' k, x ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ))
            = ∑' k, x ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ)
          from tsum_congr fun k => by rw [show 2 * (k + 1) = 2 * k + 2 from by ring]]
      norm_num
    have hsplit : (∑' k : ℕ, (x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)
          - x ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ)))
        = (∑' k, x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))
          - ∑' k, x ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ) := ho.tsum_sub ho2'
    rw [hsplit]; linarith [hshift, hsub]

/-- Parity credit: `DecrTrial` from `0` charges `A` on even results (prob `exp(-x)`) and
`B` on odd (prob `1 - exp(-x)`). -/
theorem RealDecrTrialCreditV_parity (A B : ℝ≥0∞) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    RealDecrTrialCreditV (fun n => if n % 2 = 0 then A else B) 0 x
      = ENNReal.ofReal (Real.exp (-x)) * A + ENNReal.ofReal (1 - Real.exp (-x)) * B := by
  obtain ⟨hpe, hpo⟩ := RealDecrTrialμ0_real_parity x
  have hinj2 : Function.Injective (fun k : ℕ => 2 * k) := fun i j h => by first | omega | (dsimp only at h; omega)
  have hinj2' : Function.Injective (fun k : ℕ => 2 * k + 1) := fun i j h => by
    first | omega | (dsimp only at h; omega)
  have hinj2'' : Function.Injective (fun k : ℕ => 2 * k + 2) := fun i j h => by
    first | omega | (dsimp only at h; omega)
  -- The ℝ≥0∞ even/odd `μ0` sums are `ofReal` of the real telescoping sums.
  have hEven : (∑' k : ℕ, RealDecrTrialμ0 x (2 * k)) = ENNReal.ofReal (Real.exp (-x)) := by
    rw [← hpe, ENNReal.ofReal_tsum_of_nonneg (fun k => RealDecrTrialμ0_real_nonneg hx0 hx1 (2 * k))
      (((Real.summable_pow_div_factorial x).comp_injective hinj2).sub
        ((Real.summable_pow_div_factorial x).comp_injective hinj2'))]
    rfl
  have hOdd : (∑' k : ℕ, RealDecrTrialμ0 x (2 * k + 1)) = ENNReal.ofReal (1 - Real.exp (-x)) := by
    rw [← hpo, ENNReal.ofReal_tsum_of_nonneg (fun k => RealDecrTrialμ0_real_nonneg hx0 hx1 (2 * k + 1))
      (((Real.summable_pow_div_factorial x).comp_injective hinj2').sub
        ((Real.summable_pow_div_factorial x).comp_injective hinj2''))]
    rfl
  unfold RealDecrTrialCreditV
  simp only [RealDecrTrialμ_base]
  rw [← tsum_even_add_odd (f := fun n => RealDecrTrialμ0 x n * if n % 2 = 0 then A else B)
        ENNReal.summable ENNReal.summable]
  congr 1
  · rw [tsum_congr (fun k => by rw [if_pos (show (2 * k) % 2 = 0 by omega)] :
          ∀ k : ℕ, RealDecrTrialμ0 x (2 * k) * (if (2 * k) % 2 = 0 then A else B)
            = RealDecrTrialμ0 x (2 * k) * A), ENNReal.tsum_mul_right, hEven]
  · rw [tsum_congr (fun k => by rw [if_neg (show ¬ (2 * k + 1) % 2 = 0 by omega)] :
          ∀ k : ℕ, RealDecrTrialμ0 x (2 * k + 1) * (if (2 * k + 1) % 2 = 0 then A else B)
            = RealDecrTrialμ0 x (2 * k + 1) * B), ENNReal.tsum_mul_right, hOdd]

/-- Fixed-factor tail of `DecrTrial`: once the threshold `x` is capped by some
`B < 1`, the recursion probability `≤ B`, so a single amplification factor
`k = 1/B > 1` drives the termination induction (à la `BernoulliGeometric`). -/
theorem twp_DecrTrial_tail (E : CoPset) (F : ℕ → ℝ≥0∞) (M : ℝ≥0∞) (Hnn : ∀ n, F n ≤ M)
    (B : ℝ) (hB0 : 0 < B) (hB1 : B < 1) :
    ⊢@{IProp GF} ∀ (N : ℕ) (x : ℝ), ⌜0 ≤ x⌝ -∗ ⌜x ≤ B⌝ -∗
      ↯ (RealDecrTrialCreditV F N x) -∗
      tglWp E pl(&DecrTrial #(.int (N : ℤ)) #(.real x))
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  have hkpos : (0 : ℝ) ≤ 1 / B := by positivity
  set k : ℝ≥0 := ⟨1 / B, hkpos⟩ with hk_def
  have Hk1 : 1 < k := by
    have h : (1 : ℝ) < 1 / B := by rw [lt_div_iff₀ hB0]; linarith
    exact_mod_cast h
  iintro %N %x %Hx0 %HxB Hε_spec
  -- Fresh termination credit + amplification induction with factor `k = 1/B`.
  iapply twp_err_pos solve_not_red
  iintro %ε_term %Hε_pos Hε_term
  irevert Hε_spec
  irevert %HxB
  irevert %Hx0
  irevert %x
  irevert %N
  iapply ErrorCredit.Induction.simple (k := k) Hε_pos Hk1 $$ [] Hε_term
  imodintro
  iintro ⟨IH, Hε_term⟩ %N %x %Hx0 %HxB Hε_spec
  -- Expose `let y := urand` with bounded single steps (unfold rec + 2 β-args).
  twp_pure
  twp_pure
  twp_pure
  twp_bind pl(urand)
  -- Distribute credit + `k·ε_term` on `{y < x}` across the fresh sample.
  icombine Hε_spec Hε_term as Hε
  iapply (twp_urand_exp'
    (ε₂ := RealDecrTrialgAmp F N x ((k : ℝ≥0∞) * ε_term)) ?hmeas ?hint) $$ Hε
  case hmeas => exact RealDecrTrialgAmp_measurable F N x _
  case hint =>
    rw [RealDecrTrialgAmp_lintegral ⟨Hx0, _root_.le_trans HxB hB1.le⟩ Hnn]
    have hkx : (↑k : ℝ≥0∞) * ENNReal.ofReal x ≤ 1 := by
      rw [show (↑k : ℝ≥0∞) = ENNReal.ofReal (1 / B) from by
            rw [hk_def, ← ENNReal.ofReal_coe_nnreal]; rfl,
          ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_one,
          div_mul_eq_mul_div, one_mul, div_le_one hB0]
      exact HxB
    gcongr
    calc (↑k * ε_term) * ENNReal.ofReal x
        = ε_term * ((↑k : ℝ≥0∞) * ENNReal.ofReal x) := by ring
      _ ≤ ε_term * 1 := mul_le_mul_left' hkx ε_term
      _ = ε_term := mul_one _
  iintro %y ⟨%Hym, Hcy⟩
  have Hym01 : 0 < y ∧ y < 1 := mem_unifUnitSupport_real.mp Hym
  have Hyr : 0 ≤ y ∧ y ≤ 1 := ⟨Hym01.1.le, Hym01.2.le⟩
  -- Reduce the `let` and evaluate `y < x` to `.bool (realLt y x)` — the stepper now keeps
  -- `realLt` folded (a symbolic real comparison no longer over-reduces to an opaque
  -- classical `Decidable.rec`), so we can just `rcases` on it; each branch fires the `cond`.
  twp_pures
  rcases hb : ProbLangℝ.realLt y x with _ | _
  · -- `realLt y x = false`, i.e. `¬ y < x`: terminal branch returns `N`, credit `F N`.
    twp_pures
    twp_value
    imodintro
    iexists N
    have hle : F N ≤ RealDecrTrialgAmp F N x ((k : ℝ≥0∞) * ε_term) y := by
      have hnlt : ¬ y < x := of_decide_eq_false hb
      have hxy : x ≤ y := _root_.not_lt.mp hnlt
      unfold RealDecrTrialgAmp RealDecrTrialg
      rw [if_pos hxy, if_neg hnlt, add_zero]
      exact le_add_self
    isplitr [Hcy]
    · ipureintro; rfl
    · iapply (ErrorCredit.weaken hle); iexact Hcy
  · -- `realLt y x = true`, i.e. `y < x`: recurse `DecrTrial (N+1) y` via `IH` (`y ≤ x ≤ B`).
    have hlt' : y < x := of_decide_eq_true hb
    twp_pure
    ihave Hcy' : iprop(↯ (RealDecrTrialCreditV F (N + 1) y + (k : ℝ≥0∞) * ε_term)) $$ [Hcy]
    · rw [show RealDecrTrialCreditV F (N + 1) y + (k : ℝ≥0∞) * ε_term
            = RealDecrTrialgAmp F N x ((k : ℝ≥0∞) * ε_term) y from by
          unfold RealDecrTrialgAmp RealDecrTrialg
          rw [if_pos hlt'.le, if_neg (_root_.not_le.mpr hlt'), if_pos hlt', add_zero]]  -- `gAmp` reshaping at `y < x`
      iexact Hcy
    ihave ⟨Hexp, Hterm⟩ := ErrorCredit.split (GF := GF) $$ Hcy'
    twp_pure
    rw [show ((N : ℤ) + 1) = ((N + 1 : ℕ) : ℤ) from by push_cast; ring]
    twp_bind pl(&DecrTrial #(.int ((N + 1 : ℕ) : ℤ)) #(.real y))
    iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ n : ℕ,
      ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))))
    isplitl [Hexp Hterm IH]
    · iapply IH $$ Hterm
      · ipureintro; linarith [Hyr.1]
      · ipureintro; linarith [hlt'.le, HxB]
      · iexact Hexp
    iintro %w Hpost
    iapply tglWp_value
    iexact Hpost

theorem twp_DecrTrial (E : CoPset) (F : ℕ → ℝ≥0∞) (M : ℝ≥0∞) (Hnn : ∀ n, F n ≤ M)
    (N : ℕ) (x : ℝ) (Hx : 0 ≤ x ∧ x ≤ 1) :
    ⊢@{IProp GF} ↯ (RealDecrTrialCreditV F N x) -∗
      tglWp E pl(&DecrTrial #(.int (N : ℤ)) #(.real x))
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  iintro Hε_spec
  -- Peel the first draw `y₀` (no amplification): the ordinary credit `RealDecrTrialg`.
  twp_pure
  twp_pure
  twp_pure
  twp_bind pl(urand)
  iapply (twp_urand_exp' (ε₂ := RealDecrTrialg F N x) ?hmeas ?hint) $$ Hε_spec
  case hmeas => exact RealDecrTrialg_measurable F N x
  case hint => exact _root_.le_of_eq (RealDecrTrialg_lintegral Hx Hnn)
  iintro %y ⟨%Hym, Hcy⟩
  have Hym01 : 0 < y ∧ y < 1 := mem_unifUnitSupport_real.mp Hym
  have Hyr : 0 ≤ y ∧ y ≤ 1 := ⟨Hym01.1.le, Hym01.2.le⟩
  twp_pures
  rcases hb : ProbLangℝ.realLt y x with _ | _
  · -- `¬ y₀ < x`: terminal branch returns `N`, credit `F N`.
    twp_pures
    twp_value
    imodintro
    iexists N
    have hle : F N ≤ RealDecrTrialg F N x y := by
      have hxy : x ≤ y := _root_.not_lt.mp (of_decide_eq_false hb)
      unfold RealDecrTrialg
      rw [if_pos hxy]
      exact le_add_self
    isplitr [Hcy]
    · ipureintro; rfl
    · iapply (ErrorCredit.weaken hle); iexact Hcy
  · -- `y₀ < x`: the new threshold `y₀ < x ≤ 1` is `< 1`, so hand off to the
    -- fixed-factor tail with `B := y₀` (every later threshold stays `≤ y₀`).
    have hlt' : y < x := of_decide_eq_true hb
    twp_pure
    ihave Hcy' : iprop(↯ (RealDecrTrialCreditV F (N + 1) y)) $$ [Hcy]
    · rw [show RealDecrTrialCreditV F (N + 1) y = RealDecrTrialg F N x y from by
          unfold RealDecrTrialg
          rw [if_pos hlt'.le, if_neg (_root_.not_le.mpr hlt'), add_zero]]  -- `g y = CreditV F (N+1) y` at `y < x`
      iexact Hcy
    have hy1 : y < 1 := _root_.lt_of_lt_of_le hlt' Hx.2
    have hy0 : 0 < y := Hym01.1
    twp_pure
    rw [show ((N : ℤ) + 1) = ((N + 1 : ℕ) : ℤ) from by push_cast; ring]
    twp_bind pl(&DecrTrial #(.int ((N + 1 : ℕ) : ℤ)) #(.real y))
    iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ n : ℕ,
      ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))))
    isplitl [Hcy']
    · iapply (twp_DecrTrial_tail E F M Hnn y hy0 hy1)
      · ipureintro; exact Hyr.1
      · ipureintro; exact _root_.le_refl y
      · iexact Hcy'
    iintro %w Hpost
    iapply tglWp_value
    iexact Hpost

end
end Examples
end TotalEris
end ProbLang
