module

public import Metrology.TotalEris
public import Metrology.ProbLang.Reals
public import Metrology.TotalEris.Examples.Samplers.RealDecrTrial

@[expose] public section

/-!
# Index selector

Combinators that pick the integer part of a Gaussian sample.

* `C m` chooses `0`, `1`, or `2` from a discrete `rand` (the only place a
  *discrete* sampler survives — the `{0,1,2}` selection is genuinely finite).
* `Bii k x`, `S`, `S0`, `B` are the continuous pieces: they compare the shared
  uniform `x` against fresh `urand` draws.
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang
  ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
open MeasureTheory (lintegral_add_left lintegral_const lintegral_const_mul'
  lintegral_indicator lintegral_mul_const lintegral_piecewise lintegral_tsum
  setLIntegral_congr_fun setLIntegral_const volume measure_univ)
open MeasureTheory.Measure (restrict_apply restrict_restrict)
open scoped AppGS ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [ErisGS ℝ hlc GF]

/-! ## Program -/

section program

/-- `C m`: draw from `rand (m+2)` and collapse the outcome to `0`, `1`, or `2`. -/
@[pl_fold]
def C : Exp ℝ := pl%
  fun m, let v := rand(m + #2, #.unit); if v = #0 then #0 else if v = #1 then #1 else #2

/-- `Bii k x`: boolean gate `(C (2k) = 0) ‖ ((C (2k) = 1) ∧ (x < urand))` with a
fresh `urand` draw. The disjunction short-circuits, so `Bii` samples only when
`C (2k) ≠ 0`. -/
@[pl_fold]
def Bii : Exp ℝ := pl%
  fun k, fun x,
    let f := &C (#2 * k);
    let r := urand;
    if f = #0 then #true else (if f = #1 then (x < r) else #false)

/-- `S k x y N`: rejection loop — draw `z`; return `N` if `y < z` or `Bii k x`,
else recurse at threshold `z` with index `N+1`. -/
@[pl_fold]
def S : Exp ℝ := pl%
  rec trial k x y N :=
    let z := urand;
    if y < z then N else (if &Bii k x then N else trial k x z (N + #1))

/-- `S0 k x`: first-draw wrapper of `S` — draw `z`; return `#0` if `x < z` or
`Bii k x`, else recurse into `S k x z 1`. -/
@[pl_fold]
def S0 : Exp ℝ := pl%
  fun k, fun x,
    let z := urand;
    if x < z then #0 else (if &Bii k x then #0 else &S k x z #1)

/-- `B k x`: parity of `S0 k x` — returns `S0 k x rem 2 = 0`. -/
@[pl_fold]
def B : Exp ℝ := pl%
  fun k, fun x, (&S0 k x % #2 = #0)

end program

/-! ## Distribution -/

section distribution

/-- Outcome measure for `Bii k x`: `μ true = 1 - (2k+x)/(2k+2)`,
`μ false = (2k+x)/(2k+2)`. -/
def BiiPMF (k : ℕ) (x : ℝ) : Bool → ℝ≥0∞
  | true => .ofReal (1 - (2 * (k : ℝ) + x) / (2 * k + 2))
  | false => .ofReal ((2 * (k : ℝ) + x) / (2 * k + 2))

/-- The `S`-loop PMF core: the difference of two successive `DecrTrial` masses at
the scaled point `y·(2k+x)/(2k+2)`. -/
def SPMF₀ (k : ℕ) (x y : ℝ) (n : ℕ) : ℝ≥0∞ :=
  .ofReal ((y ^ n / n.factorial) * ((2 * (k : ℝ) + x) / (2 * k + 2)) ^ n -
    (y ^ (n + 1) / (n + 1).factorial) * ((2 * (k : ℝ) + x) / (2 * k + 2)) ^ (n + 1))

/-- The `S`-loop PMF, masked to `n ≥ N`: `[N ≤ n] · SPMF₀ k x y (n - N)`. -/
def SPMF (k : ℕ) (x y : ℝ) (N n : ℕ) : ℝ≥0∞ :=
  if N ≤ n then SPMF₀ k x y (n - N) else 0

/-- `SPMF₀` is exactly the `DecrTrial` PMF at the scaled point `y·(2k+x)/(2k+2)`. -/
theorem SPMF₀_eq_RealDecrTrialPMF₀ (k : ℕ) (x y : ℝ) (n : ℕ) :
    SPMF₀ k x y n = RealDecrTrialPMF₀ (y * ((2 * (k : ℝ) + x) / (2 * k + 2))) n := by
  unfold SPMF₀ RealDecrTrialPMF₀
  congr 1
  rw [mul_pow, mul_pow]; ring

/-- The `SPMF₀` Lebesgue integral over `[0,y]`, pre-multiplied by the factor `q`, advances
the index by one (the `S`-analogue of `RealDecrTrialPMF₀_setLIntegral`; the running
threshold `z` scales by `q` inside the `DecrTrial` PMF). -/
theorem SPMF₀_q_setLIntegral (k : ℕ) {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) (m : ℕ) :
    ENNReal.ofReal ((2 * (k : ℝ) + x) / (2 * k + 2)) * (∫⁻ z in Set.Icc 0 y, SPMF₀ k x z m ∂volume)
      = SPMF₀ k x y (m + 1) := by
  have hqnn : (0 : ℝ) ≤ (2 * (k : ℝ) + x) / (2 * k + 2) :=
    div_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
  have hq1 : (2 * (k : ℝ) + x) / (2 * k + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hbridge : (∫⁻ z in Set.Icc 0 y, SPMF₀ k x z m ∂volume)
      = ENNReal.ofReal (∫ z in (0 : ℝ)..y,
          ((z * ((2 * (k : ℝ) + x) / (2 * k + 2))) ^ m / (m.factorial : ℝ)
            - (z * ((2 * (k : ℝ) + x) / (2 * k + 2))) ^ (m + 1) / ((m + 1).factorial : ℝ))) := by
    rw [← lintegral_ofReal_Icc hy0 (by fun_prop) (fun z hz =>
          RealDecrTrialPMF₀_real_nonneg (mul_nonneg hz.1 hqnn)
            (mul_le_one₀ (_root_.le_trans hz.2 hy1) hqnn hq1) m)]
    refine setLIntegral_congr_fun measurableSet_Icc (fun z hz => ?_)
    rw [SPMF₀_eq_RealDecrTrialPMF₀]; rfl
  have hint : (∫ z in (0 : ℝ)..y,
        ((z * ((2 * (k : ℝ) + x) / (2 * k + 2))) ^ m / (m.factorial : ℝ)
          - (z * ((2 * (k : ℝ) + x) / (2 * k + 2))) ^ (m + 1) / ((m + 1).factorial : ℝ)))
      = ((2 * (k : ℝ) + x) / (2 * k + 2)) ^ m * y ^ (m + 1) / (m + 1).factorial
        - ((2 * (k : ℝ) + x) / (2 * k + 2)) ^ (m + 1) * y ^ (m + 2) / (m + 2).factorial := by
    have h0 : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [mul_pow]
    have hcm0 : (fun z => z ^ m * ((2 * (k : ℝ) + x) / (2 * k + 2)) ^ m / (m.factorial : ℝ))
        = (fun z => ((2 * (k : ℝ) + x) / (2 * k + 2)) ^ m / (m.factorial : ℝ) * z ^ m) := by
      funext z; ring
    have hcm1 : (fun z => z ^ (m + 1) * ((2 * (k : ℝ) + x) / (2 * k + 2)) ^ (m + 1)
          / ((m + 1).factorial : ℝ))
        = (fun z => ((2 * (k : ℝ) + x) / (2 * k + 2)) ^ (m + 1) / ((m + 1).factorial : ℝ)
            * z ^ (m + 1)) := by
      funext z; ring
    rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _),
        hcm0, hcm1,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_pow, integral_pow, zero_pow (by omega), zero_pow (by omega)]
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  rw [hbridge, hint, ← ENNReal.ofReal_mul hqnn]
  unfold SPMF₀
  congr 1
  ring

end distribution

/-! ## Credit expectation -/

section creditExpectation

/-- Distribution credit for `C`:
`1/(m+2) · F 0 + 1/(m+2) · F 1 + m/(m+2) · F 2`. -/
def CCreditV (F : ℕ → ℝ≥0∞) (m : ℕ) : ℝ≥0∞ :=
  .ofReal (1 / ((m : ℝ) + 2)) * F 0 + .ofReal (1 / ((m : ℝ) + 2)) * F 1 +
  .ofReal ((m : ℝ) / ((m : ℝ) + 2)) * F 2

/-- Distribution credit for `Bii k x`: `μ false · F false + μ true · F true`. -/
def BiiCreditV (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  BiiPMF k x false * F false + BiiPMF k x true * F true

/-- Distribution credit for `S`: `∑ₙ SPMF k x y N n · F n`. -/
def SCreditV (F : ℕ → ℝ≥0∞) (k : ℕ) (x y : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ, SPMF k x y N n * F n

/-- Distribution credit for `B`:
`exp(-x(2k+x)/(2k+2)) · F true + (1 - exp(…)) · F false`. -/
def BCreditV (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  .ofReal (Real.exp (-x * (2 * k + x) / (2 * k + 2))) * F true +
  (1 - .ofReal (Real.exp (-x * (2 * k + x) / (2 * k + 2)))) * F false

/-- `SCreditV` is the `DecrTrial` credit at the scaled point `y·(2k+x)/(2k+2)`. -/
theorem SCreditV_eq_RealDecrTrialCreditV (F : ℕ → ℝ≥0∞) (k : ℕ) (x y : ℝ) (N : ℕ) :
    SCreditV F k x y N = RealDecrTrialCreditV F N (y * ((2 * (k : ℝ) + x) / (2 * k + 2))) := by
  unfold SCreditV RealDecrTrialCreditV
  refine tsum_congr fun n => ?_
  congr 1
  unfold SPMF RealDecrTrialPMF
  by_cases h : N ≤ n
  · rw [if_pos h, if_pos h, SPMF₀_eq_RealDecrTrialPMF₀]
  · rw [if_neg h, if_neg h]

/-- Peel the `N`-th (answer) term off `SCreditV`: coefficient `1 - qy` on `F N`. -/
theorem SCreditV_peel (F : ℕ → ℝ≥0∞) (k : ℕ) (x y : ℝ) (N : ℕ) :
    SCreditV F k x y N
      = ENNReal.ofReal (1 - (2 * (k : ℝ) + x) / (2 * k + 2) * y) * F N
        + ∑' m : ℕ, SPMF₀ k x y (m + 1) * F (N + 1 + m) := by
  rw [SCreditV_eq_RealDecrTrialCreditV, RealDecrTrialCreditV_reindex,
      tsum_eq_zero_add' (f := fun m => RealDecrTrialPMF₀ (y * ((2 * (k : ℝ) + x) / (2 * k + 2))) m
        * F (N + m)) ENNReal.summable]
  congr 1
  · rw [Nat.add_zero]
    congr 1
    unfold RealDecrTrialPMF₀
    congr 1
    simp only [pow_zero, pow_one, zero_add, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
      div_one]
    ring
  · exact tsum_congr fun m => by
      have hidx : N + (m + 1) = N + 1 + m := by omega
      rw [← SPMF₀_eq_RealDecrTrialPMF₀, hidx]

end creditExpectation

/-! ## Credit kernel -/

section creditKernel

/-- Per-outcome credit for the discrete `rand (m+2)` in `C`: outcome `0 ↦ F 0`,
`1 ↦ F 1`, everything else (`2 … m+1`) `↦ F 2` (all collapse to result `2`). -/
def CCredit (F : ℕ → ℝ≥0∞) : ℕ → ℝ≥0∞ :=
  fun j => if j = 0 then F 0 else if j = 1 then F 1 else F 2

/-- Sum of the `C` per-outcome credits over the `m+2` outcomes: outcome `0 ↦ F 0`,
`1 ↦ F 1`, and the remaining `m` outcomes (`2 … m+1`) each `↦ F 2`. -/
theorem CCredit_sum (F : ℕ → ℝ≥0∞) (m : ℕ) :
    ∑ n ∈ Finset.range (m + 2), CCredit F n = F 0 + F 1 + (m : ℝ≥0∞) * F 2 := by
  induction m with
  | zero => simp [Finset.sum_range_succ, CCredit]
  | succ k ih =>
    have hk2 : CCredit F (k + 2) = F 2 := by simp [CCredit]
    rw [add_right_comm, Finset.sum_range_succ, ih, hk2]
    push_cast; ring

/-- The `HSum` obligation of `twp_rand_exp` for `C`: the averaged per-outcome
credit equals `CCreditV F m`. Stated as `≤` (with equality) to match
`twp_rand_exp`. -/
theorem C_HSum (F : ℕ → ℝ≥0∞) (m : ℕ) :
    (∑ n ∈ Finset.range ((m : ℤ) + 2).toNat, CCredit F n)
        / (((m : ℤ) + 2).toNat : ENNReal) ≤ CCreditV F m := by
  have hz : ((m : ℤ) + 2).toNat = m + 2 := by omega
  have hpos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hd : ENNReal.ofReal ((m : ℝ) + 2) = ((m + 2 : ℕ) : ℝ≥0∞) := by
    have h : (m : ℝ) + 2 = ((m + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [h, ENNReal.ofReal_natCast]
  have hinv : ENNReal.ofReal (1 / ((m : ℝ) + 2)) = ((m + 2 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [one_div, ENNReal.ofReal_inv_of_pos hpos, hd]
  have hmm : ENNReal.ofReal ((m : ℝ) / ((m : ℝ) + 2))
      = (m : ℝ≥0∞) * ((m + 2 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_inv_of_pos hpos, hd]
  have hcv : CCreditV F m
      = (F 0 + F 1 + (m : ℝ≥0∞) * F 2) * ((m + 2 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [CCreditV, hinv, hmm]; ring
  refine _root_.le_of_eq ?_
  rw [hz, CCredit_sum, hcv, div_eq_mul_inv]

/-- The per-`(C-result n, urand-draw r)` cost inside `Bii`: the fresh draw `r` is
taken unconditionally, and `(f=0) ‖ ((f=1) ∧ (x<r))` reads off as `true` when
`n=0`, `x<r` when `n=1`, and `false` when `n≥2`. -/
def BiiCredit (F : Bool → ℝ≥0∞) (x : ℝ) (n : ℕ) (r : ℝ) : ℝ≥0∞ :=
  if n = 0 then F true else if n = 1 then (if x < r then F true else F false) else F false

/-- The credit `C` must return for outcome `n`: the expectation of `BiiCredit`
over the fresh uniform draw `r`. -/
def BiiCCredit (F : Bool → ℝ≥0∞) (x : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ r, BiiCredit F x n r ∂(ProbLangℝ.unifUnit (T := ℝ))

/-- `BiiCCredit` for the three `C`-outcomes: `0 ↦ F true`, `2 ↦ F false`, and the
gated outcome `1 ↦ (1-x)·F true + x·F false` (the fresh draw `r` compared to `x`). -/
theorem BiiCCredit_zero (F : Bool → ℝ≥0∞) (x : ℝ) : BiiCCredit F x 0 = F true := by
  show ∫⁻ r, BiiCredit F x 0 r ∂(ProbLangℝ.unifUnit (T := ℝ)) = F true
  have hfn : (fun r => BiiCredit F x 0 r) = (fun _ => F true) := by funext r; rfl
  rw [hfn, lintegral_const, measure_univ, mul_one]

theorem BiiCCredit_two (F : Bool → ℝ≥0∞) (x : ℝ) : BiiCCredit F x 2 = F false := by
  show ∫⁻ r, BiiCredit F x 2 r ∂(ProbLangℝ.unifUnit (T := ℝ)) = F false
  have hfn : (fun r => BiiCredit F x 2 r) = (fun _ => F false) := by funext r; rfl
  rw [hfn, lintegral_const, measure_univ, mul_one]

/-- `BiiCCredit … 1 = (1-x)·F true + x·F false` (the fresh draw `r` gates `x < r`). -/
theorem BiiCCredit_one (F : Bool → ℝ≥0∞) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    BiiCCredit F x 1 = F true * ENNReal.ofReal (1 - x) + F false * ENNReal.ofReal x := by
  show ∫⁻ r, BiiCredit F x 1 r ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = _
  have hfn : (fun r => BiiCredit F x 1 r) = (fun r => if x < r then F true else F false) := by
    funext r; rfl
  rw [hfn]
  have hsetT : Set.Ioi x ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc x 1 := by
    ext r; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    exact ⟨fun ⟨h2, _, h1⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨h2, _root_.le_trans hx0 h2.le, h1⟩⟩
  have hsetF : Set.Iic x ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 x := by
    ext r; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun ⟨h2, h1, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, _root_.le_trans h2 hx1⟩⟩
  have hdecomp : (fun r => if x < r then F true else F false)
      = (fun r => (Set.Ioi x).indicator (fun _ => F true) r
          + (Set.Iic x).indicator (fun _ => F false) r) := by
    funext r; by_cases h : x < r
    · simp [Set.indicator_apply, h, _root_.not_le.mpr h, _root_.le_of_lt h]
    · simp [Set.indicator_apply, h, _root_.not_lt.mp h]
  rw [hdecomp,
    lintegral_add_left ((measurable_const.indicator measurableSet_Ioi)),
    lintegral_indicator measurableSet_Ioi, lintegral_indicator measurableSet_Iic,
    setLIntegral_const, setLIntegral_const, restrict_apply measurableSet_Ioi,
    restrict_apply measurableSet_Iic, hsetT, hsetF, Real.volume_Ioc, Real.volume_Icc,
    sub_zero]

/-- Credit the nested `Bii` must return (reached only when `z ≤ y`, i.e. the first
disjunct `y<z` was false), as a function of its result `bii`: terminate (cost `F N`)
if `bii` is `true`, else recurse with new threshold `z` (cost `SCreditV … z (N+1)`,
topped up by a termination credit `c`). -/
def SbiiCredit (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) (z : ℝ) (c : ℝ≥0∞) :
    Bool → ℝ≥0∞ :=
  fun bii => if bii then F N else SCreditV F k x z (N + 1) + c

/-- Per-draw credit distributed across the fresh `z ← urand`: if `y < z` the loop
terminates immediately (cost `F N`, `Bii` not run — short-circuit `‖`); otherwise
`Bii` runs with the per-result budget `SbiiCredit`. -/
def SCreditAmp (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) (y : ℝ) (c : ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  fun z => if y < z then F N else BiiCreditV (SbiiCredit F k x N z c) k x

/-- Ordinary (un-amplified) per-draw kernel for `S`: the first draw with zero
termination top-up, `SCreditAmp F k x N y 0`. Mirrors `RealDecrTrialCredit` vs
`RealDecrTrialCreditAmp`. -/
def SCredit (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) (y : ℝ) : ℝ → ℝ≥0∞ :=
  SCreditAmp F k x N y 0

/-- Credit `B` hands to `S0`, read off by parity of the `S0` result: even ↦ `F true`,
odd ↦ `F false` (`B` returns `S0 k x rem 2 = 0`). -/
def BS0credit (F : Bool → ℝ≥0∞) : ℕ → ℝ≥0∞ :=
  fun n => if n % 2 = 0 then F true else F false

end creditKernel

/-! ## Measurability -/

section measurability

/-- `SPMF₀` is `ofReal` of a polynomial in the (running) threshold `y`, hence
measurable in `y`. -/
theorem measurable_sPMF₀ (k : ℕ) (x : ℝ) (n : ℕ) :
    Measurable (fun y : ℝ => SPMF₀ k x y n) :=
  ENNReal.measurable_ofReal.comp (by fun_prop)

/-- `SPMF` is measurable in the running threshold `y` (the `n < N` branch is constant). -/
theorem measurable_sPMF (k : ℕ) (x : ℝ) (N n : ℕ) :
    Measurable (fun y : ℝ => SPMF k x y N n) := by
  unfold SPMF
  by_cases h : N ≤ n
  · simpa only [h, if_true] using measurable_sPMF₀ k x (n - N)
  · simpa only [h, if_false] using measurable_const

/-- `SCreditV` is a `tsum` of `SPMF`-weighted credits, hence measurable in `y`. -/
theorem measurable_sCreditV (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) :
    Measurable (fun y : ℝ => SCreditV F k x y N) :=
  Measurable.tsum fun n => (measurable_sPMF k x N n).mul_const (F n)

/-- Measurability of the per-draw credit (consumed by `twp_urand_exp'`). -/
theorem measurable_sCreditAmp (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) (y : ℝ) (c : ℝ≥0∞) :
    Measurable (SCreditAmp F k x N y c) := by
  unfold SCreditAmp
  refine Measurable.ite measurableSet_Ioi measurable_const ?_
  -- `BiiCreditV (SbiiCredit … z …) k x` = `BiiPMF·(SCreditV … z … + c) + BiiPMF·(F N)`.
  have hred : (fun z : ℝ => BiiCreditV (SbiiCredit F k x N z c) k x)
      = (fun z : ℝ => BiiPMF k x false * (SCreditV F k x z (N + 1) + c)
          + BiiPMF k x true * F N) := by
    funext z; rfl
  rw [hred]
  exact (((measurable_sCreditV F k x (N + 1)).add_const c).const_mul (BiiPMF k x false)).add
    measurable_const

/-- Measurability of the per-outcome cost (consumed by `twp_urand_exp'`). -/
theorem measurable_biiCredit (F : Bool → ℝ≥0∞) (x : ℝ) (n : ℕ) :
    Measurable (BiiCredit F x n) := by
  unfold BiiCredit
  split
  · exact measurable_const
  · split
    · exact Measurable.ite measurableSet_Ioi measurable_const measurable_const
    · exact measurable_const

end measurability

/-! ## Credit conservation -/

section conservation

/-- Integrating the tail credit `SCreditV … (N+1)` over the running threshold `z ∈ [0,y]`,
pre-multiplied by `q`, telescopes into the shifted `SPMF₀`-series. -/
theorem SCreditV_q_setLIntegral (F : ℕ → ℝ≥0∞) (k : ℕ) {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (N : ℕ) :
    ENNReal.ofReal ((2 * (k : ℝ) + x) / (2 * k + 2))
        * (∫⁻ z in Set.Icc 0 y, SCreditV F k x z (N + 1) ∂volume)
      = ∑' m : ℕ, SPMF₀ k x y (m + 1) * F (N + 1 + m) := by
  have hreindex : ∀ z, SCreditV F k x z (N + 1) = ∑' m : ℕ, SPMF₀ k x z m * F (N + 1 + m) := by
    intro z
    rw [SCreditV_eq_RealDecrTrialCreditV, RealDecrTrialCreditV_reindex]
    exact tsum_congr fun m => by rw [← SPMF₀_eq_RealDecrTrialPMF₀]
  have hint : (∫⁻ z in Set.Icc 0 y, SCreditV F k x z (N + 1) ∂volume)
      = ∫⁻ z in Set.Icc 0 y, ∑' m : ℕ, SPMF₀ k x z m * F (N + 1 + m) ∂volume :=
    setLIntegral_congr_fun measurableSet_Icc (fun z _ => hreindex z)
  rw [hint,
    lintegral_tsum (fun m => ((measurable_sPMF₀ k x m).mul_const (F (N + 1 + m))).aemeasurable),
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [lintegral_mul_const _ (measurable_sPMF₀ k x m), ← mul_assoc, SPMF₀_q_setLIntegral k hx0 hx1 hy0 hy1]

/-- Credit conservation for `S` (exact): integrating the amplified per-draw credit over the
fresh `z` recovers `SCreditV` plus the reject-weighted amplification `q·y·c`. -/
theorem SCreditAmp_lintegral_eq (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) (y : ℝ) (c : ℝ≥0∞)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∫⁻ z, SCreditAmp F k x N y c z ∂(ProbLangℝ.unifUnit (T := ℝ))
      = SCreditV F k x y N + ENNReal.ofReal ((2 * (k : ℝ) + x) / (2 * k + 2) * y) * c := by
  have hqnn : (0 : ℝ) ≤ (2 * (k : ℝ) + x) / (2 * k + 2) :=
    div_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
  have hset_ioi : Set.Ioi y ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc y 1 := by
    ext z; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    exact ⟨fun ⟨h2, _, h1⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨h2, _root_.le_trans hy0 h2.le, h1⟩⟩
  have hset_iic : Set.Iic y ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 y := by
    ext z; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun ⟨h2, h1, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, _root_.le_trans h2 hy1⟩⟩
  show ∫⁻ z, SCreditAmp F k x N y c z ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = _
  have hfun : (fun z => SCreditAmp F k x N y c z) = (Set.Ioi y).piecewise (fun _ => F N)
      (fun z => ENNReal.ofReal ((2 * (k : ℝ) + x) / (2 * k + 2)) * SCreditV F k x z (N + 1)
        + (ENNReal.ofReal ((2 * (k : ℝ) + x) / (2 * k + 2)) * c
          + ENNReal.ofReal (1 - (2 * (k : ℝ) + x) / (2 * k + 2)) * F N)) := by
    funext z
    simp only [SCreditAmp, Set.piecewise, Set.mem_Ioi]
    by_cases h : y < z
    · simp only [if_pos h]
    · simp only [if_neg h]
      show BiiCreditV (SbiiCredit F k x N z c) k x = _
      unfold BiiCreditV SbiiCredit BiiPMF
      simp only [Bool.false_eq_true, if_false, if_true]
      ring
  rw [hfun,
    lintegral_piecewise measurableSet_Ioi, Set.compl_Ioi,
    setLIntegral_const, restrict_apply measurableSet_Ioi, hset_ioi, Real.volume_Ioc,
    restrict_restrict measurableSet_Iic, hset_iic,
    lintegral_add_left ((measurable_sCreditV F k x (N + 1)).const_mul _),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, SCreditV_q_setLIntegral F k hx0 hx1 hy0 hy1,
    setLIntegral_const, Real.volume_Icc, sub_zero, SCreditV_peel F k x y N]
  have hq1 : (2 * (k : ℝ) + x) / (2 * k + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hc1 : ENNReal.ofReal (1 - y)
        + ENNReal.ofReal (1 - (2 * (k : ℝ) + x) / (2 * k + 2)) * ENNReal.ofReal y
      = ENNReal.ofReal (1 - (2 * (k : ℝ) + x) / (2 * k + 2) * y) := by
    rw [← ENNReal.ofReal_mul (by linarith),
        ← ENNReal.ofReal_add (by linarith) (mul_nonneg (by linarith) hy0)]
    congr 1; ring
  have hc2 : ENNReal.ofReal ((2 * (k : ℝ) + x) / (2 * k + 2)) * ENNReal.ofReal y
      = ENNReal.ofReal ((2 * (k : ℝ) + x) / (2 * k + 2) * y) := (ENNReal.ofReal_mul hqnn).symm
  rw [← hc1, ← hc2]
  ring

/-- Credit conservation for `S` (bound): the amplification `q·y·c` is dominated by `B·c`
whenever the threshold is capped by `B` (`q ≤ 1`, `y ≤ B`). -/
theorem SCreditAmp_lintegral (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) (y : ℝ) (c : ℝ≥0∞)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (B : ℝ) (hyB : y ≤ B) :
    ∫⁻ z, SCreditAmp F k x N y c z ∂(ProbLangℝ.unifUnit (T := ℝ))
      ≤ SCreditV F k x y N + ENNReal.ofReal B * c := by
  rw [SCreditAmp_lintegral_eq F k x N y c hx0 hx1 hy0 hy1]
  have hqnn : (0 : ℝ) ≤ (2 * (k : ℝ) + x) / (2 * k + 2) :=
    div_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
  have hq1 : (2 * (k : ℝ) + x) / (2 * k + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
  gcongr
  nlinarith [mul_nonneg (sub_nonneg.mpr hq1) hy0, hyB]

/-- Credit conservation for the `C`-composition: distributing `BiiCreditV` through
`C (2k)` with per-outcome budgets `BiiCCredit`. -/
theorem BiiCreditV_C_eq (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    BiiCreditV F k x = CCreditV (BiiCCredit F x) (2 * k) := by
  have hcT : ENNReal.ofReal (1 / (2 * (k : ℝ) + 2))
        + ENNReal.ofReal (1 / (2 * (k : ℝ) + 2)) * ENNReal.ofReal (1 - x)
      = ENNReal.ofReal (1 - (2 * (k : ℝ) + x) / (2 * k + 2)) := by
    rw [← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (mul_nonneg (by positivity) (by linarith))]
    congr 1; field_simp; ring
  have hcF : ENNReal.ofReal (1 / (2 * (k : ℝ) + 2)) * ENNReal.ofReal x
        + ENNReal.ofReal (2 * (k : ℝ) / (2 * k + 2))
      = ENNReal.ofReal ((2 * (k : ℝ) + x) / (2 * k + 2)) := by
    rw [← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (mul_nonneg (by positivity) hx0) (by positivity)]
    congr 1; field_simp; ring
  simp only [CCreditV, BiiCCredit_zero, BiiCCredit_one F hx0 hx1, BiiCCredit_two, BiiCreditV, BiiPMF]
  push_cast
  rw [← hcT, ← hcF]
  ring

/-- Credit conservation for `B`: distributing `BCreditV` through `S0` with the
parity budget `BS0credit`. -/
theorem BCreditV_S0_eq (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    BCreditV F k x = SCreditV (BS0credit F) k x x 0 := by
  have hqnn : (0 : ℝ) ≤ (2 * (k : ℝ) + x) / (2 * k + 2) :=
    div_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
  have hp0 : (0 : ℝ) ≤ x * ((2 * (k : ℝ) + x) / (2 * k + 2)) := mul_nonneg hx0 hqnn
  have hp1 : x * ((2 * (k : ℝ) + x) / (2 * k + 2)) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) k, mul_nonneg (Nat.cast_nonneg (α := ℝ) k)
      (sub_nonneg.mpr hx1), mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  -- The `S`-diagonal credit is the `DecrTrial` parity credit at the scaled point.
  have hSeq : SCreditV (BS0credit F) k x x 0
      = RealDecrTrialCreditV (fun n => if n % 2 = 0 then F true else F false) 0
          (x * ((2 * (k : ℝ) + x) / (2 * k + 2))) := by
    unfold SCreditV RealDecrTrialCreditV
    refine tsum_congr fun n => ?_
    have hSPMF : SPMF k x x 0 n = RealDecrTrialPMF₀ (x * ((2 * (k : ℝ) + x) / (2 * k + 2))) n := by
      rw [SPMF, if_pos (Nat.zero_le n), Nat.sub_zero, SPMF₀_eq_RealDecrTrialPMF₀]
    rw [hSPMF, RealDecrTrialPMF_base]
    simp only [BS0credit]
  rw [hSeq, RealDecrTrialCreditV_parity (F true) (F false) hp0 hp1]
  have harg : Real.exp (-x * (2 * k + x) / (2 * k + 2))
      = Real.exp (-(x * ((2 * (k : ℝ) + x) / (2 * k + 2)))) := by congr 1; ring
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal (Real.exp (-(x * ((2 * (k : ℝ) + x) / (2 * k + 2)))))
      = ENNReal.ofReal (1 - Real.exp (-(x * ((2 * (k : ℝ) + x) / (2 * k + 2))))) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
  unfold BCreditV
  rw [harg, hsub]

end conservation

/-! ## Specification -/

section specification

/-- Weakest-precondition spec of `C`: from credit `CCreditV F m`, run `C #m`
and return `n ∈ {0,1,2}` carrying credit `F n`. -/
theorem twp_C (E : CoPset) (F : ℕ → ℝ≥0∞) (m : ℕ) :
    ⊢@{IProp GF} ↯ (CCreditV F m) -∗
      tglWp E pl(&C #(.int (m : ℤ)))
        (fun v : Val ℝ => iprop(∃ n : ℕ,
          ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ⌜n = 0 ∨ n = 1 ∨ n = 2⌝ ∗ ↯ (F n))) := by
  iintro Hε
  -- Focus `rand` before its `let` β-step; a greedy `twp_pures` would duplicate the draw.
  twp_pure
  -- Re-bind with the explicit `Exp.rand` constructor: the pl-notation form
  -- does not unify with `iapply twp_rand_exp`.
  twp_bind pl(rand(#(.int (m : ℤ)) + #2, #.unit))
  twp_pures
  twp_bind (Exp.rand (Exp.lit (.int ((m : ℤ) + 2))) (Exp.lit .unit))
  iapply (twp_rand_exp (ε₂ := CCredit F) (Hz := by omega) (HSum := C_HSum F m)) $$ Hε
  iintro %n ⟨%Hn, Hcr⟩
  iapply (ErisWpGS.tglWp_value_of_toVal (v := (.int n : Val ℝ)) rfl)
  simp only [Exp.ofVal]
  obtain ⟨Hn0, Hnz⟩ := Hn
  -- Case on the outcome `n ∈ {0, 1, ≥2}`.
  twp_pure
  twp_pures
  by_cases h0 : n = 0
  · -- `n = 0`: return `#0`, credit `CCredit F 0 = F 0`.
    have hd0 : decide ((BaseLit.int n : BaseLit ℝ) = BaseLit.int 0) = true :=
      decide_eq_true (by rw [h0])
    rw [hd0]
    twp_pures
    twp_value
    imodintro
    iexists 0
    have hn0 : n.toNat = 0 := by omega
    have hc : CCredit F n.toNat = F 0 := by rw [hn0]; rfl
    rw [← hc]
    isplitr [Hcr]
    · ipureintro; rfl
    · isplitr [Hcr]
      · ipureintro; omega
      · iexact Hcr
  · have hd0 : decide ((BaseLit.int n : BaseLit ℝ) = BaseLit.int 0) = false :=
      decide_eq_false (by simp only [BaseLit.int.injEq]; exact h0)
    rw [hd0]
    twp_pures
    by_cases h1 : n = 1
    · -- `n = 1`: return `#1`, credit `CCredit F 1 = F 1`.
      have hd1 : decide ((BaseLit.int n : BaseLit ℝ) = BaseLit.int 1) = true :=
        decide_eq_true (by rw [h1])
      rw [hd1]
      twp_pures
      twp_value
      imodintro
      iexists 1
      have htn : n.toNat = 1 := by omega
      have hc : CCredit F n.toNat = F 1 := by rw [htn]; rfl
      rw [← hc]
      isplitr [Hcr]
      · ipureintro; rfl
      · isplitr [Hcr]
        · ipureintro; omega
        · iexact Hcr
    · -- `n ≥ 2`: return `#2`, credit `CCredit F n.toNat = F 2`.
      have hd1 : decide ((BaseLit.int n : BaseLit ℝ) = BaseLit.int 1) = false :=
        decide_eq_false (by simp only [BaseLit.int.injEq]; exact h1)
      rw [hd1]
      twp_pures
      twp_value
      imodintro
      iexists 2
      have hc : CCredit F n.toNat = F 2 := by
        simp only [CCredit]; rw [if_neg (by omega), if_neg (by omega)]
      rw [← hc]
      isplitr [Hcr]
      · ipureintro; rfl
      · isplitr [Hcr]
        · ipureintro; omega
        · iexact Hcr

/-- Weakest-precondition spec of `Bii`: from credit `BiiCreditV F k x`, run `Bii`
and return `b : Bool` carrying credit `F b`. -/
theorem twp_Bii (E : CoPset) (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ⊢@{IProp GF} ↯ (BiiCreditV F k x) -∗
      tglWp E pl(&Bii #(.int (k : ℤ)) #(.real x))
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v.1 = .lit (.bool b)⌝ ∗ ↯ (F b))) := by
  iintro Hε
  -- β both `fun`s and run `C (2k)` with per-outcome budgets `BiiCCredit`.
  twp_pure
  twp_pure
  twp_bind pl(&C (#2 * #(.int (k : ℤ))))
  twp_pure
  have h2k : (2 * (k : ℤ)) = ((2 * k : ℕ) : ℤ) := by push_cast; ring
  rw [h2k]
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ n : ℕ,
    ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ⌜n = 0 ∨ n = 1 ∨ n = 2⌝ ∗ ↯ (BiiCCredit F x n))))
  isplitl [Hε]
  · iapply (twp_C E (BiiCCredit F x) (2 * k))
    iapply (ErrorCredit.ext (BiiCreditV_C_eq F k x hx0 hx1))
    iexact Hε
  iintro %v ⟨%n, %hn, %hmem, Hcn⟩
  rcases v with ⟨w, hwlc⟩
  simp only at hn; subst hn
  twp_pure
  twp_bind pl(urand)
  iapply (twp_urand_exp' (ε₂ := BiiCredit F x n) (measurable_biiCredit F x n) ?hint) $$ Hcn
  case hint =>
    have hBc : BiiCCredit F x n
        = ∫⁻ r, BiiCredit F x n r ∂(ProbLangℝ.unifUnit (T := ℝ)) := rfl
    rw [hBc]
  iintro %r ⟨%_hr, Hcr⟩
  twp_pure
  -- Read off `(f=0) ‖ ((f=1) ∧ (x<r))` per outcome.
  rcases hmem with h0 | h1 | h2
  · -- `n = 0`: boolean is `true`, cost `BiiCredit F x 0 r = F true`.
    subst h0
    twp_pures
    twp_value
    imodintro
    iexists true
    have hc : BiiCredit F x 0 r = F true := by simp only [BiiCredit]; rfl
    rw [← hc]
    isplitr [Hcr]
    · ipureintro; rfl
    · iexact Hcr
  · -- `n = 1`: boolean is `x < r`; case on it for the cost.
    subst h1
    twp_pures
    rcases hb : ProbLangℝ.realLt x r with _ | _
    · -- `¬ x < r`: boolean `false`, cost `F false`.
      twp_pures
      twp_value
      imodintro
      iexists false
      have hc : BiiCredit F x 1 r = F false := by
        simp [BiiCredit, of_decide_eq_false hb]
      rw [← hc]
      isplitr [Hcr]
      · ipureintro; rfl
      · iexact Hcr
    · -- `x < r`: boolean `true`, cost `F true`.
      twp_pures
      twp_value
      imodintro
      iexists true
      have hc : BiiCredit F x 1 r = F true := by
        simp [BiiCredit, of_decide_eq_true hb]
      rw [← hc]
      isplitr [Hcr]
      · ipureintro; rfl
      · iexact Hcr
  · -- `n = 2`: boolean is `false`, cost `BiiCredit F x 2 r = F false`.
    subst h2
    twp_pures
    twp_value
    imodintro
    iexists false
    have hc : BiiCredit F x 2 r = F false := by simp only [BiiCredit]; rfl
    rw [← hc]
    isplitr [Hcr]
    · ipureintro; rfl
    · iexact Hcr

/-- Fixed-factor tail of `S`: once the threshold `y` is capped by `B < 1`, the
per-iteration recursion probability `≤ B`, so a single amplification factor
`k = 1/B` drives the termination induction (à la `RealDecrTrial`, with the nested
short-circuit `Bii` sub-call handled inside the per-draw credit). -/
theorem twp_S_tail (E : CoPset) (F : ℕ → ℝ≥0∞) (M : ℝ≥0∞) (hnn : ∀ n, F n ≤ M)
    (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (B : ℝ) (hB0 : 0 < B) (hB1 : B < 1) :
    ⊢@{IProp GF} ∀ (N : ℕ) (y : ℝ), ⌜0 ≤ y⌝ -∗ ⌜y ≤ B⌝ -∗
      ↯ (SCreditV F k x y N) -∗
      tglWp E pl(&S #(.int (k : ℤ)) #(.real x) #(.real y) #(.int (N : ℤ)))
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  have hkpos : (0 : ℝ) ≤ 1 / B := by positivity
  set kf : ℝ≥0 := ⟨1 / B, hkpos⟩ with hkf_def
  have Hk1 : 1 < kf := by
    have h : (1 : ℝ) < 1 / B := by rw [lt_div_iff₀ hB0]; linarith
    exact_mod_cast h
  iintro %N %y %Hy0 %HyB Hε_spec
  iapply twp_err_pos solve_not_red
  iintro %ε_term %Hε_pos Hε_term
  irevert Hε_spec
  irevert %HyB
  irevert %Hy0
  irevert %y
  irevert %N
  iapply ErrorCredit.Induction.simple (k := kf) Hε_pos Hk1 $$ [] Hε_term
  imodintro
  iintro ⟨IH, Hε_term⟩ %N %y %Hy0 %HyB Hε_spec
  twp_pure
  twp_pure
  twp_pure
  twp_pure
  twp_pure
  twp_bind pl(urand)
  icombine Hε_spec Hε_term as Hε
  iapply (twp_urand_exp' (ε₂ := SCreditAmp F k x N y ((kf : ℝ≥0∞) * ε_term))
    (measurable_sCreditAmp F k x N y _) ?hint) $$ Hε
  case hint =>
    have hy1 : y ≤ 1 := by linarith
    have hBkf : ENNReal.ofReal B * (↑kf * ε_term) = ε_term := by
      have hkf : (↑kf : ℝ≥0∞) = ENNReal.ofReal (1 / B) := by
        rw [hkf_def, ← ENNReal.ofReal_coe_nnreal]; rfl
      rw [← mul_assoc, hkf,
          ← ENNReal.ofReal_mul hB0.le, mul_one_div, div_self (ne_of_gt hB0),
          ENNReal.ofReal_one, one_mul]
    calc ∫⁻ r, SCreditAmp F k x N y (↑kf * ε_term) r ∂(ProbLangℝ.unifUnit (T := ℝ))
        ≤ SCreditV F k x y N + ENNReal.ofReal B * (↑kf * ε_term) :=
          SCreditAmp_lintegral F k x N y (↑kf * ε_term) hx0 hx1 Hy0 hy1 B HyB
      _ = SCreditV F k x y N + ε_term := by rw [hBkf]
  iintro %z ⟨%Hzm, Hcz⟩
  have Hz01 : 0 < z ∧ z < 1 := mem_unifUnitSupport_real.mp Hzm
  have Hzr : 0 ≤ z ∧ z ≤ 1 := ⟨Hz01.1.le, Hz01.2.le⟩
  twp_pure
  twp_pures
  rcases hyz : ProbLangℝ.realLt y z with _ | _
  · -- `¬ y < z` (z ≤ y): run `Bii`.
    have hcz : SCreditAmp F k x N y ((kf : ℝ≥0∞) * ε_term) z
        = BiiCreditV (SbiiCredit F k x N z ((kf : ℝ≥0∞) * ε_term)) k x := by
      simp [SCreditAmp, of_decide_eq_false hyz]
    ihave Hcz' : iprop(↯ (BiiCreditV (SbiiCredit F k x N z ((kf : ℝ≥0∞) * ε_term)) k x)) $$ [Hcz]
    · rw [← hcz]; iexact Hcz
    twp_pure
    twp_bind pl(&Bii #(.int (k : ℤ)) #(.real x))
    iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ bii : Bool,
      ⌜v.1 = .lit (.bool bii)⌝ ∗ ↯ (SbiiCredit F k x N z ((kf : ℝ≥0∞) * ε_term) bii))))
    isplitl [Hcz']
    · iapply (twp_Bii E (SbiiCredit F k x N z ((kf : ℝ≥0∞) * ε_term)) k x hx0 hx1)
      iexact Hcz'
    iintro %v ⟨%bii, %hbii, Hcbii⟩
    rcases v with ⟨w, hwlc⟩
    simp only at hbii; subst hbii
    cases bii with
    | false =>
      -- recurse `S k x z (N+1)`, cost `SCreditV … z (N+1) + k·ε_term`.
      have hcb : SbiiCredit F k x N z ((kf : ℝ≥0∞) * ε_term) false
          = SCreditV F k x z (N + 1) + (kf : ℝ≥0∞) * ε_term := by simp [SbiiCredit]
      ihave Hcb' : iprop(↯ (SCreditV F k x z (N + 1) + (kf : ℝ≥0∞) * ε_term)) $$ [Hcbii]
      · rw [← hcb]; iexact Hcbii
      ihave ⟨Hexp, Hterm⟩ := ErrorCredit.split (GF := GF) $$ Hcb'
      twp_pure
      twp_pure
      rw [← Nat.cast_add_one]
      twp_bind pl(&S #(.int (k : ℤ)) #(.real x) #(.real z) #(.int ((N + 1 : ℕ) : ℤ)))
      iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ n : ℕ,
        ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))))
      isplitl [Hexp Hterm IH]
      · iapply IH $$ Hterm
        · ipureintro; exact Hzr.1
        · ipureintro
          have : z ≤ y := _root_.not_lt.mp (of_decide_eq_false hyz)
          linarith [HyB]
        · iexact Hexp
      iintro %w Hpost
      iapply tglWp_value
      iexact Hpost
    | true =>
      -- terminal: return `N`, cost `F N`.
      have hcb : SbiiCredit F k x N z ((kf : ℝ≥0∞) * ε_term) true = F N := by simp [SbiiCredit]
      twp_pures
      twp_value
      imodintro
      iexists N
      rw [← hcb]
      iframe Hcbii
      itrivial
  · -- `y < z`: terminal `N`, cost `F N`.
    have hcz : SCreditAmp F k x N y ((kf : ℝ≥0∞) * ε_term) z = F N := by
      simp [SCreditAmp, of_decide_eq_true hyz]
    twp_pures
    twp_value
    imodintro
    iexists N
    rw [← hcz]
    iframe Hcz
    itrivial

/-- Weakest-precondition spec of `S`: peel the first draw `z₀` (un-amplified), then
hand off to the fixed-factor tail `twp_S_tail` with `B := z₀` (later thresholds
stay `≤ z₀ < 1`). -/
theorem twp_S (E : CoPset) (F : ℕ → ℝ≥0∞) (M : ℝ≥0∞) (hnn : ∀ n, F n ≤ M)
    (k : ℕ) (x y : ℝ) (N : ℕ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ⊢@{IProp GF} ↯ (SCreditV F k x y N) -∗
      tglWp E pl(&S #(.int (k : ℤ)) #(.real x) #(.real y) #(.int (N : ℤ)))
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  iintro Hε_spec
  twp_pure
  twp_pure
  twp_pure
  twp_pure
  twp_pure
  twp_bind pl(urand)
  iapply (twp_urand_exp' (ε₂ := SCredit F k x N y)
    (measurable_sCreditAmp F k x N y 0) ?hint) $$ Hε_spec
  case hint =>
    simp only [SCredit]
    exact _root_.le_of_eq
      (by rw [SCreditAmp_lintegral_eq F k x N y 0 hx0 hx1 hy0 hy1, mul_zero, add_zero])
  iintro %z ⟨%Hzm, Hcz⟩
  have Hz01 : 0 < z ∧ z < 1 := mem_unifUnitSupport_real.mp Hzm
  have Hzr : 0 ≤ z ∧ z ≤ 1 := ⟨Hz01.1.le, Hz01.2.le⟩
  twp_pure
  twp_pures
  rcases hyz : ProbLangℝ.realLt y z with _ | _
  · -- `z ≤ y`: run `Bii`.
    have hcz : SCredit F k x N y z = BiiCreditV (SbiiCredit F k x N z 0) k x := by
      simp [SCredit, SCreditAmp, of_decide_eq_false hyz]
    ihave Hcz' : iprop(↯ (BiiCreditV (SbiiCredit F k x N z 0) k x)) $$ [Hcz]
    · rw [← hcz]; iexact Hcz
    twp_pure
    twp_bind pl(&Bii #(.int (k : ℤ)) #(.real x))
    iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ bii : Bool,
      ⌜v.1 = .lit (.bool bii)⌝ ∗ ↯ (SbiiCredit F k x N z 0 bii))))
    isplitl [Hcz']
    · iapply (twp_Bii E (SbiiCredit F k x N z 0) k x hx0 hx1)
      iexact Hcz'
    iintro %v ⟨%bii, %hbii, Hcbii⟩
    rcases v with ⟨w, hwlc⟩
    simp only at hbii; subst hbii
    cases bii with
    | false =>
      -- recurse: hand off to the fixed-factor tail with `B := z₀`.
      have hcb : SbiiCredit F k x N z 0 false = SCreditV F k x z (N + 1) := by
        simp [SbiiCredit]
      ihave Hcb' : iprop(↯ (SCreditV F k x z (N + 1))) $$ [Hcbii]
      · rw [← hcb]; iexact Hcbii
      have hz1 : z < 1 := Hz01.2
      have hz0 : 0 < z := Hz01.1
      twp_pure
      twp_pure
      rw [← Nat.cast_add_one]
      twp_bind pl(&S #(.int (k : ℤ)) #(.real x) #(.real z) #(.int ((N + 1 : ℕ) : ℤ)))
      iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ n : ℕ,
        ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))))
      isplitl [Hcb']
      · iapply (twp_S_tail E F M hnn k x hx0 hx1 z hz0 hz1)
        · ipureintro; exact Hzr.1
        · ipureintro; exact _root_.le_refl z
        · iexact Hcb'
      iintro %w Hpost
      iapply tglWp_value
      iexact Hpost
    | true =>
      have hcb : SbiiCredit F k x N z 0 true = F N := by simp [SbiiCredit]
      twp_pures
      twp_value
      imodintro
      iexists N
      rw [← hcb]
      iframe Hcbii
      itrivial
  · have hcz : SCredit F k x N y z = F N := by simp [SCredit, SCreditAmp, of_decide_eq_true hyz]
    twp_pures
    twp_value
    imodintro
    iexists N
    rw [← hcz]
    iframe Hcz
    itrivial

/-- Weakest-precondition spec of `S0`: non-recursive — draw `z`; terminate at `#0`
if `x < z` or `Bii`, else hand off to `S` (its termination handled by `twp_S`). -/
theorem twp_S0 (E : CoPset) (F : ℕ → ℝ≥0∞) (M : ℝ≥0∞) (hnn : ∀ n, F n ≤ M)
    (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ⊢@{IProp GF} ↯ (SCreditV F k x x 0) -∗
      tglWp E pl(&S0 #(.int (k : ℤ)) #(.real x))
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  iintro Hε
  twp_pure
  twp_pure
  twp_bind pl(urand)
  iapply (twp_urand_exp' (ε₂ := SCredit F k x 0 x)
    (measurable_sCreditAmp F k x 0 x 0) ?hint) $$ Hε
  case hint =>
    simp only [SCredit]
    exact _root_.le_of_eq
      (by rw [SCreditAmp_lintegral_eq F k x 0 x 0 hx0 hx1 hx0 hx1, mul_zero, add_zero])
  iintro %z ⟨%Hzm, Hcz⟩
  have Hz01 : 0 < z ∧ z < 1 := mem_unifUnitSupport_real.mp Hzm
  have Hzr : 0 ≤ z ∧ z ≤ 1 := ⟨Hz01.1.le, Hz01.2.le⟩
  twp_pure
  twp_pures
  rcases hyz : ProbLangℝ.realLt x z with _ | _
  · -- `¬ x < z` (z ≤ x): run `Bii`.
    have hcz : SCredit F k x 0 x z = BiiCreditV (SbiiCredit F k x 0 z 0) k x := by
      simp [SCredit, SCreditAmp, of_decide_eq_false hyz]
    ihave Hcz' : iprop(↯ (BiiCreditV (SbiiCredit F k x 0 z 0) k x)) $$ [Hcz]
    · rw [← hcz]; iexact Hcz
    -- Fire the outer `if #false` → else branch, exposing `if &Bii k x then #0 else …`.
    twp_pure
    twp_bind pl(&Bii #(.int (k : ℤ)) #(.real x))
    iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ bii : Bool,
      ⌜v.1 = .lit (.bool bii)⌝ ∗ ↯ (SbiiCredit F k x 0 z 0 bii))))
    isplitl [Hcz']
    · iapply (twp_Bii E (SbiiCredit F k x 0 z 0) k x hx0 hx1)
      iexact Hcz'
    iintro %v ⟨%bii, %hbii, Hcbii⟩
    rcases v with ⟨w, hwlc⟩
    simp only at hbii; subst hbii
    cases bii with
    | false =>
      -- recurse `S k x z 1`.
      have hcb : SbiiCredit F k x 0 z 0 false = SCreditV F k x z (0 + 1) := by
        simp [SbiiCredit]
      ihave Hcb' : iprop(↯ (SCreditV F k x z 1)) $$ [Hcbii]
      · have h01 : SCreditV F k x z 1 = SCreditV F k x z (0 + 1) := rfl
        rw [h01, ← hcb]; iexact Hcbii
      -- Fire the inner `if #false` → else, exposing `&S k x z #1`.
      twp_pure
      twp_bind pl(&S #(.int (k : ℤ)) #(.real x) #(.real z) #(.int (1 : ℤ)))
      iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ n : ℕ,
        ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))))
      isplitl [Hcb']
      · iapply (twp_S E F M hnn k x z 1 hx0 hx1 Hzr.1 Hzr.2)
        iexact Hcb'
      iintro %w Hpost
      iapply tglWp_value
      iexact Hpost
    | true =>
      -- terminal: `#0`, cost `F 0`.
      have hcb : SbiiCredit F k x 0 z 0 true = F 0 := by simp [SbiiCredit]
      twp_pures
      twp_value
      imodintro
      iexists 0
      rw [← hcb]
      iframe Hcbii
      itrivial
  · -- `x < z`: terminal `#0`, cost `F 0`.
    have hcz : SCredit F k x 0 x z = F 0 := by simp [SCredit, SCreditAmp, of_decide_eq_true hyz]
    twp_pures
    twp_value
    imodintro
    iexists 0
    rw [← hcz]
    iframe Hcz
    itrivial

/-- Weakest-precondition spec of `B`: run `S0` and return the parity of its result. -/
theorem twp_B (E : CoPset) (F : Bool → ℝ≥0∞) (M : ℝ≥0∞) (Hnn : ∀ b, F b ≤ M)
    (k : ℕ) (x : ℝ) (Hx : 0 ≤ x ∧ x ≤ 1) :
    ⊢@{IProp GF} ↯ (BCreditV F k x) -∗
      tglWp E pl(&B #(.int (k : ℤ)) #(.real x))
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v.1 = .lit (.bool b)⌝ ∗ ↯ (F b))) := by
  iintro Hε
  twp_pure
  twp_pure
  twp_bind pl(&S0 #(.int (k : ℤ)) #(.real x))
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ n : ℕ,
    ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (BS0credit F n))))
  isplitl [Hε]
  · iapply (twp_S0 E (BS0credit F) M (fun n => by
      simp only [BS0credit]; split <;> exact Hnn _) k x Hx.1 Hx.2)
    iapply (ErrorCredit.ext (BCreditV_S0_eq F k x Hx.1 Hx.2))
    iexact Hε
  iintro %v ⟨%n, %hn, Hcn⟩
  rcases v with ⟨w, hwlc⟩
  simp only at hn; subst hn
  -- Read off the parity `n rem 2 = 0`.
  twp_pures
  rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
  · -- `n` even: result `#true`, cost `F true`.
    have hmod : (Int.ofNat n % 2 : ℤ) = 0 := by simp only [Int.ofNat_eq_natCast]; omega
    rw [hmod]
    twp_pures
    twp_value
    imodintro
    iexists true
    have hc : BS0credit F n = F true := by simp only [BS0credit, hpar]; rfl
    rw [← hc]
    iframe Hcn
    itrivial
  · -- `n` odd: result `#false`, cost `F false`.
    have hmod : (Int.ofNat n % 2 : ℤ) = 1 := by simp only [Int.ofNat_eq_natCast]; omega
    rw [hmod]
    twp_pures
    twp_value
    imodintro
    iexists false
    have hc : BS0credit F n = F false := by
      simp only [BS0credit]; rw [if_neg (by omega)]
    rw [← hc]
    iframe Hcn
    itrivial

end specification

end
end Examples
end TotalEris
end ProbLang
