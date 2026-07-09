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

/-! ## The discrete selector `C` -/

/-- `C m`: draw from `rand (m+2)` and collapse the outcome to `0`, `1`, or `2`. -/
@[pl_fold]
def C : Exp ℝ := pl%
  fun m, let v := rand(m + #2, #.unit); if v = #0 then #0 else if v = #1 then #1 else #2

/-- Per-outcome credit for the discrete `rand (m+2)` in `C`: outcome `0 ↦ F 0`,
`1 ↦ F 1`, everything else (`2 … m+1`) `↦ F 2` (all collapse to result `2`). -/
def C_credit (F : ℕ → ℝ≥0∞) : ℕ → ℝ≥0∞ :=
  fun j => if j = 0 then F 0 else if j = 1 then F 1 else F 2

/-- Distribution credit for `C`:
`1/(m+2) · F 0 + 1/(m+2) · F 1 + m/(m+2) · F 2`. -/
def C_CreditV (F : ℕ → ℝ≥0∞) (m : ℕ) : ℝ≥0∞ :=
  .ofReal (1 / ((m : ℝ) + 2)) * F 0 + .ofReal (1 / ((m : ℝ) + 2)) * F 1 +
  .ofReal ((m : ℝ) / ((m : ℝ) + 2)) * F 2

/-- Sum of the `C` per-outcome credits over the `m+2` outcomes: outcome `0 ↦ F 0`,
`1 ↦ F 1`, and the remaining `m` outcomes (`2 … m+1`) each `↦ F 2`. -/
theorem C_credit_sum (F : ℕ → ℝ≥0∞) (m : ℕ) :
    ∑ n ∈ Finset.range (m + 2), C_credit F n = F 0 + F 1 + (m : ℝ≥0∞) * F 2 := by
  induction m with
  | zero => simp [Finset.sum_range_succ, C_credit]
  | succ k ih =>
    have hk2 : C_credit F (k + 2) = F 2 := by simp [C_credit]
    rw [add_right_comm, Finset.sum_range_succ, ih, hk2]
    push_cast; ring

/-- The `HSum` obligation of `twp_rand_exp` for `C`: the averaged per-outcome
credit equals `C_CreditV F m`. Stated as `≤` (with equality) to match
`twp_rand_exp`. -/
theorem C_HSum (F : ℕ → ℝ≥0∞) (m : ℕ) :
    (∑ n ∈ Finset.range ((m : ℤ) + 2).toNat, C_credit F n)
        / (((m : ℤ) + 2).toNat : ENNReal) ≤ C_CreditV F m := by
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
  have hcv : C_CreditV F m
      = (F 0 + F 1 + (m : ℝ≥0∞) * F 2) * ((m + 2 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [C_CreditV, hinv, hmm]; ring
  refine _root_.le_of_eq ?_
  rw [hz, C_credit_sum, hcv, div_eq_mul_inv]

/-- Weakest-precondition spec of `C`: from credit `C_CreditV F m`, run `C #m`
and return `n ∈ {0,1,2}` carrying credit `F n`. -/
theorem twp_C (E : CoPset) (F : ℕ → ℝ≥0∞) (m : ℕ) :
    ⊢@{IProp GF} ↯ (C_CreditV F m) -∗
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
  iapply (twp_rand_exp (ε₂ := C_credit F) (Hz := by omega) (HSum := C_HSum F m)) $$ Hε
  iintro %n ⟨%Hn, Hcr⟩
  iapply (ErisWpGS.tglWp_value_of_toVal (v := (.int n : Val ℝ)) rfl)
  simp only [Exp.ofVal]
  obtain ⟨Hn0, Hnz⟩ := Hn
  -- Case on the outcome `n ∈ {0, 1, ≥2}`.
  twp_pure
  twp_pures
  by_cases h0 : n = 0
  · -- `n = 0`: return `#0`, credit `C_credit F 0 = F 0`.
    have hd0 : decide ((BaseLit.int n : BaseLit ℝ) = BaseLit.int 0) = true :=
      decide_eq_true (by rw [h0])
    rw [hd0]
    twp_pures
    twp_value
    imodintro
    iexists 0
    have hn0 : n.toNat = 0 := by omega
    have hc : C_credit F n.toNat = F 0 := by rw [hn0]; rfl
    rw [← hc]
    isplitr [Hcr]
    · ipureintro; rfl
    · isplitr [Hcr]
      · ipureintro; omega
      · iexact Hcr
  · rw [show decide ((BaseLit.int n : BaseLit ℝ) = BaseLit.int 0) = false from
          decide_eq_false (by simp only [BaseLit.int.injEq]; exact h0)]
    twp_pures
    by_cases h1 : n = 1
    · -- `n = 1`: return `#1`, credit `C_credit F 1 = F 1`.
      rw [show decide ((BaseLit.int n : BaseLit ℝ) = BaseLit.int 1) = true from
            decide_eq_true (by rw [h1])]
      twp_pures
      twp_value
      imodintro
      iexists 1
      have hc : C_credit F n.toNat = F 1 := by rw [show n.toNat = 1 from by omega]; rfl
      rw [← hc]
      isplitr [Hcr]
      · ipureintro; rfl
      · isplitr [Hcr]
        · ipureintro; omega
        · iexact Hcr
    · -- `n ≥ 2`: return `#2`, credit `C_credit F n.toNat = F 2`.
      rw [show decide ((BaseLit.int n : BaseLit ℝ) = BaseLit.int 1) = false from
            decide_eq_false (by simp only [BaseLit.int.injEq]; exact h1)]
      twp_pures
      twp_value
      imodintro
      iexists 2
      have hc : C_credit F n.toNat = F 2 := by
        simp only [C_credit]; rw [if_neg (by omega), if_neg (by omega)]
      rw [← hc]
      isplitr [Hcr]
      · ipureintro; rfl
      · isplitr [Hcr]
        · ipureintro; omega
        · iexact Hcr

/-! ## The boolean gate `Bii` -/

/-- `Bii k x`: boolean gate `(C (2k) = 0) ‖ ((C (2k) = 1) ∧ (x < urand))` with a
fresh `urand` draw. The disjunction short-circuits, so `Bii` samples only when
`C (2k) ≠ 0`. -/
@[pl_fold]
def Bii : Exp ℝ := pl%
  fun k, fun x,
    let f := &C (#2 * k);
    let r := urand;
    if f = #0 then #true else (if f = #1 then (x < r) else #false)

/-- Outcome measure for `Bii k x`: `μ true = 1 - (2k+x)/(2k+2)`,
`μ false = (2k+x)/(2k+2)`. -/
def Biiμ (k : ℕ) (x : ℝ) : Bool → ℝ≥0∞
  | true => .ofReal (1 - (2 * (k : ℝ) + x) / (2 * k + 2))
  | false => .ofReal ((2 * (k : ℝ) + x) / (2 * k + 2))

/-- Distribution credit for `Bii k x`: `μ false · F false + μ true · F true`. -/
def Bii_CreditV (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  Biiμ k x false * F false + Biiμ k x true * F true

/-- The per-`(C-result n, urand-draw r)` cost inside `Bii`: the fresh draw `r` is
taken unconditionally, and `(f=0) ‖ ((f=1) ∧ (x<r))` reads off as `true` when
`n=0`, `x<r` when `n=1`, and `false` when `n≥2`. -/
def BiiCostFn (F : Bool → ℝ≥0∞) (x : ℝ) (n : ℕ) (r : ℝ) : ℝ≥0∞ :=
  if n = 0 then F true else if n = 1 then (if x < r then F true else F false) else F false

/-- The credit `C` must return for outcome `n`: the expectation of `BiiCostFn`
over the fresh uniform draw `r`. -/
def BiiCCredit (F : Bool → ℝ≥0∞) (x : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ r, BiiCostFn F x n r ∂(ProbLangℝ.unifUnit (T := ℝ))

/-- `BiiCCredit` for the three `C`-outcomes: `0 ↦ F true`, `2 ↦ F false`, and the
gated outcome `1 ↦ (1-x)·F true + x·F false` (the fresh draw `r` compared to `x`). -/
theorem BiiCCredit_zero (F : Bool → ℝ≥0∞) (x : ℝ) : BiiCCredit F x 0 = F true := by
  show ∫⁻ r, BiiCostFn F x 0 r ∂(ProbLangℝ.unifUnit (T := ℝ)) = F true
  rw [show (fun r => BiiCostFn F x 0 r) = (fun _ => F true) from by funext r; rfl,
    lintegral_const, measure_univ, mul_one]

theorem BiiCCredit_two (F : Bool → ℝ≥0∞) (x : ℝ) : BiiCCredit F x 2 = F false := by
  show ∫⁻ r, BiiCostFn F x 2 r ∂(ProbLangℝ.unifUnit (T := ℝ)) = F false
  rw [show (fun r => BiiCostFn F x 2 r) = (fun _ => F false) from by funext r; rfl,
    lintegral_const, measure_univ, mul_one]

/-- `BiiCCredit … 1 = (1-x)·F true + x·F false` (the fresh draw `r` gates `x < r`). -/
theorem BiiCCredit_one (F : Bool → ℝ≥0∞) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    BiiCCredit F x 1 = F true * ENNReal.ofReal (1 - x) + F false * ENNReal.ofReal x := by
  show ∫⁻ r, BiiCostFn F x 1 r ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = _
  rw [show (fun r => BiiCostFn F x 1 r) = (fun r => if x < r then F true else F false) from by
    funext r; rfl]
  have hsetT : Set.Ioi x ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc x 1 := by
    ext r; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    exact ⟨fun ⟨h2, _, h1⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨h2, _root_.le_trans hx0 h2.le, h1⟩⟩
  have hsetF : Set.Iic x ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 x := by
    ext r; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun ⟨h2, h1, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, _root_.le_trans h2 hx1⟩⟩
  rw [show (fun r => if x < r then F true else F false)
        = (fun r => (Set.Ioi x).indicator (fun _ => F true) r
            + (Set.Iic x).indicator (fun _ => F false) r) from by
      funext r; by_cases h : x < r
      · simp [Set.indicator_apply, h, _root_.not_le.mpr h, _root_.le_of_lt h]
      · simp [Set.indicator_apply, h, _root_.not_lt.mp h],
    lintegral_add_left ((measurable_const.indicator measurableSet_Ioi)),
    lintegral_indicator measurableSet_Ioi, lintegral_indicator measurableSet_Iic,
    setLIntegral_const, setLIntegral_const, restrict_apply measurableSet_Ioi,
    restrict_apply measurableSet_Iic, hsetT, hsetF, Real.volume_Ioc, Real.volume_Icc,
    sub_zero]

/-- Credit conservation for the `C`-composition: distributing `Bii_CreditV` through
`C (2k)` with per-outcome budgets `BiiCCredit`. -/
theorem Bii_CreditV_C_eq (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Bii_CreditV F k x = C_CreditV (BiiCCredit F x) (2 * k) := by
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
  simp only [C_CreditV, BiiCCredit_zero, BiiCCredit_one F hx0 hx1, BiiCCredit_two, Bii_CreditV, Biiμ]
  push_cast
  rw [← hcT, ← hcF]
  ring

/-- Measurability of the per-outcome cost (consumed by `twp_urand_exp'`). -/
theorem BiiCostFn_measurable (F : Bool → ℝ≥0∞) (x : ℝ) (n : ℕ) :
    Measurable (BiiCostFn F x n) := by
  unfold BiiCostFn
  split
  · exact measurable_const
  · split
    · exact Measurable.ite measurableSet_Ioi measurable_const measurable_const
    · exact measurable_const

/-- Weakest-precondition spec of `Bii`: from credit `Bii_CreditV F k x`, run `Bii`
and return `b : Bool` carrying credit `F b`. -/
theorem twp_Bii (E : CoPset) (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ⊢@{IProp GF} ↯ (Bii_CreditV F k x) -∗
      tglWp E pl(&Bii #(.int (k : ℤ)) #(.real x))
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v.1 = .lit (.bool b)⌝ ∗ ↯ (F b))) := by
  iintro Hε
  -- β both `fun`s and run `C (2k)` with per-outcome budgets `BiiCCredit`.
  twp_pure
  twp_pure
  twp_bind pl(&C (#2 * #(.int (k : ℤ))))
  twp_pure
  rw [show (2 * (k : ℤ)) = ((2 * k : ℕ) : ℤ) from by push_cast; ring]
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ n : ℕ,
    ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ⌜n = 0 ∨ n = 1 ∨ n = 2⌝ ∗ ↯ (BiiCCredit F x n))))
  isplitl [Hε]
  · iapply (twp_C E (BiiCCredit F x) (2 * k))
    iapply (ErrorCredit.ext (Bii_CreditV_C_eq F k x hx0 hx1))
    iexact Hε
  iintro %v ⟨%n, %hn, %hmem, Hcn⟩
  rcases v with ⟨w, hwlc⟩
  simp only at hn; subst hn
  twp_pure
  twp_bind pl(urand)
  iapply (twp_urand_exp' (ε₂ := BiiCostFn F x n) (BiiCostFn_measurable F x n) ?hint) $$ Hcn
  case hint => rw [show BiiCCredit F x n
      = ∫⁻ r, BiiCostFn F x n r ∂(ProbLangℝ.unifUnit (T := ℝ)) from rfl]
  iintro %r ⟨%_hr, Hcr⟩
  twp_pure
  -- Read off `(f=0) ‖ ((f=1) ∧ (x<r))` per outcome.
  rcases hmem with h0 | h1 | h2
  · -- `n = 0`: boolean is `true`, cost `BiiCostFn F x 0 r = F true`.
    subst h0
    twp_pures
    twp_value
    imodintro
    iexists true
    have hc : BiiCostFn F x 0 r = F true := by simp only [BiiCostFn]; rfl
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
      have hc : BiiCostFn F x 1 r = F false := by
        simp [BiiCostFn, of_decide_eq_false hb]
      rw [← hc]
      isplitr [Hcr]
      · ipureintro; rfl
      · iexact Hcr
    · -- `x < r`: boolean `true`, cost `F true`.
      twp_pures
      twp_value
      imodintro
      iexists true
      have hc : BiiCostFn F x 1 r = F true := by
        simp [BiiCostFn, of_decide_eq_true hb]
      rw [← hc]
      isplitr [Hcr]
      · ipureintro; rfl
      · iexact Hcr
  · -- `n = 2`: boolean is `false`, cost `BiiCostFn F x 2 r = F false`.
    subst h2
    twp_pures
    twp_value
    imodintro
    iexists false
    have hc : BiiCostFn F x 2 r = F false := by simp only [BiiCostFn]; rfl
    rw [← hc]
    isplitr [Hcr]
    · ipureintro; rfl
    · iexact Hcr

/-! ## The index loop `S` -/

/-- `S k x y N`: rejection loop — draw `z`; return `N` if `y < z` or `Bii k x`,
else recurse at threshold `z` with index `N+1`. -/
@[pl_fold]
def S : Exp ℝ := pl%
  rec trial k x y N :=
    let z := urand;
    if y < z then N else (if &Bii k x then N else trial k x z (N + #1))

/-- The `S`-loop PMF core: the difference of two successive `DecrTrial` masses at
the scaled point `y·(2k+x)/(2k+2)`. -/
def Sμ0 (k : ℕ) (x y : ℝ) (n : ℕ) : ℝ≥0∞ :=
  .ofReal ((y ^ n / n.factorial) * ((2 * (k : ℝ) + x) / (2 * k + 2)) ^ n -
    (y ^ (n + 1) / (n + 1).factorial) * ((2 * (k : ℝ) + x) / (2 * k + 2)) ^ (n + 1))

/-- The `S`-loop PMF, masked to `n ≥ N`: `[N ≤ n] · Sμ0 k x y (n - N)`. -/
def Sμ (k : ℕ) (x y : ℝ) (N n : ℕ) : ℝ≥0∞ :=
  if N ≤ n then Sμ0 k x y (n - N) else 0

/-- Distribution credit for `S`: `∑ₙ Sμ k x y N n · F n`. -/
def S_CreditV (F : ℕ → ℝ≥0∞) (k : ℕ) (x y : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ, Sμ k x y N n * F n

/-- Credit the nested `Bii` must return (reached only when `z ≤ y`, i.e. the first
disjunct `y<z` was false), as a function of its result `bii`: terminate (cost `F N`)
if `bii` is `true`, else recurse with new threshold `z` (cost `S_CreditV … z (N+1)`,
topped up by a termination credit `c`). -/
def SbiiCredit (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) (z : ℝ) (c : ℝ≥0∞) :
    Bool → ℝ≥0∞ :=
  fun bii => if bii then F N else S_CreditV F k x z (N + 1) + c

/-- Per-draw credit distributed across the fresh `z ← urand`: if `y < z` the loop
terminates immediately (cost `F N`, `Bii` not run — short-circuit `‖`); otherwise
`Bii` runs with the per-result budget `SbiiCredit`. -/
def SgAmp (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) (y : ℝ) (c : ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  fun z => if y < z then F N else Bii_CreditV (SbiiCredit F k x N z c) k x

/-- `Sμ0` is exactly the `DecrTrial` PMF at the scaled point `y·(2k+x)/(2k+2)`. -/
theorem Sμ0_eq_RealDecrTrialμ0 (k : ℕ) (x y : ℝ) (n : ℕ) :
    Sμ0 k x y n = RealDecrTrialμ0 (y * ((2 * (k : ℝ) + x) / (2 * k + 2))) n := by
  unfold Sμ0 RealDecrTrialμ0
  congr 1
  rw [mul_pow, mul_pow]; ring

/-- `S_CreditV` is the `DecrTrial` credit at the scaled point `y·(2k+x)/(2k+2)`. -/
theorem S_CreditV_eq_RealDecrTrialCreditV (F : ℕ → ℝ≥0∞) (k : ℕ) (x y : ℝ) (N : ℕ) :
    S_CreditV F k x y N = RealDecrTrialCreditV F N (y * ((2 * (k : ℝ) + x) / (2 * k + 2))) := by
  unfold S_CreditV RealDecrTrialCreditV
  refine tsum_congr fun n => ?_
  congr 1
  unfold Sμ RealDecrTrialμ
  by_cases h : N ≤ n
  · rw [if_pos h, if_pos h, Sμ0_eq_RealDecrTrialμ0]
  · rw [if_neg h, if_neg h]

/-- The `Sμ0` Lebesgue integral over `[0,y]`, pre-multiplied by the factor `q`, advances
the index by one (the `S`-analogue of `RealDecrTrialμ0_setLIntegral`; the running
threshold `z` scales by `q` inside the `DecrTrial` PMF). -/
theorem Sμ0_q_setLIntegral (k : ℕ) {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) (m : ℕ) :
    ENNReal.ofReal ((2 * (k : ℝ) + x) / (2 * k + 2)) * (∫⁻ z in Set.Icc 0 y, Sμ0 k x z m ∂volume)
      = Sμ0 k x y (m + 1) := by
  have hqnn : (0 : ℝ) ≤ (2 * (k : ℝ) + x) / (2 * k + 2) :=
    div_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
  have hq1 : (2 * (k : ℝ) + x) / (2 * k + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hbridge : (∫⁻ z in Set.Icc 0 y, Sμ0 k x z m ∂volume)
      = ENNReal.ofReal (∫ z in (0 : ℝ)..y,
          ((z * ((2 * (k : ℝ) + x) / (2 * k + 2))) ^ m / (m.factorial : ℝ)
            - (z * ((2 * (k : ℝ) + x) / (2 * k + 2))) ^ (m + 1) / ((m + 1).factorial : ℝ))) := by
    rw [← lintegral_ofReal_Icc hy0 (by fun_prop) (fun z hz =>
          RealDecrTrialμ0_real_nonneg (mul_nonneg hz.1 hqnn)
            (mul_le_one₀ (_root_.le_trans hz.2 hy1) hqnn hq1) m)]
    refine setLIntegral_congr_fun measurableSet_Icc (fun z hz => ?_)
    rw [Sμ0_eq_RealDecrTrialμ0]; rfl
  have hint : (∫ z in (0 : ℝ)..y,
        ((z * ((2 * (k : ℝ) + x) / (2 * k + 2))) ^ m / (m.factorial : ℝ)
          - (z * ((2 * (k : ℝ) + x) / (2 * k + 2))) ^ (m + 1) / ((m + 1).factorial : ℝ)))
      = ((2 * (k : ℝ) + x) / (2 * k + 2)) ^ m * y ^ (m + 1) / (m + 1).factorial
        - ((2 * (k : ℝ) + x) / (2 * k + 2)) ^ (m + 1) * y ^ (m + 2) / (m + 2).factorial := by
    have h0 : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [mul_pow]
    rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _),
        show (fun z => z ^ m * ((2 * (k : ℝ) + x) / (2 * k + 2)) ^ m / (m.factorial : ℝ))
          = (fun z => ((2 * (k : ℝ) + x) / (2 * k + 2)) ^ m / (m.factorial : ℝ) * z ^ m) from by
          funext z; ring,
        show (fun z => z ^ (m + 1) * ((2 * (k : ℝ) + x) / (2 * k + 2)) ^ (m + 1)
              / ((m + 1).factorial : ℝ))
          = (fun z => ((2 * (k : ℝ) + x) / (2 * k + 2)) ^ (m + 1) / ((m + 1).factorial : ℝ)
              * z ^ (m + 1)) from by funext z; ring,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_pow, integral_pow, zero_pow (by omega), zero_pow (by omega),
        show ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * m.factorial from by
          rw [Nat.factorial_succ]; push_cast; ring,
        show ((m + 2).factorial : ℝ) = ((m : ℝ) + 2) * (((m : ℝ) + 1) * m.factorial) from by
          rw [show m + 2 = (m + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ];
          push_cast; ring]
    field_simp; push_cast; ring
  rw [hbridge, hint, ← ENNReal.ofReal_mul hqnn]
  unfold Sμ0
  congr 1
  ring

/-- `Sμ0` is `ofReal` of a polynomial in the (running) threshold `y`, hence
measurable in `y`. -/
theorem Sμ0_measurable (k : ℕ) (x : ℝ) (n : ℕ) :
    Measurable (fun y : ℝ => Sμ0 k x y n) :=
  ENNReal.measurable_ofReal.comp (by fun_prop)

/-- Integrating the tail credit `S_CreditV … (N+1)` over the running threshold `z ∈ [0,y]`,
pre-multiplied by `q`, telescopes into the shifted `Sμ0`-series. -/
theorem S_CreditV_q_setLIntegral (F : ℕ → ℝ≥0∞) (k : ℕ) {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (N : ℕ) :
    ENNReal.ofReal ((2 * (k : ℝ) + x) / (2 * k + 2))
        * (∫⁻ z in Set.Icc 0 y, S_CreditV F k x z (N + 1) ∂volume)
      = ∑' m : ℕ, Sμ0 k x y (m + 1) * F (N + 1 + m) := by
  have hreindex : ∀ z, S_CreditV F k x z (N + 1) = ∑' m : ℕ, Sμ0 k x z m * F (N + 1 + m) := by
    intro z
    rw [S_CreditV_eq_RealDecrTrialCreditV, RealDecrTrialCreditV_reindex]
    exact tsum_congr fun m => by rw [← Sμ0_eq_RealDecrTrialμ0]
  rw [show (∫⁻ z in Set.Icc 0 y, S_CreditV F k x z (N + 1) ∂volume)
        = ∫⁻ z in Set.Icc 0 y, ∑' m : ℕ, Sμ0 k x z m * F (N + 1 + m) ∂volume from
      setLIntegral_congr_fun measurableSet_Icc (fun z _ => hreindex z),
    lintegral_tsum (fun m => ((Sμ0_measurable k x m).mul_const (F (N + 1 + m))).aemeasurable),
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [lintegral_mul_const _ (Sμ0_measurable k x m), ← mul_assoc, Sμ0_q_setLIntegral k hx0 hx1 hy0 hy1]

/-- `Sμ` is measurable in the running threshold `y` (the `n < N` branch is constant). -/
theorem Sμ_measurable (k : ℕ) (x : ℝ) (N n : ℕ) :
    Measurable (fun y : ℝ => Sμ k x y N n) := by
  unfold Sμ
  by_cases h : N ≤ n
  · simpa only [h, if_true] using Sμ0_measurable k x (n - N)
  · simpa only [h, if_false] using measurable_const

/-- `S_CreditV` is a `tsum` of `Sμ`-weighted credits, hence measurable in `y`. -/
theorem S_CreditV_measurable (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) :
    Measurable (fun y : ℝ => S_CreditV F k x y N) :=
  Measurable.ennreal_tsum fun n => (Sμ_measurable k x N n).mul_const (F n)

/-- Measurability of the per-draw credit (consumed by `twp_urand_exp'`). -/
theorem SgAmp_measurable (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) (y : ℝ) (c : ℝ≥0∞) :
    Measurable (SgAmp F k x N y c) := by
  unfold SgAmp
  refine Measurable.ite measurableSet_Ioi measurable_const ?_
  -- `Bii_CreditV (SbiiCredit … z …) k x` = `Biiμ·(S_CreditV … z … + c) + Biiμ·(F N)`.
  have hred : (fun z : ℝ => Bii_CreditV (SbiiCredit F k x N z c) k x)
      = (fun z : ℝ => Biiμ k x false * (S_CreditV F k x z (N + 1) + c)
          + Biiμ k x true * F N) := by
    funext z; rfl
  rw [hred]
  exact (((S_CreditV_measurable F k x (N + 1)).add_const c).const_mul (Biiμ k x false)).add
    measurable_const

/-- Peel the `N`-th (answer) term off `S_CreditV`: coefficient `1 - qy` on `F N`. -/
theorem S_CreditV_peel (F : ℕ → ℝ≥0∞) (k : ℕ) (x y : ℝ) (N : ℕ) :
    S_CreditV F k x y N
      = ENNReal.ofReal (1 - (2 * (k : ℝ) + x) / (2 * k + 2) * y) * F N
        + ∑' m : ℕ, Sμ0 k x y (m + 1) * F (N + 1 + m) := by
  rw [S_CreditV_eq_RealDecrTrialCreditV, RealDecrTrialCreditV_reindex,
      tsum_eq_zero_add' (f := fun m => RealDecrTrialμ0 (y * ((2 * (k : ℝ) + x) / (2 * k + 2))) m
        * F (N + m)) ENNReal.summable]
  congr 1
  · rw [Nat.add_zero]
    congr 1
    unfold RealDecrTrialμ0
    congr 1
    simp only [pow_zero, pow_one, zero_add, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
      div_one]
    ring
  · exact tsum_congr fun m => by
      rw [← Sμ0_eq_RealDecrTrialμ0, show N + (m + 1) = N + 1 + m from by omega]

/-- Credit conservation for `S` (exact): integrating the amplified per-draw credit over the
fresh `z` recovers `S_CreditV` plus the reject-weighted amplification `q·y·c`. -/
theorem SgAmp_lintegral_eq (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) (y : ℝ) (c : ℝ≥0∞)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∫⁻ z, SgAmp F k x N y c z ∂(ProbLangℝ.unifUnit (T := ℝ))
      = S_CreditV F k x y N + ENNReal.ofReal ((2 * (k : ℝ) + x) / (2 * k + 2) * y) * c := by
  have hqnn : (0 : ℝ) ≤ (2 * (k : ℝ) + x) / (2 * k + 2) :=
    div_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
  have hset_ioi : Set.Ioi y ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc y 1 := by
    ext z; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    exact ⟨fun ⟨h2, _, h1⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨h2, _root_.le_trans hy0 h2.le, h1⟩⟩
  have hset_iic : Set.Iic y ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 y := by
    ext z; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun ⟨h2, h1, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, _root_.le_trans h2 hy1⟩⟩
  show ∫⁻ z, SgAmp F k x N y c z ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = _
  rw [show (fun z => SgAmp F k x N y c z) = (Set.Ioi y).piecewise (fun _ => F N)
        (fun z => ENNReal.ofReal ((2 * (k : ℝ) + x) / (2 * k + 2)) * S_CreditV F k x z (N + 1)
          + (ENNReal.ofReal ((2 * (k : ℝ) + x) / (2 * k + 2)) * c
            + ENNReal.ofReal (1 - (2 * (k : ℝ) + x) / (2 * k + 2)) * F N)) from by
      funext z
      simp only [SgAmp, Set.piecewise, Set.mem_Ioi]
      by_cases h : y < z
      · simp only [if_pos h]
      · simp only [if_neg h]
        show Bii_CreditV (SbiiCredit F k x N z c) k x = _
        unfold Bii_CreditV SbiiCredit Biiμ
        simp only [Bool.false_eq_true, if_false, if_true]
        ring,
    lintegral_piecewise measurableSet_Ioi, Set.compl_Ioi,
    setLIntegral_const, restrict_apply measurableSet_Ioi, hset_ioi, Real.volume_Ioc,
    restrict_restrict measurableSet_Iic, hset_iic,
    lintegral_add_left ((S_CreditV_measurable F k x (N + 1)).const_mul _),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, S_CreditV_q_setLIntegral F k hx0 hx1 hy0 hy1,
    setLIntegral_const, Real.volume_Icc, sub_zero, S_CreditV_peel F k x y N]
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
theorem SgAmp_lintegral (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ) (N : ℕ) (y : ℝ) (c : ℝ≥0∞)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (B : ℝ) (hyB : y ≤ B) :
    ∫⁻ z, SgAmp F k x N y c z ∂(ProbLangℝ.unifUnit (T := ℝ))
      ≤ S_CreditV F k x y N + ENNReal.ofReal B * c := by
  rw [SgAmp_lintegral_eq F k x N y c hx0 hx1 hy0 hy1]
  have hqnn : (0 : ℝ) ≤ (2 * (k : ℝ) + x) / (2 * k + 2) :=
    div_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
  have hq1 : (2 * (k : ℝ) + x) / (2 * k + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
  gcongr
  nlinarith [mul_nonneg (sub_nonneg.mpr hq1) hy0, hyB]

/-- Fixed-factor tail of `S`: once the threshold `y` is capped by `B < 1`, the
per-iteration recursion probability `≤ B`, so a single amplification factor
`k = 1/B` drives the termination induction (à la `RealDecrTrial`, with the nested
short-circuit `Bii` sub-call handled inside the per-draw credit). -/
theorem twp_S_tail (E : CoPset) (F : ℕ → ℝ≥0∞) (M : ℝ≥0∞) (hnn : ∀ n, F n ≤ M)
    (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (B : ℝ) (hB0 : 0 < B) (hB1 : B < 1) :
    ⊢@{IProp GF} ∀ (N : ℕ) (y : ℝ), ⌜0 ≤ y⌝ -∗ ⌜y ≤ B⌝ -∗
      ↯ (S_CreditV F k x y N) -∗
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
  iapply (twp_urand_exp' (ε₂ := SgAmp F k x N y ((kf : ℝ≥0∞) * ε_term))
    (SgAmp_measurable F k x N y _) ?hint) $$ Hε
  case hint =>
    have hy1 : y ≤ 1 := by linarith
    have hBkf : ENNReal.ofReal B * (↑kf * ε_term) = ε_term := by
      rw [← mul_assoc, show (↑kf : ℝ≥0∞) = ENNReal.ofReal (1 / B) from by
            rw [hkf_def, ← ENNReal.ofReal_coe_nnreal]; rfl,
          ← ENNReal.ofReal_mul hB0.le, mul_one_div, div_self (ne_of_gt hB0),
          ENNReal.ofReal_one, one_mul]
    calc ∫⁻ r, SgAmp F k x N y (↑kf * ε_term) r ∂(ProbLangℝ.unifUnit (T := ℝ))
        ≤ S_CreditV F k x y N + ENNReal.ofReal B * (↑kf * ε_term) :=
          SgAmp_lintegral F k x N y (↑kf * ε_term) hx0 hx1 Hy0 hy1 B HyB
      _ = S_CreditV F k x y N + ε_term := by rw [hBkf]
  iintro %z ⟨%Hzm, Hcz⟩
  have Hz01 : 0 < z ∧ z < 1 := mem_unifUnitSupport_real.mp Hzm
  have Hzr : 0 ≤ z ∧ z ≤ 1 := ⟨Hz01.1.le, Hz01.2.le⟩
  twp_pure
  twp_pures
  rcases hyz : ProbLangℝ.realLt y z with _ | _
  · -- `¬ y < z` (z ≤ y): run `Bii`.
    have hcz : SgAmp F k x N y ((kf : ℝ≥0∞) * ε_term) z
        = Bii_CreditV (SbiiCredit F k x N z ((kf : ℝ≥0∞) * ε_term)) k x := by
      simp [SgAmp, of_decide_eq_false hyz]
    ihave Hcz' : iprop(↯ (Bii_CreditV (SbiiCredit F k x N z ((kf : ℝ≥0∞) * ε_term)) k x)) $$ [Hcz]
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
      -- recurse `S k x z (N+1)`, cost `S_CreditV … z (N+1) + k·ε_term`.
      have hcb : SbiiCredit F k x N z ((kf : ℝ≥0∞) * ε_term) false
          = S_CreditV F k x z (N + 1) + (kf : ℝ≥0∞) * ε_term := by simp [SbiiCredit]
      ihave Hcb' : iprop(↯ (S_CreditV F k x z (N + 1) + (kf : ℝ≥0∞) * ε_term)) $$ [Hcbii]
      · rw [← hcb]; iexact Hcbii
      ihave ⟨Hexp, Hterm⟩ := ErrorCredit.split (GF := GF) $$ Hcb'
      twp_pure
      twp_pure
      rw [show ((N : ℤ) + 1) = ((N + 1 : ℕ) : ℤ) from by push_cast; ring]
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
    have hcz : SgAmp F k x N y ((kf : ℝ≥0∞) * ε_term) z = F N := by
      simp [SgAmp, of_decide_eq_true hyz]
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
    ⊢@{IProp GF} ↯ (S_CreditV F k x y N) -∗
      tglWp E pl(&S #(.int (k : ℤ)) #(.real x) #(.real y) #(.int (N : ℤ)))
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  iintro Hε_spec
  twp_pure
  twp_pure
  twp_pure
  twp_pure
  twp_pure
  twp_bind pl(urand)
  iapply (twp_urand_exp' (ε₂ := SgAmp F k x N y 0)
    (SgAmp_measurable F k x N y _) ?hint) $$ Hε_spec
  case hint =>
    exact _root_.le_of_eq
      (by rw [SgAmp_lintegral_eq F k x N y 0 hx0 hx1 hy0 hy1, mul_zero, add_zero])
  iintro %z ⟨%Hzm, Hcz⟩
  have Hz01 : 0 < z ∧ z < 1 := mem_unifUnitSupport_real.mp Hzm
  have Hzr : 0 ≤ z ∧ z ≤ 1 := ⟨Hz01.1.le, Hz01.2.le⟩
  twp_pure
  twp_pures
  rcases hyz : ProbLangℝ.realLt y z with _ | _
  · -- `z ≤ y`: run `Bii`.
    have hcz : SgAmp F k x N y 0 z = Bii_CreditV (SbiiCredit F k x N z 0) k x := by
      simp [SgAmp, of_decide_eq_false hyz]
    ihave Hcz' : iprop(↯ (Bii_CreditV (SbiiCredit F k x N z 0) k x)) $$ [Hcz]
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
      have hcb : SbiiCredit F k x N z 0 false = S_CreditV F k x z (N + 1) := by
        simp [SbiiCredit]
      ihave Hcb' : iprop(↯ (S_CreditV F k x z (N + 1))) $$ [Hcbii]
      · rw [← hcb]; iexact Hcbii
      have hz1 : z < 1 := Hz01.2
      have hz0 : 0 < z := Hz01.1
      twp_pure
      twp_pure
      rw [show ((N : ℤ) + 1) = ((N + 1 : ℕ) : ℤ) from by push_cast; ring]
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
  · have hcz : SgAmp F k x N y 0 z = F N := by simp [SgAmp, of_decide_eq_true hyz]
    twp_pures
    twp_value
    imodintro
    iexists N
    rw [← hcz]
    iframe Hcz
    itrivial

/-! ## The first-draw wrapper `S0` -/

/-- `S0 k x`: first-draw wrapper of `S` — draw `z`; return `#0` if `x < z` or
`Bii k x`, else recurse into `S k x z 1`. -/
@[pl_fold]
def S0 : Exp ℝ := pl%
  fun k, fun x,
    let z := urand;
    if x < z then #0 else (if &Bii k x then #0 else &S k x z #1)

/-- Weakest-precondition spec of `S0`: non-recursive — draw `z`; terminate at `#0`
if `x < z` or `Bii`, else hand off to `S` (its termination handled by `twp_S`). -/
theorem twp_S0 (E : CoPset) (F : ℕ → ℝ≥0∞) (M : ℝ≥0∞) (hnn : ∀ n, F n ≤ M)
    (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ⊢@{IProp GF} ↯ (S_CreditV F k x x 0) -∗
      tglWp E pl(&S0 #(.int (k : ℤ)) #(.real x))
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  iintro Hε
  twp_pure
  twp_pure
  twp_bind pl(urand)
  iapply (twp_urand_exp' (ε₂ := SgAmp F k x 0 x 0)
    (SgAmp_measurable F k x 0 x 0) ?hint) $$ Hε
  case hint =>
    exact _root_.le_of_eq
      (by rw [SgAmp_lintegral_eq F k x 0 x 0 hx0 hx1 hx0 hx1, mul_zero, add_zero])
  iintro %z ⟨%Hzm, Hcz⟩
  have Hz01 : 0 < z ∧ z < 1 := mem_unifUnitSupport_real.mp Hzm
  have Hzr : 0 ≤ z ∧ z ≤ 1 := ⟨Hz01.1.le, Hz01.2.le⟩
  twp_pure
  twp_pures
  rcases hyz : ProbLangℝ.realLt x z with _ | _
  · -- `¬ x < z` (z ≤ x): run `Bii`.
    have hcz : SgAmp F k x 0 x 0 z = Bii_CreditV (SbiiCredit F k x 0 z 0) k x := by
      simp [SgAmp, of_decide_eq_false hyz]
    ihave Hcz' : iprop(↯ (Bii_CreditV (SbiiCredit F k x 0 z 0) k x)) $$ [Hcz]
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
      have hcb : SbiiCredit F k x 0 z 0 false = S_CreditV F k x z (0 + 1) := by
        simp [SbiiCredit]
      ihave Hcb' : iprop(↯ (S_CreditV F k x z 1)) $$ [Hcbii]
      · rw [show S_CreditV F k x z 1 = S_CreditV F k x z (0 + 1) from rfl, ← hcb]; iexact Hcbii
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
    have hcz : SgAmp F k x 0 x 0 z = F 0 := by simp [SgAmp, of_decide_eq_true hyz]
    twp_pures
    twp_value
    imodintro
    iexists 0
    rw [← hcz]
    iframe Hcz
    itrivial

/-! ## The parity combinator `B` -/

/-- `B k x`: parity of `S0 k x` — returns `S0 k x rem 2 = 0`. -/
@[pl_fold]
def B : Exp ℝ := pl%
  fun k, fun x, (&S0 k x % #2 = #0)

/-- Distribution credit for `B`:
`exp(-x(2k+x)/(2k+2)) · F true + (1 - exp(…)) · F false`. -/
def B_CreditV (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  .ofReal (Real.exp (-x * (2 * k + x) / (2 * k + 2))) * F true +
  (1 - .ofReal (Real.exp (-x * (2 * k + x) / (2 * k + 2)))) * F false

/-- Credit `B` hands to `S0`, read off by parity of the `S0` result: even ↦ `F true`,
odd ↦ `F false` (`B` returns `S0 k x rem 2 = 0`). -/
def B_S0credit (F : Bool → ℝ≥0∞) : ℕ → ℝ≥0∞ :=
  fun n => if n % 2 = 0 then F true else F false

/-- Credit conservation for `B`: distributing `B_CreditV` through `S0` with the
parity budget `B_S0credit`. -/
theorem B_CreditV_S0_eq (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    B_CreditV F k x = S_CreditV (B_S0credit F) k x x 0 := by
  have hqnn : (0 : ℝ) ≤ (2 * (k : ℝ) + x) / (2 * k + 2) :=
    div_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
  have hp0 : (0 : ℝ) ≤ x * ((2 * (k : ℝ) + x) / (2 * k + 2)) := mul_nonneg hx0 hqnn
  have hp1 : x * ((2 * (k : ℝ) + x) / (2 * k + 2)) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) k, mul_nonneg (Nat.cast_nonneg (α := ℝ) k)
      (sub_nonneg.mpr hx1), mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  -- The `S`-diagonal credit is the `DecrTrial` parity credit at the scaled point.
  have hSeq : S_CreditV (B_S0credit F) k x x 0
      = RealDecrTrialCreditV (fun n => if n % 2 = 0 then F true else F false) 0
          (x * ((2 * (k : ℝ) + x) / (2 * k + 2))) := by
    unfold S_CreditV RealDecrTrialCreditV
    refine tsum_congr fun n => ?_
    rw [show Sμ k x x 0 n = RealDecrTrialμ0 (x * ((2 * (k : ℝ) + x) / (2 * k + 2))) n from by
          rw [Sμ, if_pos (Nat.zero_le n), Nat.sub_zero, Sμ0_eq_RealDecrTrialμ0],
        RealDecrTrialμ_base]
    simp only [B_S0credit]
  rw [hSeq, RealDecrTrialCreditV_parity (F true) (F false) hp0 hp1]
  have harg : Real.exp (-x * (2 * k + x) / (2 * k + 2))
      = Real.exp (-(x * ((2 * (k : ℝ) + x) / (2 * k + 2)))) := by congr 1; ring
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal (Real.exp (-(x * ((2 * (k : ℝ) + x) / (2 * k + 2)))))
      = ENNReal.ofReal (1 - Real.exp (-(x * ((2 * (k : ℝ) + x) / (2 * k + 2))))) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
  unfold B_CreditV
  rw [harg, hsub]

/-- Weakest-precondition spec of `B`: run `S0` and return the parity of its result. -/
theorem twp_B (E : CoPset) (F : Bool → ℝ≥0∞) (M : ℝ≥0∞) (Hnn : ∀ b, F b ≤ M)
    (k : ℕ) (x : ℝ) (Hx : 0 ≤ x ∧ x ≤ 1) :
    ⊢@{IProp GF} ↯ (B_CreditV F k x) -∗
      tglWp E pl(&B #(.int (k : ℤ)) #(.real x))
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v.1 = .lit (.bool b)⌝ ∗ ↯ (F b))) := by
  iintro Hε
  twp_pure
  twp_pure
  twp_bind pl(&S0 #(.int (k : ℤ)) #(.real x))
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ n : ℕ,
    ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (B_S0credit F n))))
  isplitl [Hε]
  · iapply (twp_S0 E (B_S0credit F) M (fun n => by
      simp only [B_S0credit]; split <;> exact Hnn _) k x Hx.1 Hx.2)
    iapply (ErrorCredit.ext (B_CreditV_S0_eq F k x Hx.1 Hx.2))
    iexact Hε
  iintro %v ⟨%n, %hn, Hcn⟩
  rcases v with ⟨w, hwlc⟩
  simp only at hn; subst hn
  -- Read off the parity `n rem 2 = 0`.
  twp_pures
  rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
  · -- `n` even: result `#true`, cost `F true`.
    rw [show (Int.ofNat n % 2 : ℤ) = 0 from by simp only [Int.ofNat_eq_natCast]; omega]
    twp_pures
    twp_value
    imodintro
    iexists true
    have hc : B_S0credit F n = F true := by simp only [B_S0credit, hpar]; rfl
    rw [← hc]
    iframe Hcn
    itrivial
  · -- `n` odd: result `#false`, cost `F false`.
    rw [show (Int.ofNat n % 2 : ℤ) = 1 from by simp only [Int.ofNat_eq_natCast]; omega]
    twp_pures
    twp_value
    imodintro
    iexists false
    have hc : B_S0credit F n = F false := by
      simp only [B_S0credit]; rw [if_neg (by omega)]
    rw [← hc]
    iframe Hcn
    itrivial

end
end Examples
end TotalEris
end ProbLang
