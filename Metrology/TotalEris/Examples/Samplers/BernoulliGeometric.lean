module

public import Metrology.TotalEris
public import Mathlib.Probability.Distributions.Geometric

@[expose] public section

/-! # Geometric sampler -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {rT : Type _} [ProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [ErisGS rT hlc GF]

structure AbstractBernoulli (e : Val rT) (γ : ↑unitInterval) where
  spec {E} : iprop%
    ⊢@{IProp GF}
      ∀ (F : Bool → ℝ≥0∞),
      ↯ (.ofReal γ * F true + (1 - .ofReal γ) * F false) -∗
      tglWp E pl(&e.1 #.unit) (fun (v : Val rT) => iprop%
        ∃ b : Bool, ⌜ v.1 = .lit (.bool b) ⌝ ∗ ↯ (F b))

@[pl_fold]
def GeometricTrial : Exp rT := pl%
  rec geo trial N := if trial #.unit then geo trial (N + #1) else N

/-- The PMF for the geometric distribution. `GeometricTrial` recurses while
`trial ()` returns `true` (probability `γ`) and returns on the first `false`
(probability `1 - γ`), so the number of steps `n` has PMF `γ^n · (1-γ)`.
(Rocq's def had `γ ↔ (1-γ)` swapped relative to this program; corrected here.) -/
def GeometricPMF (γ : ↑unitInterval) (n : ℕ) : ℝ≥0∞ :=
  .ofReal ((γ : ℝ) ^ n * (1 - γ))

/-- Geometric distribution, shifted right by `shiftR` (supported on `z ≥ shiftR`). -/
noncomputable def ShiftGeometricPMF (γ : ↑unitInterval) (shiftR z : ℤ) : ℝ≥0∞ :=
  if shiftR ≤ z then .ofReal ((γ : ℝ) ^ (z - shiftR).toNat * (1 - γ)) else 0

theorem shiftGeometricPMF_geometricPMF_eq (γ : ↑unitInterval) (n : ℕ) :
    GeometricPMF γ n = ShiftGeometricPMF γ 0 n := by
  simp [GeometricPMF, ShiftGeometricPMF]

/-- Expected value of a ℤ-valued random variable wrt. the shifted geometric
distribution, as a sum over the number of steps `k : ℕ` (`z = shiftR + k`). -/
def shiftGeometricPMF_expectation (γ : ↑unitInterval) (shiftR : ℤ) (F : ℤ → ℝ≥0∞) :=
  ∑'(k : ℕ), F (shiftR + k) * GeometricPMF γ k

/-- Error-amplification factor `1/γ`. Well-defined (`≥ 0`) for any `γ`; only
`> 1` when `0 < γ < 1` (see `one_lt_terminationFactor`). -/
def terminationFactor (γ : ↑unitInterval) : ℝ≥0 :=
  ⟨1 / (γ : ℝ), div_nonneg zero_le_one (unitInterval.nonneg γ)⟩

theorem one_lt_terminationFactor (γ : ↑unitInterval)
    (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) : 1 < terminationFactor γ := by
  have h : (1 : ℝ) < 1 / (γ : ℝ) := (one_lt_div hγ0).mpr hγ1
  rw [terminationFactor]
  exact_mod_cast h

def Famp (F : Int → ℝ≥0∞) (γ : ↑unitInterval) (shift : Int) (ε_term : ℝ≥0∞) :
    Bool → ℝ≥0∞
  | true => (shiftGeometricPMF_expectation γ (shift + 1) F) + terminationFactor γ * ε_term
  | false => F shift

/-- `GeometricPMF γ 0 = 1 - γ` (the stop probability). -/
theorem GeometricPMF_zero (γ : ↑unitInterval) :
    GeometricPMF γ 0 = 1 - ENNReal.ofReal (γ : ℝ) := by
  rw [GeometricPMF, pow_zero, one_mul, ENNReal.ofReal_sub 1 γ.2.1, ENNReal.ofReal_one]

/-- `GeometricPMF γ (k+1) = γ · GeometricPMF γ k`. -/
theorem GeometricPMF_succ (γ : ↑unitInterval) (k : ℕ) :
    GeometricPMF γ (k + 1) = ENNReal.ofReal (γ : ℝ) * GeometricPMF γ k := by
  have h : (γ : ℝ) ^ (k + 1) * (1 - (γ : ℝ)) = (γ : ℝ) * ((γ : ℝ) ^ k * (1 - (γ : ℝ))) := by
    ring
  rw [GeometricPMF, GeometricPMF, h, ENNReal.ofReal_mul γ.2.1]

/-- `γ · (1/γ) = 1` in `ℝ≥0∞`, for `0 < γ`. -/
theorem ofReal_mul_terminationFactor (γ : ↑unitInterval) (hγ0 : 0 < (γ : ℝ)) :
    ENNReal.ofReal (γ : ℝ) * (terminationFactor γ : ℝ≥0∞) = 1 := by
  rw [ENNReal.coe_nnreal_eq (terminationFactor γ),
    show ((terminationFactor γ : ℝ≥0) : ℝ) = 1 / (γ : ℝ) from rfl,
    ← ENNReal.ofReal_mul γ.2.1, mul_one_div, div_self hγ0.ne', ENNReal.ofReal_one]

/-- The geometric expectation recurrence:
`E[shift] = γ · E[shift+1] + (1-γ) · F shift`. -/
theorem shiftGeometricPMF_expectation_succ (γ : ↑unitInterval) (shift : ℤ) (F : ℤ → ℝ≥0∞) :
    shiftGeometricPMF_expectation γ shift F
      = ENNReal.ofReal (γ : ℝ) * shiftGeometricPMF_expectation γ (shift + 1) F
        + (1 - ENNReal.ofReal (γ : ℝ)) * F shift := by
  unfold shiftGeometricPMF_expectation
  rw [tsum_eq_zero_add' (f := fun k : ℕ => F (shift + ↑k) * GeometricPMF γ k) ENNReal.summable,
    add_comm]
  congr 1
  · -- tail: ∑' k, F(shift+(k+1))·PMF(k+1) = γ · ∑' k, F((shift+1)+k)·PMF k
    rw [← ENNReal.tsum_mul_left]
    congr 1; funext k
    rw [GeometricPMF_succ,
      show shift + (↑(k + 1) : ℤ) = (shift + 1) + ↑k by push_cast; ring]
    ring
  · -- head: F shift · PMF 0 = (1-γ)·F shift
    rw [Nat.cast_zero, add_zero, GeometricPMF_zero, mul_comm]

theorem twp_GeometricTrial {γ : ↑unitInterval} (shift : Int) (v : Val rT)
    (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Hspec : AbstractBernoulli (hlc := hlc) (GF := GF) v γ):
    ⊢@{IProp GF}
      ∀ (F : Int → ℝ≥0∞),
      ↯ (shiftGeometricPMF_expectation γ shift F) -∗
      tglWp E pl(&GeometricTrial &v.1 #(.int shift)) (fun (v : Val rT) => iprop%
        ∃ z : ℤ, ⌜ v.1 = .lit (.int z) ⌝ ∗ ⌜ shift ≤ z ⌝ ∗ ↯ (F z)) := by
  iintro %F Hε_spec
  -- Use fresh thin-air credit for termination proof
  iapply twp_err_pos solve_not_red
  iintro %ε_term %Hε_term_pos Hε_term
  -- Termination factor: recursive cases are guarded behind a probability γ event, so
  -- we can amplify ε_term by γ.
  have Hk1 : 1 < terminationFactor γ := one_lt_terminationFactor γ hγ0 hγ1
  irevert Hε_spec
  irevert %shift
  -- Apply credit contitioning
  iapply ErrorCredit.Induction.simple (k := terminationFactor γ) Hε_term_pos Hk1 $$ [] Hε_term
  imodintro
  iintro ⟨IH, Hε_term⟩ %shift Hε_spec
  -- Symbolic execution
  twp_pures
  twp_bind pl({v.fst} #.unit)
  -- Apply amplification at the random sampling step
  iapply tglWp_wand
  isplitl [Hε_spec Hε_term]
  · iapply (Hspec.spec (E := E)) $$ %(Famp F γ shift ε_term)
    icombine Hε_term Hε_spec as Hε
    iapply ErrorCredit.ext $$ Hε
    -- Math part: the geometric recurrence, plus `γ · (1/γ) = 1` collapsing the
    -- amplified termination credit back to `ε_term`.
    simp only [Famp]
    rw [shiftGeometricPMF_expectation_succ γ shift F, mul_add, ← mul_assoc,
      ofReal_mul_terminationFactor γ hγ0, one_mul]
    ring
  iintro %w' ⟨%b, %hret, Hε⟩
  rcases w' with ⟨w, hw, hlc⟩
  simp only at hret; subst hret
  rcases b
  · -- Terminating case: use `Famp false` credits to conclude
    twp_pures
    twp_value
    imodintro
    simp only [Exp.lit.injEq, BaseLit.int.injEq, Famp]
    iexists shift
    isplitr [Hε]
    · ipureintro; rfl
    · isplitr [Hε]
      · ipureintro; exact _root_.le_refl shift
      · iexact Hε
  · -- Recursive case: step the `if`/arithmetic so only the recursive call remains,
    -- then refocus it onto the *named* `GeometricTrial` constant via `twp_bind` (the
    -- stepped goal otherwise holds the unfolded `rec` value, which does not unify with
    -- the named-constant induction hypothesis). The refocused goal then matches `IH`.
    twp_pure
    twp_pure
    twp_bind pl(&GeometricTrial &v.1 #(.int (shift + 1)))
    -- Bridge the trivial bind-continuation to the induction hypothesis' post via `wand`.
    iapply (tglWp_wand (Φ := fun (v : Val rT) => iprop%
      ∃ z : ℤ, ⌜ v.1 = .lit (.int z) ⌝ ∗ ⌜ shift + 1 ≤ z ⌝ ∗ ↯ (F z)))
    isplitl [Hε IH]
    · -- Split the `Famp … true` credit `↯(exp(shift+1) + (1/γ)·ε_term)` into the
      -- shifted expectation (for the recursive spec) and the amplified termination
      -- credit `↯((1/γ)·ε_term)` = `↯(k·ε_term)` that feeds the induction hypothesis.
      ihave Hε' : iprop(↯(shiftGeometricPMF_expectation γ (shift + 1) F
          + (terminationFactor γ : ℝ≥0∞) * ε_term)) $$ [Hε]
      · rw [show shiftGeometricPMF_expectation γ (shift + 1) F
              + (terminationFactor γ : ℝ≥0∞) * ε_term
              = Famp F γ shift ε_term true from rfl]
        iexact Hε
      ihave ⟨Hexp, Hterm⟩ := ErrorCredit.split (GF := GF) $$ Hε'
      -- The recursive call now unifies syntactically with `IH` (both named).
      iapply IH $$ Hterm
      iexact Hexp
    -- Value continuation: the recursive call already returns a witnessed value;
    -- weaken its bound `shift + 1 ≤ z` to `shift ≤ z`.
    iintro %w ⟨%z, %hzeq, %hzle, Hf⟩
    iapply tglWp_value
    iexists z
    isplitr [Hf]
    · ipureintro; exact hzeq
    · isplitr [Hf]
      · ipureintro; omega
      · iexact Hf
