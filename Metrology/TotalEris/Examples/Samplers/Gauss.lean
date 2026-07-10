module

public import Metrology.TotalEris
public import Metrology.ProbLang.Reals
public import Metrology.TotalEris.Examples.Samplers.HalfBernNegExp
public import Metrology.TotalEris.Examples.Samplers.BernoulliGeometric
public import Metrology.TotalEris.Examples.Samplers.BernIter
public import Metrology.TotalEris.Examples.Samplers.Selector

@[expose] public section

/-!
# Discrete/continuous Gaussian sampler

* `G1 ()` samples a non-negative integer `k` from the (half-)discrete Gaussian
  `G1PMF k = exp(-k²/2) / Norm1`, via a geometric trial (`GeometricTrial BNEHalf`)
  followed by an accept/reject iteration (`IterTrial BNEHalf`).
* `G2 ()` extends `G1` to a full continuous Gaussian on `[k, k+1)`, returning a
  pair `(x, k)` of fractional real `x ∈ [0,1)` and integer `k`, with density
  `G2pdf k x = exp(-(x+k)²/2) / Norm2`; the accept step uses the selector `B`.
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [ErisGS ℝ hlc GF]

/-! ## Program -/
section program
/-- Iteration count `k·(k-1)`. -/
def IterN (k : ℕ) : ℕ := k * (k - 1)

@[pl_fold]
def G1 : Exp ℝ := pl%
  rec trial u :=
    let k := &GeometricTrial &BNEHalf #0;
    if &IterTrial &BNEHalf (k * (k - #1)) then k else trial #.unit

@[pl_fold]
def G2 : Exp ℝ := pl%
  rec trial u :=
    let k := &G1 #.unit;
    let x := urand;
    if &IterTrial (fun _u, &B k x) (k + #1) then (x, k) else trial #.unit

end program

/-! ## Distribution -/
section distribution
/-- Normalising constant of the discrete Gaussian. -/
def Norm1 : ℝ := ∑' k : ℕ, Real.exp (-(k : ℝ) ^ 2 / 2)

/-- Discrete-Gaussian PMF: `exp(-k²/2) / Norm1`. -/
def G1PMF (k : ℕ) : ℝ≥0∞ := .ofReal (Real.exp (-(k : ℝ) ^ 2 / 2) / Norm1)

open MeasureTheory in
/-- Normalising constant of the continuous Gaussian on `[k, k+1)`:
`∫₀¹ ∑ₖ exp(-(x+k)²/2) dx`. -/
def Norm2 : ℝ := ∫ x in (0 : ℝ)..1, ∑' k : ℕ, Real.exp (-((x + k) ^ 2) / 2)

/-- Continuous-Gaussian density: `exp(-(x+k)²/2) / Norm2`. -/
def G2pdf (k : ℕ) (x : ℝ) : ℝ≥0∞ := .ofReal (Real.exp (-((x + k) ^ 2) / 2) / Norm2)

end distribution

/-! ## Credit expectation -/
section creditExpectation
/-- Credit under the discrete-Gaussian PMF: `∑ₖ G1PMF k · F k`. -/
def G1CreditV (F : ℕ → ℝ≥0∞) : ℝ≥0∞ := ∑' k : ℕ, G1PMF k * F k

open MeasureTheory in
/-- Credit under the continuous-Gaussian density:
`∑ₖ ∫₀¹ G2pdf k x · F k x dx`. -/
def G2CreditV (F : ℕ → ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' k : ℕ, ∫⁻ x, G2pdf k x * F k x ∂(ProbLangℝ.unifUnit (T := ℝ))

end creditExpectation

/-! ## Credit kernel -/
section creditKernel
/-! ### `BNEHalf` as an abstract Bernoulli (G1 bias)

Both `GeometricTrial` and `IterTrial` are parameterised over a Bernoulli value
satisfying `AbstractBernoulli` / `AbstractBernoulliI`; `BNEHalf` (bias `exp(-½)`)
is that Bernoulli for the Gauss tower. -/

/-- `BNEHalf` packaged as a runtime value. `@[reducible]` so `BNEHalfVal.fst`
transparently unfolds to `BNEHalf` for the proof-mode unifier (`iapply`). -/
@[reducible] def BNEHalfVal : Val ℝ := ⟨BNEHalf, IsVal.lam (by is_lc), by is_lc⟩

/-- Success bias of `BNEHalf`: `exp(-½) ∈ (0,1)`. -/
noncomputable def γBNE : ↑unitInterval :=
  ⟨Real.exp (-1 / 2), (Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by norm_num)⟩

/-- `(γBNE : ℝ) = exp(-½)`. -/
theorem γBNE_coe : (γBNE : ℝ) = Real.exp (-1 / 2) := rfl

theorem γBNE_pos : (0 : ℝ) < (γBNE : ℝ) := Real.exp_pos _

theorem γBNE_nonneg : (0 : ℝ) ≤ (γBNE : ℝ) := γBNE_pos.le

theorem γBNE_lt_one : (γBNE : ℝ) < 1 := by
  rw [γBNE_coe]; exact Real.exp_lt_one_iff.mpr (by norm_num)

/-- Credit-shape bridge: the `AbstractBernoulli` credit is exactly `BNEHalfCreditV`. -/
theorem γBNE_credit_eq (F : Bool → ℝ≥0∞) :
    ENNReal.ofReal (γBNE : ℝ) * F true + (1 - ENNReal.ofReal (γBNE : ℝ)) * F false
      = BNEHalfCreditV F := by
  have ht : BNEHalfPMF true = ENNReal.ofReal (Real.exp (-1 / 2)) := rfl
  have hf : BNEHalfPMF false = ENNReal.ofReal (1 - Real.exp (-1 / 2)) := rfl
  simp only [BNEHalfCreditV, ht, hf, γBNE_coe]
  have h1 : (1 : ℝ≥0∞) - ENNReal.ofReal (Real.exp (-1 / 2))
      = ENNReal.ofReal (1 - Real.exp (-1 / 2)) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
  rw [h1]
  ring

/-- `BNEHalf` satisfies the `AbstractBernoulli` interface (`Bool`-indexed `F` is always
bounded, so `twp_BNEHalf`'s boundedness hypothesis is free). -/
theorem abstractBernoulli_BNEHalf : AbstractBernoulli (GF := GF) BNEHalfVal γBNE where
  spec := by
    intro E
    iintro %F Hε
    iapply (twp_BNEHalf E F (F true + F false)
      (by intro b; cases b <;> first | exact le_self_add | exact le_add_self))
    iapply (ErrorCredit.ext (γBNE_credit_eq F))
    iexact Hε

/-- `BNEHalf` satisfies the invariant-threading `AbstractBernoulliI` interface: `BNEHalf`
does not touch `I`, so it is simply framed across the draw. -/
theorem abstractBernoulliI_BNEHalf (I : IProp GF) :
    AbstractBernoulliI (hlc := hlc) (GF := GF) BNEHalfVal γBNE I where
  spec := by
    intro E
    iintro %F ⟨Hε, HI⟩
    iapply (tglWp_wand (Φ := fun w : Val ℝ => iprop(∃ b : Bool,
      ⌜w.1 = .lit (.bool b)⌝ ∗ ↯ (F b))))
    isplitl [Hε]
    · iapply (twp_BNEHalf E F (F true + F false)
        (by intro b; cases b <;> first | exact le_self_add | exact le_add_self))
      iapply (ErrorCredit.ext (γBNE_credit_eq F))
      iexact Hε
    iintro %w ⟨%b, %hb, Hfb⟩
    iexists b
    isplitr [Hfb HI]
    · ipureintro; exact hb
    · iframe Hfb HI

/-! ### `G1` per-draw kernel

`G1` is a reject loop whose "sub-sampler" is the `GeometricTrial`→`IterTrial`
composite (draw `k`, accept iff `IterTrial` returns `true`). The per-iteration
accept probability is a fixed constant `(1-γ)·Norm1`, so a single amplification
factor `G1Factor = 1/reject` drives termination (à la `NegExp`), with the
amplification threaded into the reject branch of the iteration continuation. -/

/-- Amplified iteration continuation: accept `↦ F k`, reject `↦ G1CreditV F` topped
up by termination credit `c`. -/
def G1IterContAmp (F : ℕ → ℝ≥0∞) (c : ℝ≥0∞) (k : ℕ) : Bool → ℝ≥0∞ :=
  fun b => if b then F k else G1CreditV F + c

/-- Per-drawn-`k` credit `GeometricTrial` must deliver: the `IterTrial` budget with
the amplified continuation. -/
def G1GeometricCredit (F : ℕ → ℝ≥0∞) (c : ℝ≥0∞) : ℤ → ℝ≥0∞ :=
  fun z => IterCreditV (G1IterContAmp F c z.toNat) γBNE (IterN z.toNat)

/-! ### `B k x` as an abstract Bernoulli (G2 bias)

`G2`'s accept step calls `IterTrial (λ_, B k x) (k+1)`, i.e. the geometric-style
iteration over the selector closure `λ_, B k x` from `Selector` (bias
`exp(-x(2k+x)/(2k+2))`). As with `BNEHalf` for `G1`, we package it as a
`γBkx`-biased `AbstractBernoulliI` so that `twp_IterTrial` applies. -/

/-- Bias of the per-`(k,x)` selector Bernoulli `B k x`: `exp(-x(2k+x)/(2k+2))`.
The exponent is clamped at `0` (`min 0 …`) so the value is `≤ 1` for **every** real
`x` (keeping `γBkx` a total map into `unitInterval`, as measurability requires). On the
intended domain `x ≥ 0` the exponent is already `≤ 0`, so `min 0 · = ·` is a no-op there
and the bias agrees with the raw `exp(-x(2k+x)/(2k+2))` (see `γBkx_credit_eq`). -/
noncomputable def γBkx (k : ℕ) (x : ℝ) : ↑unitInterval :=
  ⟨Real.exp (min 0 (-x * (2 * k + x) / (2 * k + 2))), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (min_le_left _ _)⟩

/-- The closure `λ_, B k x` packaged as a value. -/
@[reducible] def BkxVal (k : ℕ) (x : ℝ) : Val ℝ :=
  ⟨pl% (fun _u, &B #(.int (k : ℤ)) #(.real x)), IsVal.lam (by is_lc), by is_lc⟩

/-- On `x ≥ 0` the clamped exponent of `γBkx` is a no-op, so the bias is the raw `exp(…)`. -/
theorem γBkx_coe (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (γBkx k x : ℝ) = Real.exp (-x * (2 * k + x) / (2 * k + 2)) := by
  have harg : -x * (2 * (k : ℝ) + x) / (2 * k + 2) ≤ 0 := by
    rw [neg_mul, neg_div]
    exact neg_nonpos.mpr
      (div_nonneg (mul_nonneg hx (by linarith [Nat.cast_nonneg (α := ℝ) k])) (by positivity))
  show Real.exp (min 0 (-x * (2 * (k : ℝ) + x) / (2 * k + 2)))
      = Real.exp (-x * (2 * k + x) / (2 * k + 2))
  rw [min_eq_right harg]

/-- Credit-shape bridge: `BCreditV` is the `AbstractBernoulli` credit at bias `γBkx`. -/
theorem γBkx_credit_eq (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal (γBkx k x : ℝ) * F true + (1 - ENNReal.ofReal (γBkx k x : ℝ)) * F false
      = BCreditV F k x := by
  rw [γBkx_coe k hx]; rfl

/-- `λ_, B k x` satisfies `AbstractBernoulliI`: β-reduce the closure, apply `twp_B`,
frame the invariant. -/
theorem abstractBernoulliI_Bkx (k : ℕ) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (I : IProp GF) :
    AbstractBernoulliI (hlc := hlc) (GF := GF) (BkxVal k x) (γBkx k x) I where
  spec := by
    intro E
    iintro %F ⟨Hε, HI⟩
    twp_pure
    -- the closure β left an `open`/`close` tower around the closed `B`; collapse it.
    have hβ :
        (Exp.openRec 0 (Exp.lit .unit) (Exp.closeRec 0 (Var.internal 0) B) : Exp ℝ) = B := rfl
    rw [hβ]
    iapply (tglWp_wand (Φ := fun w : Val ℝ => iprop(∃ b : Bool,
      ⌜w.1 = .lit (.bool b)⌝ ∗ ↯ (F b))))
    isplitl [Hε]
    · iapply (twp_B E F (F true + F false)
        (by intro b; cases b <;> first | exact le_self_add | exact le_add_self) k x hx)
      iapply (ErrorCredit.ext (γBkx_credit_eq F k x hx.1))
      iexact Hε
    iintro %w ⟨%b, %hb, Hfb⟩
    iexists b
    isplitr [Hfb HI]
    · ipureintro; exact hb
    · iframe Hfb HI

/-! ### `G2` per-draw kernel

`G2` is a reject loop over `G1` (draw `k`) + `urand` (draw `x`) + the `B k x`
selector accept. The per-iteration accept mass is `Norm2/Norm1`, so a single
amplification factor `G2Factor = 1/reject` drives termination, threaded into the
reject branch of the iteration continuation — mirroring `G1`. -/

/-- Amplified accept/reject continuation for `G2`. -/
def G2IterContAmp (F : ℕ → ℝ → ℝ≥0∞) (c : ℝ≥0∞) (k : ℕ) (x : ℝ) : Bool → ℝ≥0∞ :=
  fun b => if b then F k x else G2CreditV F + c

/-- Per-`(k,x)` `IterTrial` budget (`IterCreditV` at bias `γBkx`, count `k+1`). -/
def G2CreditAmp (F : ℕ → ℝ → ℝ≥0∞) (c : ℝ≥0∞) (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  IterCreditV (G2IterContAmp F c k x) (γBkx k x) (k + 1)

open MeasureTheory in
/-- Per-drawn-`k` credit `G1` must deliver (the `x`-expectation of the `IterTrial` budget). -/
def G2G1Credit (F : ℕ → ℝ → ℝ≥0∞) (c : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, G2CreditAmp F c k x ∂(ProbLangℝ.unifUnit (T := ℝ))

/-- Accept probability of the `(k,x)` selector after `k+1` iterations: `ofReal(γBkx^(k+1))`. -/
def G2p (k : ℕ) (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((γBkx k x : ℝ) ^ (k + 1))

end creditKernel

/-! ## Measurability -/
section measurability
open MeasureTheory in
/-- Measurability of the per-draw `IterTrial` budget (consumed by `twp_urand_exp'`). -/
theorem measurable_g2CreditAmp (F : ℕ → ℝ → ℝ≥0∞) (hF : ∀ a, Measurable (F a))
    (c : ℝ≥0∞) (k : ℕ) :
    Measurable (G2CreditAmp F c k) := by
  -- `γBkx k x = exp(-x(2k+x)/(2k+2))`, so `x ↦ ofReal((γBkx k x)^(k+1))` is measurable.
  have hγ : Measurable (fun x : ℝ => ENNReal.ofReal ((γBkx k x : ℝ) ^ (k + 1))) :=
    ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp (by fun_prop)).pow_const (k + 1))
  -- `IterCreditV` unfolds to `ofReal(γ^(k+1))·F k x + (1 - ofReal(γ^(k+1)))·(G2CreditV F + c)`.
  show Measurable (fun x : ℝ => ENNReal.ofReal ((γBkx k x : ℝ) ^ (k + 1)) * F k x
      + (1 - ENNReal.ofReal ((γBkx k x : ℝ) ^ (k + 1))) * (G2CreditV F + c))
  exact (hγ.mul (hF k)).add ((hγ.const_sub 1).mul measurable_const)

/-- `G2p ≤ 1` (it is `ofReal` of a power of a value in `[0,1]`). -/
theorem G2p_le_one (k : ℕ) (x : ℝ) : G2p k x ≤ 1 := by
  rw [G2p, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (pow_le_one₀ (γBkx k x).2.1 (γBkx k x).2.2)

/-- `G2p k` is measurable (same shape as `measurable_g2CreditAmp`'s `hγ`). -/
theorem measurable_G2p (k : ℕ) : Measurable (G2p k) :=
  ENNReal.measurable_ofReal.comp
    ((Real.measurable_exp.comp (by fun_prop)).pow_const (k + 1))

open MeasureTheory in
/-- The fresh sample is uniform on `[0,1]`, a probability measure. -/
theorem unifUnit_lintegral_one :
    ∫⁻ _x : ℝ, (1 : ℝ≥0∞) ∂(ProbLangℝ.unifUnit (T := ℝ)) = 1 := by
  show ∫⁻ _x : ℝ, (1 : ℝ≥0∞) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = 1
  rw [lintegral_one, Measure.restrict_apply_univ, Real.volume_Icc]; norm_num

end measurability

/-! ## Credit conservation -/
section conservation
/-! ### `Norm1` bounds

The reject-loop factors are `1 / reject` with `reject = 1 - (1-γ)·Norm1`, so we need
`0 < reject < 1`. Both follow from `0 < Norm1` and the strict bound
`(1-γ)·Norm1 < 1`. The latter comes from dominating the Gaussian tail by a geometric
series: `exp(-k²/2) ≤ exp(-½)^k` (as `k ≤ k²`), hence
`Norm1 < ∑ₖ exp(-½)^k = (1-exp(-½))⁻¹`, i.e. `(1-γ)·Norm1 < 1` (strict: the `k=2`
term `exp(-2) < exp(-1)` is a strict drop). -/

/-- `exp(-k²/2) ≤ exp(-½)^k`, since `k ≤ k²`. Dominates the Gaussian tail by a
geometric series. -/
lemma normTerm_le_geometric (k : ℕ) :
    Real.exp (-(k : ℝ) ^ 2 / 2) ≤ Real.exp (-1 / 2) ^ k := by
  rw [← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr ?_
  have hnat : (k : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (by norm_num) k
  linarith [hnat]

/-- `∑' k, exp(-k²/2)` converges: dominated by the geometric series `∑ exp(-½)^k`. -/
theorem summable_normTerm : Summable (fun k : ℕ => Real.exp (-(k : ℝ) ^ 2 / 2)) := by
  have hγ0 : (0 : ℝ) ≤ Real.exp (-1 / 2) := γBNE_nonneg
  have hγ1 : Real.exp (-1 / 2) < 1 := γBNE_lt_one
  exact Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le)
    (fun k => normTerm_le_geometric k) (summable_geometric_of_lt_one hγ0 hγ1)

/-- `0 < Norm1` (the `k = 0` summand is `exp 0 = 1`). -/
theorem Norm1_pos : 0 < Norm1 := by
  unfold Norm1
  calc (0 : ℝ) < Real.exp (-((0 : ℕ) : ℝ) ^ 2 / 2) := Real.exp_pos _
    _ ≤ _ := summable_normTerm.le_tsum 0 (fun b _ => (Real.exp_pos _).le)

/-- `Norm1 < (1 - exp(-½))⁻¹`: the discrete-Gaussian tail is strictly dominated by
the geometric series `∑ exp(-½)^k` (strict at `k = 2`). -/
theorem Norm1_bound : Norm1 < (1 - Real.exp (-1 / 2))⁻¹ := by
  have hγ0 : (0 : ℝ) ≤ Real.exp (-1 / 2) := γBNE_nonneg
  have hγ1 : Real.exp (-1 / 2) < 1 := γBNE_lt_one
  rw [Norm1, ← tsum_geometric_of_lt_one hγ0 hγ1]
  refine Summable.tsum_lt_tsum_of_nonneg (i := 2) (fun k => (Real.exp_pos _).le)
    (fun k => normTerm_le_geometric k) ?_ (summable_geometric_of_lt_one hγ0 hγ1)
  · show Real.exp (-((2 : ℕ) : ℝ) ^ 2 / 2) < Real.exp (-1 / 2) ^ 2
    rw [← Real.exp_nat_mul]; exact Real.exp_lt_exp.mpr (by norm_num)

/-- `(1 - γBNE) · Norm1 < 1`: the `G1` reject loop's per-iteration accept mass is
strictly below `1` (so the amplification factor is finite). -/
theorem Norm1_reject_lt_one : (1 - (γBNE : ℝ)) * Norm1 < 1 := by
  rw [γBNE_coe]
  have hγ1 : Real.exp (-1 / 2) < 1 := γBNE_lt_one
  have h1γ : (0 : ℝ) < 1 - Real.exp (-1 / 2) := by linarith
  calc (1 - Real.exp (-1 / 2)) * Norm1
      < (1 - Real.exp (-1 / 2)) * (1 - Real.exp (-1 / 2))⁻¹ :=
        mul_lt_mul_of_pos_left Norm1_bound h1γ
    _ = 1 := mul_inv_cancel₀ (ne_of_gt h1γ)

/-- `G1` reject-loop amplification factor `= 1/reject`, `reject = 1 - (1-γ)·Norm1`. -/
noncomputable def G1Factor : ℝ≥0 :=
  ⟨1 / (1 - (1 - (γBNE : ℝ)) * Norm1),
    div_nonneg zero_le_one (by linarith [Norm1_reject_lt_one])⟩

/-- `1 < G1Factor` (the `G1` reject mass `(1-γ)·Norm1` is strictly positive). -/
theorem one_lt_G1Factor : 1 < G1Factor := by
  rw [← NNReal.coe_lt_coe, NNReal.coe_one]
  show (1 : ℝ) < 1 / (1 - (1 - (γBNE : ℝ)) * Norm1)
  have hrpos : 0 < 1 - (1 - (γBNE : ℝ)) * Norm1 := linarith [Norm1_reject_lt_one]
  rw [one_lt_div hrpos]
  have hγ1 : (γBNE : ℝ) < 1 := γBNE_lt_one
  have : 0 < (1 - (γBNE : ℝ)) * Norm1 := mul_pos (by linarith) Norm1_pos
  linarith

/-- The shift-`0` geometric distribution is a probability distribution. -/
theorem geometricPMF_tsum : ∑' k : ℕ, GeometricPMF γBNE k = 1 := by
  have hγ0 : (0 : ℝ) ≤ (γBNE : ℝ) := γBNE_nonneg
  have hγ1 : (γBNE : ℝ) < 1 := γBNE_lt_one
  have hdef : (fun k : ℕ => GeometricPMF γBNE k)
      = fun k => ENNReal.ofReal ((γBNE : ℝ) ^ k * (1 - γBNE)) := by funext k; rfl
  rw [hdef,
      ← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (by positivity) (by linarith))
        ((summable_geometric_of_lt_one hγ0 hγ1).mul_right _),
      tsum_mul_right, tsum_geometric_of_lt_one hγ0 hγ1,
      inv_mul_cancel₀ (sub_pos.mpr hγ1).ne', ENNReal.ofReal_one]

/-- The rejection acceptance mass: `∑ₖ P(draw k)·P(accept k) = (1-γ)·Norm1` (the total
weight of the discrete Gaussian before normalisation). Here `P(accept k) = γ^{k(k-1)}`. -/
theorem geom_iterN_tsum :
    ∑' k : ℕ, GeometricPMF γBNE k * ENNReal.ofReal ((γBNE : ℝ) ^ IterN k)
      = ENNReal.ofReal ((1 - (γBNE : ℝ)) * Norm1) := by
  have hγ1 : (γBNE : ℝ) < 1 := γBNE_lt_one
  have hterm : ∀ k : ℕ, GeometricPMF γBNE k * ENNReal.ofReal ((γBNE : ℝ) ^ IterN k)
      = ENNReal.ofReal ((1 - (γBNE : ℝ)) * Real.exp (-(k : ℝ) ^ 2 / 2)) := by
    intro k
    have hpmf : GeometricPMF γBNE k = ENNReal.ofReal ((γBNE : ℝ) ^ k * (1 - γBNE)) := rfl
    rw [hpmf, ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg γBNE.2.1 k) (by linarith))]
    congr 1
    have hkk : k + IterN k = k ^ 2 := by
      unfold IterN
      cases k with
      | zero => rfl
      | succ n => rw [Nat.succ_sub_one]; ring
    have hmul : (γBNE : ℝ) ^ k * (1 - (γBNE : ℝ)) * (γBNE : ℝ) ^ IterN k
        = (1 - (γBNE : ℝ)) * (γBNE : ℝ) ^ (k + IterN k) := by rw [pow_add]; ring
    rw [hmul, hkk, γBNE_coe, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  rw [tsum_congr hterm,
      ← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (by linarith) (Real.exp_pos _).le)
        (summable_normTerm.mul_left _),
      tsum_mul_left]
  rfl

/-! ### Norm2 bounds

The `G2` reject-loop factor is `1 / reject` with `reject = 1 - Norm2 / Norm1`, so we
need `0 < Norm2 < Norm1`. Fubini swaps the defining interval-integral/series; the
summand bound `∫₀¹ exp(-(x+k)²/2) ≤ exp(-k²/2)` (strict at `k = 0`) yields both
summability (dominated by `Norm1`) and `Norm2 < Norm1`. -/

open MeasureTheory in
/-- Fubini/Tonelli for `Norm2`: swap the interval integral and the series. Each
summand is continuous, and the integral-norm series is dominated by `Norm1`. -/
theorem Norm2_eq_tsum : Norm2 = ∑' k : ℕ, ∫ x in (0 : ℝ)..1, Real.exp (-((x + (k : ℝ)) ^ 2) / 2) := by
  have hpk : ∀ k : ℕ, (∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖Real.exp (-((x + (k : ℝ)) ^ 2) / 2)‖ₑ ∂volume)
      ≤ ENNReal.ofReal (Real.exp (-(k : ℝ) ^ 2 / 2)) := by
    intro k
    calc ∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖Real.exp (-((x + (k : ℝ)) ^ 2) / 2)‖ₑ ∂volume
        ≤ ∫⁻ _ in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Real.exp (-(k : ℝ) ^ 2 / 2)) ∂volume := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          have hkx : (0 : ℝ) ≤ (k : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx.1.le
          rw [← ofReal_norm, Real.norm_of_nonneg (Real.exp_pos _).le]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith [hx.1, hkx]))
      _ = ENNReal.ofReal (Real.exp (-(k : ℝ) ^ 2 / 2)) := by
          rw [setLIntegral_const, Real.volume_Ioc]; norm_num
  have hbound : (∑' k : ℕ, ∫⁻ x in Set.Ioc (0 : ℝ) 1,
      ‖Real.exp (-((x + (k : ℝ)) ^ 2) / 2)‖ₑ ∂volume) ≠ (⊤ : ℝ≥0∞) := by
    rw [← lt_top_iff_ne_top]
    calc (∑' k : ℕ, ∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖Real.exp (-((x + (k : ℝ)) ^ 2) / 2)‖ₑ ∂volume)
        ≤ ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(k : ℝ) ^ 2 / 2)) := ENNReal.tsum_le_tsum hpk
      _ = ENNReal.ofReal Norm1 := by
          rw [Norm1, ENNReal.ofReal_tsum_of_nonneg (fun k => (Real.exp_pos _).le) summable_normTerm]
      _ < (⊤ : ℝ≥0∞) := ENNReal.ofReal_lt_top
  rw [Norm2, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    MeasureTheory.integral_tsum (fun k => (Continuous.aestronglyMeasurable (by fun_prop))) hbound]
  exact tsum_congr fun k => (intervalIntegral.integral_of_le (by norm_num)).symm

open MeasureTheory in
/-- `∫₀¹ exp(-(x+k)²/2) dx ≤ exp(-k²/2)`, strict at `k = 0`. -/
theorem Norm2_summand_le (k : ℕ) :
    (∫ x in (0 : ℝ)..1, Real.exp (-((x + (k : ℝ)) ^ 2) / 2)) ≤ Real.exp (-(k : ℝ) ^ 2 / 2) := by
  have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (f := fun x => Real.exp (-((x + (k : ℝ)) ^ 2) / 2))
    (g := fun _ => Real.exp (-(k : ℝ) ^ 2 / 2))
    (Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1)
    (intervalIntegrable_const)
    (fun x hx => Real.exp_le_exp.mpr (by
      have hkx : (0 : ℝ) ≤ (k : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx.1
      nlinarith [hx.1, hkx]))
  rwa [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at h

open MeasureTheory in
/-- The `Norm2` summand series converges (dominated termwise by the `Norm1` summand). -/
theorem Norm2_summand_summable :
    Summable (fun k : ℕ => ∫ x in (0 : ℝ)..1, Real.exp (-((x + (k : ℝ)) ^ 2) / 2)) := by
  apply Summable.of_nonneg_of_le (fun k => intervalIntegral.integral_nonneg (by norm_num)
    (fun x _ => (Real.exp_pos _).le)) Norm2_summand_le summable_normTerm

open MeasureTheory in
/-- `0 < Norm2` (the `k = 0` summand is strictly positive on `(0,1)`). -/
theorem Norm2_pos : 0 < Norm2 := by
  rw [Norm2_eq_tsum]
  refine _root_.lt_of_lt_of_le ?_ (Norm2_summand_summable.le_tsum 0
    (fun b _ => intervalIntegral.integral_nonneg (by norm_num) (fun x _ => (Real.exp_pos _).le)))
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    (Continuous.intervalIntegrable (by fun_prop) _ _) (fun x _ => Real.exp_pos _) (by norm_num)

open MeasureTheory in
/-- `Norm2 < Norm1` (strict at `k = 0`: `∫₀¹ exp(-x²/2) dx < exp(-0²/2) = 1`). -/
theorem Norm2_lt_Norm1 : Norm2 < Norm1 := by
  rw [Norm2_eq_tsum, Norm1]
  refine Norm2_summand_summable.tsum_lt_tsum (i := 0) Norm2_summand_le ?_ summable_normTerm
  simp only [Nat.cast_zero, add_zero]
  -- strict at k = 0: `∫₀¹ exp(-x²/2) < exp(-0²/2)`.
  have key : (0 : ℝ) < ∫ x in (0 : ℝ)..1,
      (Real.exp (-(0 : ℝ) ^ 2 / 2) - Real.exp (-x ^ 2 / 2)) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (Continuous.intervalIntegrable (by fun_prop) 0 1) ?_ (by norm_num)
    intro x hx
    have : Real.exp (-x ^ 2 / 2) < Real.exp (-(0 : ℝ) ^ 2 / 2) :=
      Real.exp_lt_exp.mpr (by nlinarith [mul_pos hx.1 hx.1])
    linarith
  rw [intervalIntegral.integral_sub intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) 0 1), intervalIntegral.integral_const,
      sub_zero, smul_eq_mul, one_mul] at key
  linarith

/-- `G2` reject-loop amplification factor `= 1/reject`, `reject = 1 - Norm2/Norm1`. -/
noncomputable def G2Factor : ℝ≥0 :=
  ⟨1 / (1 - Norm2 / Norm1),
    div_nonneg zero_le_one (by rw [sub_nonneg, div_le_one Norm1_pos]; exact Norm2_lt_Norm1.le)⟩

/-- `1 < G2Factor` (the `G2` reject mass `Norm2/Norm1` is strictly positive). -/
theorem one_lt_G2Factor : 1 < G2Factor := by
  rw [← NNReal.coe_lt_coe, NNReal.coe_one]
  show (1 : ℝ) < 1 / (1 - Norm2 / Norm1)
  have h := Norm2_lt_Norm1
  have hNorm1 := Norm1_pos
  have hrpos : 0 < 1 - Norm2 / Norm1 := by rw [sub_pos, div_lt_one hNorm1]; exact h
  rw [one_lt_div hrpos]
  have : 0 < Norm2 / Norm1 := div_pos Norm2_pos hNorm1
  linarith

/-- `G1PMF` is a PMF: `∑ₖ exp(-k²/2)/Norm1 = Norm1/Norm1 = 1`. -/
theorem G1PMF_tsum : ∑' k : ℕ, G1PMF k = 1 := by
  simp only [G1PMF]
  have hsum : (∑' k : ℕ, Real.exp (-(k : ℝ) ^ 2 / 2) / Norm1) = 1 := by
    rw [tsum_div_const, ← Norm1, div_self (ne_of_gt Norm1_pos)]
  rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun k => div_nonneg (Real.exp_pos _).le Norm1_pos.le)
        (summable_normTerm.div_const _),
      hsum, ENNReal.ofReal_one]

open MeasureTheory in
/-- The `x`-integral of `G2pdf k` over the fresh sample. -/
theorem G2pdf_setLIntegral (k : ℕ) :
    ∫⁻ x, G2pdf k x ∂(ProbLangℝ.unifUnit (T := ℝ))
      = ENNReal.ofReal (∫ x in (0 : ℝ)..1, Real.exp (-((x + k) ^ 2) / 2) / Norm2) := by
  show ∫⁻ x in Set.Icc (0 : ℝ) 1, G2pdf k x ∂volume = _
  simp only [G2pdf]
  exact lintegral_ofReal_Icc (by norm_num) (by fun_prop)
    (fun r _ => div_nonneg (Real.exp_pos _).le Norm2_pos.le)

open MeasureTheory in
/-- `G2pdf` integrates to `1`: `∑ₖ ∫₀¹ exp(-(x+k)²/2)/Norm2 = Norm2/Norm2 = 1`. -/
theorem G2pdf_total : ∑' k : ℕ, ∫⁻ x, G2pdf k x ∂(ProbLangℝ.unifUnit (T := ℝ)) = 1 := by
  simp_rw [G2pdf_setLIntegral, intervalIntegral.integral_div]
  rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun k => div_nonneg (intervalIntegral.integral_nonneg (by norm_num)
          (fun x _ => (Real.exp_pos _).le)) Norm2_pos.le)
        (Norm2_summand_summable.div_const _),
      tsum_div_const, ← Norm2_eq_tsum, div_self (ne_of_gt Norm2_pos), ENNReal.ofReal_one]

/-! ### `G2pdf` distribution and accept-mass identities

PMF/normalisation facts for `G1PMF`/`G2pdf`, bounds on the accept probability `G2p`,
and the accept-mass identities (`G1PMF k · ∫ G2p·F = (Norm2/Norm1) · ∫ G2pdf·F`) that
feed the `G2` amplification collapse `G2G1_collapse`. -/

/-- Density identity: `G1PMF k · G2p k x = (Norm2/Norm1) · G2pdf k x` for `x ≥ 0`, since
`γBkx^(k+1) = exp(-x(2k+x)/2)` and `exp(-k²/2)·exp(-x(2k+x)/2) = exp(-(x+k)²/2)`. -/
theorem G1PMF_mul_accept (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    G1PMF k * G2p k x = ENNReal.ofReal (Norm2 / Norm1) * G2pdf k x := by
  have hpow : (γBkx k x : ℝ) ^ (k + 1) = Real.exp (-x * (2 * k + x) / 2) := by
    rw [γBkx_coe k hx, ← Real.exp_nat_mul]
    congr 1
    have h2 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
    push_cast; field_simp
  simp only [G1PMF, G2pdf, G2p]
  rw [hpow, ← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le Norm1_pos.le),
      ← ENNReal.ofReal_mul (div_nonneg Norm2_pos.le Norm1_pos.le)]
  congr 1
  have hrr : Real.exp (-(k : ℝ) ^ 2 / 2) / Norm1 * Real.exp (-x * (2 * k + x) / 2)
      = Real.exp (-(k : ℝ) ^ 2 / 2) * Real.exp (-x * (2 * k + x) / 2) / Norm1 := by ring
  have hadd : -(k : ℝ) ^ 2 / 2 + -x * (2 * k + x) / 2 = -((x + k) ^ 2) / 2 := by ring
  rw [hrr, ← Real.exp_add, hadd]
  field_simp [ne_of_gt Norm1_pos, ne_of_gt Norm2_pos]

open MeasureTheory in
/-- The accept contribution of the drawn `k`: `G1PMF k · ∫ G2p·F = (Norm2/Norm1) · ∫ G2pdf·F`. -/
theorem G2_accept_lintegral (F : ℕ → ℝ → ℝ≥0∞) (k : ℕ) :
    G1PMF k * ∫⁻ x, G2p k x * F k x ∂(ProbLangℝ.unifUnit (T := ℝ))
      = ENNReal.ofReal (Norm2 / Norm1)
          * ∫⁻ x, G2pdf k x * F k x ∂(ProbLangℝ.unifUnit (T := ℝ)) := by
  rw [← lintegral_const_mul' (G1PMF k) _ (by rw [G1PMF]; exact ENNReal.ofReal_ne_top),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  show ∫⁻ x in Set.Icc (0 : ℝ) 1, _ ∂volume = ∫⁻ x in Set.Icc (0 : ℝ) 1, _ ∂volume
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [← mul_assoc, G1PMF_mul_accept k hx.1, mul_assoc]

open MeasureTheory in
/-- The accept mass of the drawn `k`: `G1PMF k · ∫ G2p = (Norm2/Norm1) · ∫ G2pdf`. -/
theorem G2_accept_mass (k : ℕ) :
    G1PMF k * ∫⁻ x, G2p k x ∂(ProbLangℝ.unifUnit (T := ℝ))
      = ENNReal.ofReal (Norm2 / Norm1) * ∫⁻ x, G2pdf k x ∂(ProbLangℝ.unifUnit (T := ℝ)) := by
  have h := G2_accept_lintegral (fun _ _ => 1) k
  simpa only [mul_one] using h

/-- Amplification collapse: summing the amplified geometric credit over `k` recovers
`G1CreditV F` plus the reject-weighted top-up (`reject · G1Factor = 1`). -/
theorem G1Geometric_collapse (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    shiftGeometricPMFCreditV γBNE 0 (G1GeometricCredit F ((G1Factor : ℝ≥0∞) * ε))
      = G1CreditV F + ε := by
  have hγ1 : (γBNE : ℝ) < 1 := γBNE_lt_one
  have hrej : (0 : ℝ) < 1 - (1 - (γBNE : ℝ)) * Norm1 := by linarith [Norm1_reject_lt_one]
  set c := (G1Factor : ℝ≥0∞) * ε with hc
  set R := ENNReal.ofReal ((1 - (γBNE : ℝ)) * Norm1) with hR
  have hR1 : R ≤ 1 := by
    rw [hR, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [Norm1_reject_lt_one])
  have hak1 : ∀ k, ENNReal.ofReal ((γBNE : ℝ) ^ IterN k) ≤ 1 := fun k => by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (pow_le_one₀ γBNE.2.1 hγ1.le)
  have hpmf (k : ℕ) : GeometricPMF γBNE k = ENNReal.ofReal ((γBNE : ℝ) ^ k * (1 - γBNE)) := rfl
  have hkk (k : ℕ) : IterN k + k = k ^ 2 := by
    unfold IterN
    cases k with
    | zero => rfl
    | succ n => rw [Nat.succ_sub_one]; ring
  -- per-term accept mass · `G1PMF`.
  have hpterm : ∀ k, ENNReal.ofReal ((γBNE : ℝ) ^ IterN k) * GeometricPMF γBNE k = R * G1PMF k := by
    intro k
    rw [hR, G1PMF, hpmf k,
        ← ENNReal.ofReal_mul (pow_nonneg γBNE.2.1 _),
        ← ENNReal.ofReal_mul (mul_nonneg (by linarith) Norm1_pos.le)]
    congr 1
    have hmul : (γBNE : ℝ) ^ IterN k * ((γBNE : ℝ) ^ k * (1 - (γBNE : ℝ)))
        = (1 - (γBNE : ℝ)) * (γBNE : ℝ) ^ (IterN k + k) := by rw [pow_add]; ring
    have hexp : (γBNE : ℝ) ^ k ^ 2 = Real.exp (-(k : ℝ) ^ 2 / 2) := by
      rw [γBNE_coe, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hmul, hkk k, hexp]
    field_simp [ne_of_gt Norm1_pos]
  have hRfin : (∑' k : ℕ, ENNReal.ofReal ((γBNE : ℝ) ^ IterN k) * GeometricPMF γBNE k) = R := by
    rw [tsum_congr fun k => mul_comm _ _]; exact geom_iterN_tsum
  -- the reject mass sums to `1 - R`.
  have hrejsum : (∑' k : ℕ, (1 - ENNReal.ofReal ((γBNE : ℝ) ^ IterN k)) * GeometricPMF γBNE k)
      = 1 - R := by
    have hfun :
        (fun k : ℕ => (1 - ENNReal.ofReal ((γBNE : ℝ) ^ IterN k)) * GeometricPMF γBNE k)
          = fun k => GeometricPMF γBNE k
              - ENNReal.ofReal ((γBNE : ℝ) ^ IterN k) * GeometricPMF γBNE k := by
      funext k
      rw [ENNReal.sub_mul (fun _ _ => by simp [GeometricPMF]), one_mul]
    rw [hfun,
      ENNReal.tsum_sub (by rw [hRfin, hR]; exact ENNReal.ofReal_ne_top)
        (fun k => by
          nth_rewrite 2 [← one_mul (GeometricPMF γBNE k)]
          exact mul_le_mul_right' (hak1 k) _),
      geometricPMF_tsum, hRfin]
  -- the summand, split into accept / reject contributions.
  have hgeo : ∀ k : ℕ, G1GeometricCredit F c (0 + (k : ℤ)) * GeometricPMF γBNE k
      = R * G1PMF k * F k
        + (1 - ENNReal.ofReal ((γBNE : ℝ) ^ IterN k)) * GeometricPMF γBNE k * (G1CreditV F + c) := by
    intro k
    have h0 : (0 : ℤ) + (k : ℤ) = (k : ℤ) := by ring
    have hgc : G1GeometricCredit F c (k : ℤ)
        = ENNReal.ofReal ((γBNE : ℝ) ^ IterN k) * F k
            + (1 - ENNReal.ofReal ((γBNE : ℝ) ^ IterN k)) * (G1CreditV F + c) := rfl
    rw [h0, hgc, add_mul, ← hpterm k]
    ring
  unfold shiftGeometricPMFCreditV
  have hacc : (∑' k : ℕ, R * G1PMF k * F k) = R * G1CreditV F := by
    rw [G1CreditV, ← ENNReal.tsum_mul_left]; exact tsum_congr fun k => by rw [mul_assoc]
  have hrej' : (∑' k : ℕ, (1 - ENNReal.ofReal ((γBNE : ℝ) ^ IterN k)) * GeometricPMF γBNE k
        * (G1CreditV F + c))
      = (G1CreditV F + c) * (1 - R) := by
    rw [ENNReal.tsum_mul_right, hrejsum, mul_comm]
  rw [tsum_congr hgeo, ENNReal.tsum_add, hacc, hrej']
  -- rejection algebra: `R·X + (X+c)·(1-R) = X + c·(1-R)`, and `c·(1-R) = ε`.
  have halg : R * G1CreditV F + (G1CreditV F + c) * (1 - R)
      = G1CreditV F * (R + (1 - R)) + c * (1 - R) := by ring
  rw [halg, add_tsub_cancel_of_le hR1, mul_one]
  congr 1
  -- `c·(1-R) = ε`, using `G1Factor · reject = 1`.
  have h1R : (1 : ℝ≥0∞) - R = ENNReal.ofReal (1 - (1 - (γBNE : ℝ)) * Norm1) := by
    rw [hR, ENNReal.ofReal_sub _ (mul_nonneg (by linarith) Norm1_pos.le), ENNReal.ofReal_one]
  have hFac : (↑G1Factor : ℝ≥0∞)
      = ENNReal.ofReal (1 / (1 - (1 - (γBNE : ℝ)) * Norm1)) := by
    rw [G1Factor, ← ENNReal.ofReal_coe_nnreal]; rfl
  have hcancel : (↑G1Factor : ℝ≥0∞)
      * ENNReal.ofReal (1 - (1 - (γBNE : ℝ)) * Norm1) = 1 := by
    rw [hFac, ← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel (ne_of_gt hrej),
      ENNReal.ofReal_one]
  rw [hc, h1R, mul_right_comm, hcancel, one_mul]

open MeasureTheory in
/-- Amplification collapse at the `G1` level: accept mass `Norm2/Norm1` recovers
`G2CreditV F`, and reject mass `1 - Norm2/Norm1` cancels via `G2Factor · reject = 1`. -/
theorem G2G1_collapse (F : ℕ → ℝ → ℝ≥0∞) (hFm : ∀ a, Measurable (F a)) (ε : ℝ≥0∞) :
    G1CreditV (G2G1Credit F ((G2Factor : ℝ≥0∞) * ε)) = G2CreditV F + ε := by
  set c : ℝ≥0∞ := (G2Factor : ℝ≥0∞) * ε with hc
  have hrej_pos : (0 : ℝ) < 1 - Norm2 / Norm1 := by
    rw [sub_pos, div_lt_one Norm1_pos]; exact Norm2_lt_Norm1
  have hρ_le : ENNReal.ofReal (Norm2 / Norm1) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by rw [div_le_one Norm1_pos]; exact Norm2_lt_Norm1.le)
  have hq1 : ∀ k, (∫⁻ x, G2p k x ∂(ProbLangℝ.unifUnit (T := ℝ))) ≤ 1 := fun k =>
    _root_.le_trans (lintegral_mono (fun x => G2p_le_one k x)) unifUnit_lintegral_one.le
  have hgm_mul : ∀ k, ENNReal.ofReal (Norm2 / Norm1)
      * ∫⁻ x, G2pdf k x ∂(ProbLangℝ.unifUnit (T := ℝ)) ≤ G1PMF k := fun k => by
    rw [← G2_accept_mass k]
    exact (mul_le_mul_left' (hq1 k) (G1PMF k)).trans (_root_.le_of_eq (mul_one _))
  -- `∫(1 - G2p) = 1 - ∫G2p`.
  have h1mp : ∀ k, (∫⁻ x, (1 - G2p k x) ∂(ProbLangℝ.unifUnit (T := ℝ)))
      = 1 - ∫⁻ x, G2p k x ∂(ProbLangℝ.unifUnit (T := ℝ)) := fun k => by
    rw [MeasureTheory.lintegral_sub (measurable_G2p k) (ne_top_of_le_ne_top ENNReal.one_ne_top (hq1 k))
          (Filter.Eventually.of_forall (fun x => G2p_le_one k x)), unifUnit_lintegral_one]
  -- reject mass sums to `1 - Norm2/Norm1`.
  have hfun :
      (fun k : ℕ => (1 - ∫⁻ x, G2p k x ∂(ProbLangℝ.unifUnit (T := ℝ))) * G1PMF k)
        = fun k => G1PMF k
            - ENNReal.ofReal (Norm2 / Norm1)
              * ∫⁻ x, G2pdf k x ∂(ProbLangℝ.unifUnit (T := ℝ)) := by
    funext k
    rw [ENNReal.sub_mul (fun _ _ => by rw [G1PMF]; exact ENNReal.ofReal_ne_top), one_mul,
        mul_comm (∫⁻ x, G2p k x ∂(ProbLangℝ.unifUnit (T := ℝ))) (G1PMF k), G2_accept_mass k]
  have hrejsum : (∑' k : ℕ, (1 - ∫⁻ x, G2p k x ∂(ProbLangℝ.unifUnit (T := ℝ))) * G1PMF k)
      = 1 - ENNReal.ofReal (Norm2 / Norm1) := by
    rw [hfun,
      ENNReal.tsum_sub
        (by rw [ENNReal.tsum_mul_left, G2pdf_total, mul_one]
            exact ne_top_of_le_ne_top ENNReal.one_ne_top hρ_le) hgm_mul,
      G1PMF_tsum, ENNReal.tsum_mul_left, G2pdf_total, mul_one]
  -- accept contribution sums to `(Norm2/Norm1) · G2CreditV F`.
  have haccsum : (∑' k : ℕ, ENNReal.ofReal (Norm2 / Norm1)
      * ∫⁻ x, G2pdf k x * F k x ∂(ProbLangℝ.unifUnit (T := ℝ)))
      = ENNReal.ofReal (Norm2 / Norm1) * G2CreditV F := by
    rw [ENNReal.tsum_mul_left]; rfl
  -- per-`k` split of `G1PMF k · G2G1Credit` into accept + reject.
  have hsplit : ∀ k : ℕ, G1PMF k * G2G1Credit F c k
      = ENNReal.ofReal (Norm2 / Norm1) * (∫⁻ x, G2pdf k x * F k x ∂(ProbLangℝ.unifUnit (T := ℝ)))
        + (1 - ∫⁻ x, G2p k x ∂(ProbLangℝ.unifUnit (T := ℝ))) * G1PMF k * (G2CreditV F + c) := by
    intro k
    have hamp : (fun x => G2CreditAmp F c k x)
        = fun x => G2p k x * F k x + (1 - G2p k x) * (G2CreditV F + c) := by
      funext x; rw [G2CreditAmp, IterCreditV]; rfl
    rw [G2G1Credit, hamp,
        lintegral_add_left ((measurable_G2p k).mul (hFm k)),
        lintegral_mul_const _ ((measurable_G2p k).const_sub 1),
        mul_add, G2_accept_lintegral F k, h1mp k]
    ring
  rw [G1CreditV, tsum_congr hsplit, ENNReal.tsum_add, haccsum, ENNReal.tsum_mul_right, hrejsum]
  -- rejection algebra: `ρ·X + (X+c)·(1-ρ) = X + c·(1-ρ)`, and `c·(1-ρ) = ε`.
  have halg : ENNReal.ofReal (Norm2 / Norm1) * G2CreditV F
        + (1 - ENNReal.ofReal (Norm2 / Norm1)) * (G2CreditV F + c)
      = G2CreditV F * (ENNReal.ofReal (Norm2 / Norm1) + (1 - ENNReal.ofReal (Norm2 / Norm1)))
        + c * (1 - ENNReal.ofReal (Norm2 / Norm1)) := by ring
  rw [halg, add_tsub_cancel_of_le hρ_le, mul_one]
  congr 1
  have h1ρ : (1 : ℝ≥0∞) - ENNReal.ofReal (Norm2 / Norm1) = ENNReal.ofReal (1 - Norm2 / Norm1) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (div_nonneg Norm2_pos.le Norm1_pos.le)]
  have hFac : (↑G2Factor : ℝ≥0∞) = ENNReal.ofReal (1 / (1 - Norm2 / Norm1)) := by
    rw [G2Factor, ← ENNReal.ofReal_coe_nnreal]; rfl
  have hcancel : (↑G2Factor : ℝ≥0∞) * ENNReal.ofReal (1 - Norm2 / Norm1) = 1 := by
    rw [hFac, ← ENNReal.ofReal_mul (div_nonneg zero_le_one hrej_pos.le),
        one_div_mul_cancel (ne_of_gt hrej_pos), ENNReal.ofReal_one]
  rw [hc, h1ρ, mul_right_comm, hcancel, one_mul]

end conservation

/-! ## Specification -/
section specification
/-- `G1 ()` samples `n` from the discrete Gaussian. -/
theorem twp_G1 (E : CoPset) (F : ℕ → ℝ≥0∞) (M : ℝ≥0∞) (Hnn : ∀ n, F n ≤ M) :
    ⊢@{IProp GF} ↯ (G1CreditV F) -∗
      tglWp E pl(&G1 #.unit)
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  iintro Hε_spec
  iapply twp_err_pos solve_not_red
  iintro %ε_term %Hε_pos Hε_term
  set kf : ℝ≥0 := G1Factor
  have Hk1 : 1 < kf := one_lt_G1Factor
  irevert Hε_spec
  iapply ErrorCredit.Induction.simple (k := kf) Hε_pos Hk1 $$ [] Hε_term
  imodintro
  iintro ⟨IH, Hε_term⟩ Hε_spec
  -- unfold `rec` + β the unused arg, exposing `let k := GeometricTrial BNEHalf 0`.
  twp_pure
  twp_pure
  twp_bind pl(&GeometricTrial &BNEHalfVal.1 #(.int (0 : ℤ)))
  icombine Hε_spec Hε_term as Hε
  -- Draw `k` from the geometric; the amplified per-`k` `IterTrial` budget collapses
  -- back to `G1CreditV F + ε_term`.
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ z : ℤ,
    ⌜v.1 = .lit (.int z)⌝ ∗ ⌜(0 : ℤ) ≤ z⌝ ∗ ↯ (G1GeometricCredit F ((kf : ℝ≥0∞) * ε_term) z))))
  isplitl [Hε]
  · iapply (twp_GeometricTrial (γ := γBNE) 0 BNEHalfVal γBNE_pos γBNE_lt_one
        abstractBernoulli_BNEHalf)
      $$ %(G1GeometricCredit F ((kf : ℝ≥0∞) * ε_term))
    iapply (ErrorCredit.ext (G1Geometric_collapse F ε_term).symm)
    iexact Hε
  iintro %vk ⟨%z, %hz, %hz0, Hck⟩
  rcases vk with ⟨wk, hwlck⟩
  simp only at hz; subst hz
  -- `hz0 : 0 ≤ z` now comes directly from the strengthened `twp_GeometricTrial` spec.
  -- β `let k := #z`, focus the `IterTrial` call, evaluate its `k(k-1)` argument.
  twp_pure
  have hck : G1GeometricCredit F ((kf : ℝ≥0∞) * ε_term) z
      = IterCreditV (G1IterContAmp F ((kf : ℝ≥0∞) * ε_term) z.toNat) γBNE (IterN z.toNat) := rfl
  twp_bind pl(&IterTrial &BNEHalf (#(.int z) * (#(.int z) - #1)))
  twp_pure
  twp_pure
  have hzn : (z * (z - 1)) = ((IterN z.toNat : ℕ) : ℤ) := by
    rw [IterN]
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, z = (k : ℤ) := ⟨z.toNat, (Int.toNat_of_nonneg hz0).symm⟩
    simp only [Int.toNat_natCast]
    cases k with
    | zero => simp
    | succ k => push_cast; ring
  rw [hzn]
  iapply (tglWp_wand (Φ := fun w : Val ℝ => iprop(∃ b : Bool,
    ⌜w.1 = .lit (.bool b)⌝ ∗ ↯ (G1IterContAmp F ((kf : ℝ≥0∞) * ε_term) z.toNat b) ∗ ⌜True⌝)))
  isplitl [Hck]
  · iapply (twp_IterTrial E BNEHalfVal γBNE (iprop(⌜True⌝))
      (abstractBernoulliI_BNEHalf (iprop(⌜True⌝)))
      (G1IterContAmp F ((kf : ℝ≥0∞) * ε_term) z.toNat) (IterN z.toNat))
    isplitl [Hck]
    · rw [← hck]; iexact Hck
    · ipureintro; trivial
  iintro %vb ⟨%b, %hb, Hcb, %_ht⟩
  rcases vb with ⟨wb, hwlcb⟩
  simp only at hb; subst hb
  cases b with
  | true =>
    -- accept: return `k = z`, cost `F z.toNat`.
    have hcb : G1IterContAmp F ((kf : ℝ≥0∞) * ε_term) z.toNat true = F z.toNat := by
      simp [G1IterContAmp]
    twp_pures
    twp_value
    imodintro
    iexists z.toNat
    isplitr [Hcb]
    · ipureintro
      have hz : Int.ofNat z.toNat = z := Int.toNat_of_nonneg hz0
      rw [hz]
    · rw [← hcb]; iexact Hcb
  | false =>
    -- reject: recurse `trial ()`, cost `G1CreditV F + k·ε_term`.
    have hcb : G1IterContAmp F ((kf : ℝ≥0∞) * ε_term) z.toNat false
        = G1CreditV F + (kf : ℝ≥0∞) * ε_term := by simp [G1IterContAmp]
    ihave Hcb' : iprop(↯ (G1CreditV F + (kf : ℝ≥0∞) * ε_term)) $$ [Hcb]
    · rw [← hcb]; iexact Hcb
    ihave ⟨Hexp, Hterm⟩ := ErrorCredit.split (GF := GF) $$ Hcb'
    -- fire the `if #false` → else (single step — a greedy `twp_pures` would unfold
    -- the inlined `&G1` self-ref body and diverge at `whnf`).
    twp_pure
    twp_bind pl(&G1 #.unit)
    iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ n : ℕ,
      ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))))
    isplitl [Hexp Hterm IH]
    · iapply IH $$ Hterm
      iexact Hexp
    iintro %w Hpost
    iapply tglWp_value
    iexact Hpost

/-- `G2 ()` returns `(x, k)` from the continuous Gaussian. -/
theorem twp_G2 (E : CoPset) (F : ℕ → ℝ → ℝ≥0∞) (M : ℝ≥0∞)
    (Hnn : ∀ x k, 0 ≤ x → x ≤ 1 → F k x ≤ M) (hFm : ∀ a, Measurable (F a)) :
    ⊢@{IProp GF} ↯ (G2CreditV F) -∗
      tglWp E pl(&G2 #.unit)
        (fun p : Val ℝ => iprop(∃ (k : ℕ) (r : ℝ),
          ⌜0 ≤ r ∧ r < 1⌝ ∗
          ⌜p.1 = .pair (.lit (.real r)) (.lit (.int (Int.ofNat k)))⌝ ∗ ↯ (F k r))) := by
  have Hk1 : 1 < G2Factor := one_lt_G2Factor
  iintro Hε_spec
  iapply twp_err_pos solve_not_red
  iintro %ε_term %Hε_pos Hε_term
  set kf : ℝ≥0 := G2Factor
  irevert Hε_spec
  iapply ErrorCredit.Induction.simple (k := kf) Hε_pos Hk1 $$ [] Hε_term
  imodintro
  iintro ⟨IH, Hε_term⟩ Hε_spec
  twp_pure
  twp_pure
  twp_bind pl(&G1 #.unit)
  icombine Hε_spec Hε_term as Hε
  -- Draw `k` from `G1` with the amplified per-`k` budget; collapse back to `G2CreditV + ε`.
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ n : ℕ,
    ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (G2G1Credit F ((kf : ℝ≥0∞) * ε_term) n))))
  isplitl [Hε]
  · iapply (twp_G1 E (G2G1Credit F ((kf : ℝ≥0∞) * ε_term))
      (M + G2CreditV F + (kf : ℝ≥0∞) * ε_term)
      (by
        intro n
        rw [G2G1Credit]
        calc ∫⁻ x, G2CreditAmp F ((kf : ℝ≥0∞) * ε_term) n x ∂(ProbLangℝ.unifUnit (T := ℝ))
            ≤ ∫⁻ _x, (M + (G2CreditV F + (kf : ℝ≥0∞) * ε_term))
                ∂(ProbLangℝ.unifUnit (T := ℝ)) := by
              apply MeasureTheory.lintegral_mono_ae
              filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
              have ht : G2IterContAmp F ((kf : ℝ≥0∞) * ε_term) n x true = F n x := by simp [G2IterContAmp]
              have hf : G2IterContAmp F ((kf : ℝ≥0∞) * ε_term) n x false
                  = G2CreditV F + (kf : ℝ≥0∞) * ε_term := by simp [G2IterContAmp]
              rw [G2CreditAmp, IterCreditV, ht, hf]
              exact add_le_add
                ((mul_le_mul' (G2p_le_one n x) (Hnn x n hx.1 hx.2)).trans
                  (_root_.le_of_eq (one_mul M)))
                ((mul_le_mul' tsub_le_self le_rfl).trans (_root_.le_of_eq (one_mul _)))
          _ = M + (G2CreditV F + (kf : ℝ≥0∞) * ε_term) := by
              rw [MeasureTheory.lintegral_const]
              show _ * (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ = _
              rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
                ENNReal.ofReal_one, mul_one]
          _ = M + G2CreditV F + (kf : ℝ≥0∞) * ε_term := (add_assoc _ _ _).symm))
    iapply (ErrorCredit.ext (G2G1_collapse F hFm ε_term).symm)
    iexact Hε
  iintro %vk ⟨%k, %hk, Hck⟩
  rcases vk with ⟨wk, hwlck⟩
  simp only at hk; subst hk
  -- β `let k := #k`, draw `x ← urand` with the `IterTrial` budget `G2CreditAmp`.
  twp_pure
  twp_bind pl(urand)
  iapply (twp_urand_exp' (ε₂ := G2CreditAmp F ((kf : ℝ≥0∞) * ε_term) k)
    (measurable_g2CreditAmp F hFm ((kf : ℝ≥0∞) * ε_term) k) ?hint) $$ Hck
  case hint =>
    have hdef : G2G1Credit F ((kf : ℝ≥0∞) * ε_term) k
        = ∫⁻ x, G2CreditAmp F ((kf : ℝ≥0∞) * ε_term) k x ∂(ProbLangℝ.unifUnit (T := ℝ)) := rfl
    rw [hdef]
  iintro %x ⟨%Hxm, Hcx⟩
  have Hx01 : 0 < x ∧ x < 1 := mem_unifUnitSupport_real.mp Hxm
  have Hxr : 0 ≤ x ∧ x ≤ 1 := ⟨Hx01.1.le, Hx01.2.le⟩
  -- β `let x := #x`, run `IterTrial (λ_, B k x) (k+1)`.
  twp_pure
  twp_bind pl(&IterTrial &(BkxVal k x).1 (#(.int (k : ℤ)) + #1))
  twp_pure
  have hk1 : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hk1]
  have hck : G2CreditAmp F ((kf : ℝ≥0∞) * ε_term) k x
      = IterCreditV (G2IterContAmp F ((kf : ℝ≥0∞) * ε_term) k x) (γBkx k x) (k + 1) := rfl
  iapply (tglWp_wand (Φ := fun w : Val ℝ => iprop(∃ b : Bool,
    ⌜w.1 = .lit (.bool b)⌝ ∗ ↯ (G2IterContAmp F ((kf : ℝ≥0∞) * ε_term) k x b) ∗ ⌜True⌝)))
  isplitl [Hcx]
  · iapply (twp_IterTrial E (BkxVal k x) (γBkx k x) (iprop(⌜True⌝))
      (abstractBernoulliI_Bkx k x Hxr (iprop(⌜True⌝)))
      (G2IterContAmp F ((kf : ℝ≥0∞) * ε_term) k x) (k + 1))
    isplitl [Hcx]
    · rw [← hck]; iexact Hcx
    · ipureintro; trivial
  iintro %vb ⟨%b, %hb, Hcb, %_ht⟩
  rcases vb with ⟨wb, hwlcb⟩
  simp only at hb; subst hb
  cases b with
  | true =>
    -- accept: return `(x, k)`, cost `F k x`.
    have hcb : G2IterContAmp F ((kf : ℝ≥0∞) * ε_term) k x true = F k x := by simp [G2IterContAmp]
    have Hx1 : 0 ≤ x ∧ x < 1 := ⟨Hx01.1.le, Hx01.2⟩
    twp_pures
    twp_value
    imodintro
    iexists k, x
    rw [← hcb]
    isplitr [Hcb]
    · ipureintro; exact Hx1
    · isplitr [Hcb]
      · ipureintro; rfl
      · iexact Hcb
  | false =>
    -- reject: recurse, cost `G2CreditV F + k·ε_term`.
    have hcb : G2IterContAmp F ((kf : ℝ≥0∞) * ε_term) k x false
        = G2CreditV F + (kf : ℝ≥0∞) * ε_term := by simp [G2IterContAmp]
    ihave Hcb' : iprop(↯ (G2CreditV F + (kf : ℝ≥0∞) * ε_term)) $$ [Hcb]
    · rw [← hcb]; iexact Hcb
    ihave ⟨Hexp, Hterm⟩ := ErrorCredit.split (GF := GF) $$ Hcb'
    twp_pure
    twp_bind pl(&G2 #.unit)
    iapply (tglWp_wand (Φ := fun p : Val ℝ => iprop(∃ (k : ℕ) (r : ℝ),
      ⌜0 ≤ r ∧ r < 1⌝ ∗
      ⌜p.1 = .pair (.lit (.real r)) (.lit (.int (Int.ofNat k)))⌝ ∗ ↯ (F k r))))
    isplitl [Hexp Hterm IH]
    · iapply IH $$ Hterm
      iexact Hexp
    iintro %w Hpost
    iapply tglWp_value
    iexact Hpost

end specification

end
end Examples
end TotalEris
end ProbLang
