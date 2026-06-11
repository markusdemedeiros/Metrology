module

public import Metrology.TotalEris.ErisGS
public import Metrology.TotalEris.TotalPrimitiveLaws

@[expose] public section

/-!
# Selective port of Eris error rules

Port of the *subset* of `clutch/theories/eris/error_rules.v` needed by the
target examples. The error-credit ghost-state lemmas (`split`, `combine`,
`weaken`, `contradict`, `zero`, amplification family) are already in
`Metrology/Iris/ErrorCredits.lean` under the `ErrorCredit` namespace.

This file just re-exports the relevant ones under conventional Rocq-style
names (`ec_split`, `ec_combine`, …) so example proofs can stay close to the
Rocq text. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped ENNReal AppGS

namespace ProbLang


variable {rT : Type _} [ProbLang.ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]

namespace TotalEris

variable {hlc : Bool} {GF : BundledGFunctors}

section ECGSOnly

variable [ECGS GF]

/-! ## Error-credit re-exports

These delegate to `Metrology.Iris.ErrorCredits` lemmas in the `ErrorCredit`
namespace. The chosen names mirror Rocq (`ec_split`, …). -/

/-- `↯(ε₁ + ε₂) ⊢ ↯ε₁ ∗ ↯ε₂`. Rocq: `ec_split`. -/
theorem ec_split {ε₁ ε₂ : ENNReal} :
    iprop(↯(ε₁ + ε₂)) ⊢@{IProp GF} iprop(↯ε₁ ∗ ↯ε₂) :=
  ErrorCredit.split

/-- `↯ε₁ ∗ ↯ε₂ ⊢ ↯(ε₁ + ε₂)`. Rocq: `ec_combine`. -/
theorem ec_combine {ε₁ ε₂ : ENNReal} :
    iprop(↯ε₁ ∗ ↯ε₂) ⊢@{IProp GF} iprop(↯(ε₁ + ε₂)) :=
  ErrorCredit.combine

/-- Definitional equality on credits. Rocq: `ec_eq`. -/
theorem ec_eq {ε₁ ε₂ : ENNReal} (h : ε₁ = ε₂) :
    iprop(↯ε₁) ⊢@{IProp GF} iprop(↯ε₂) :=
  ErrorCredit.ext h

/-- `1 ≤ ε → ↯ε ⊢ False`. Rocq: `ec_contradict`. -/
theorem ec_contradict {ε : ENNReal} (h : 1 ≤ ε) :
    iprop(↯ε) ⊢@{IProp GF} iprop(False : IProp GF) :=
  ErrorCredit.contradict h

/-- `ε₂ ≤ ε₁ → ↯ε₁ ⊢ ↯ε₂`. Rocq: `ec_weaken`. -/
theorem ec_weaken {ε₁ ε₂ : ENNReal} (h : ε₂ ≤ ε₁) :
    iprop(↯ε₁) ⊢@{IProp GF} iprop(↯ε₂) :=
  ErrorCredit.weaken h

/-- `⊢ |==> ↯0`. Rocq: `ec_zero`. -/
theorem ec_zero : ⊢@{IProp GF} iprop(|==> ↯0) :=
  ErrorCredit.zero

/-- Error credits are valid: `↯ε ⊢ ⌜ε < 1⌝`. -/
theorem ec_valid {ε : ENNReal} :
    iprop(↯ε) ⊢@{IProp GF} iprop(⌜ε < 1⌝) :=
  ErrorCredit.valid

/-! ## Error induction

These are re-exports from `Metrology/Iris/ErrorCredits.lean`'s
`ErrorCredit.Induction` namespace, named to match Rocq's `eris_rules.v`. -/

/-- Geometric-amplification induction: from a Lean-level rule that says
"given the wand `↯(k*ε) -∗ P` and `↯ε`, you can prove `P`", conclude
`↯ε ⊢ P`. Rocq: `ec_ind_simpl_external` (`error_credits.v:395`). -/
theorem ec_ind_simpl_external {ε : ENNReal} {k : NNReal} {P : IProp GF}
    (hε : 0 < ε) (hk : 1 < k)
    (hamp : iprop((↯((k : ENNReal) * ε) -∗ P) ∗ ↯ε) ⊢@{IProp GF} P) :
    iprop(↯ε) ⊢@{IProp GF} P :=
  ErrorCredit.Induction.external_simple hε hk hamp

/-- Linear-amplification induction: from "given the wand `↯ε' -∗ P` (where
`ε' > ε`) and `↯ε`, you can prove `P`", conclude `↯ε ⊢ P`. Rocq:
`ec_induction` (`eris_rules.v:173`). The Lean version requires `ε' : NNReal`
(finite) and currently expresses the hypothesis at the iris-wand level. -/
theorem ec_induction {ε : ENNReal} {ε' : NNReal} {P : IProp GF}
    (hε : 0 < ε) (hε' : ε < ε') :
    iprop(□ ((↯(ε' : ENNReal) -∗ P) ∗ ↯ε -∗ P)) ⊢@{IProp GF} iprop(↯ε -∗ P) :=
  ErrorCredit.Induction.increasing hε hε'

/-! ## Conjuring positive credits and expectation-preserving sampling

These two lemmas are the remaining prerequisites for the `geometric_total`
tutorial. Both are fully proved (no `sorry`). Downstream proofs in
`Examples/GeometricTotal.lean` go through unconditionally. -/

end ECGSOnly

section ErisGSStubs

variable [ErisGS rT hlc GF]

/-- Pre-specialized `supply_decrease` against the `ECGS` instance carried
by `ErisGS`. Same `∗`-bundling trick as `errInterp_supply_bound`. -/
theorem errInterp_supply_decrease {εₛ ε : ENNReal} :
    iprop(ErisWpGS.errInterp (rT := rT) εₛ ∗ ↯ε)
      ⊢@{IProp GF} iprop(|==> ErisWpGS.errInterp (rT := rT) (εₛ - ε)) := by
  show iprop(ecAuth εₛ ∗ ↯ε) ⊢ iprop(|==> ecAuth (εₛ - ε))
  iintro ⟨Hs, Hε⟩
  iapply (ErrorCredit.supply_decrease (GF := GF)) $$ Hs Hε

/-- Pre-specialized `supply_bound` against the `ECGS` instance carried
by `ErisGS`. Bundles both arguments into a `∗` to dodge the wand-source
typeclass diamond. Returns both inputs together with the bound so the
caller doesn't lose `↯ε` / `errInterp εₛ` from the iris context. -/
theorem errInterp_supply_bound {εₛ ε : ENNReal} :
    iprop(ErisWpGS.errInterp (rT := rT) εₛ ∗ ↯ε)
      ⊢@{IProp GF} iprop(ErisWpGS.errInterp (rT := rT) εₛ ∗ ↯ε ∗ ⌜ε ≤ εₛ⌝) := by
  show iprop(ecAuth εₛ ∗ ↯ε) ⊢ iprop(ecAuth εₛ ∗ ↯ε ∗ ⌜ε ≤ εₛ⌝)
  iintro ⟨Hs, Hε⟩
  ihave %hLe := ErrorCredit.supply_bound (GF := GF) $$ Hs Hε
  isplitl [Hs]; · iexact Hs
  isplitl [Hε]; · iexact Hε
  ipure_intro; exact hLe

/-- Pre-specialized `supply_increase` against the `ECGS` instance carried
by `ErisGS` (i.e., `ErisGS.ecGS`). The outer-scope `[ECGS GF]` was lifted
into its own `ECGSOnly` section so that this section only sees the
`ErisGS`-derived ECGS, dodging the typeclass diamond. -/
theorem errInterp_supply_increase {ε δ : ENNReal} (h : ε + δ < 1) :
    iprop(ErisWpGS.errInterp (rT := rT) ε)
      ⊢@{IProp GF} iprop(|==> (ErisWpGS.errInterp (rT := rT) (ε + δ) ∗ ↯δ)) := by
  simp only [erisWpGS_errInterp_eq]
  exact ErrorCredit.supply_increase h

/-- "Error increase" rule: given `↯ε`, we may freely "borrow" up to any
`ε' > ε`. Rocq: `twp_err_incr` (`error_rules.v:881`). -/
theorem twp_err_incr {E : CoPset} {e : Exp rT} {ε : ENNReal} {Φ : Val rT → IProp GF}
    (Hnv : e.toVal? = none) :
    iprop(↯ε ∗ ∀ (ε' : ENNReal), ⌜ε < ε'⌝ -∗ ↯ε' -∗ tglWp E e Φ)
      ⊢@{IProp GF} tglWp E e Φ := by
  iintro ⟨Herr, Hwp⟩
  iapply (twp_lift_step_fupd_glm Hnv)
  iintro %σ₁ %ε₂ ⟨Hσ₁, Hε₂⟩
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset) with Hclose
  imodintro
  iapply glm_credit_bump
  iintro %ε' %Hε'
  -- Case split on `ε' < 1`: if not, the conclusion follows trivially via
  -- `execStutter_spend`. Otherwise we do the supply-increase + credit
  -- combination work.
  by_cases hlt : ε' < 1
  case neg =>
    push Not at hlt
    imodintro
    iapply execStutter_spend hlt
  case pos =>
    -- ε' < 1, so we can increase the supply by `δ := ε' - ε₂`.
    have hle : ε₂ ≤ ε' := Hε'.le
    have hbnd : ε₂ + (ε' - ε₂) < 1 := by
      rw [add_tsub_cancel_of_le hle]; exact hlt
    -- Apply our typeclass-friendly wrapper.
    imod (errInterp_supply_increase hbnd) $$ Hε₂ with ⟨HsuppNew, Hfrag⟩
    -- Combine `Herr : ↯ε` with the new fragment `Hfrag : ↯(ε' - ε₂)`.
    ihave Herr' : iprop(↯(ε + (ε' - ε₂))) $$ [Herr Hfrag]
    · iapply ErrorCredit.combine (ε₁ := ε) (ε₂ := ε' - ε₂)
      isplitl [Herr]; · iexact Herr
      iexact Hfrag
    -- Establish `ε < ε + (ε' - ε₂)` via `ENNReal.lt_add_right`. Need
    -- `ε ≠ ⊤` (from `ec_valid` on `Herr'`) and `ε' - ε₂ ≠ 0` (from `Hε'`).
    ihave %hValid := ErrorCredit.valid $$ Herr'
    have hsub_ne : (ε' - ε₂) ≠ 0 := by
      rw [Ne, _root_.tsub_eq_zero_iff_le]; exact _root_.not_le.mpr Hε'
    have hε_ne_top : ε ≠ (⊤ : ENNReal) := by
      intro hε_top
      rw [hε_top, _root_.top_add] at hValid
      exact absurd hValid (by simp)
    have hlt_hwp : ε < ε + (ε' - ε₂) := ENNReal.lt_add_right hε_ne_top hsub_ne
    -- Invoke `Hwp` to obtain `tglWp E e Φ` at the bigger credit amount.
    ihave HwpRes := Hwp $$ %(ε + (ε' - ε₂)) %hlt_hwp Herr'
    -- Unfold `tglWp` to `tglWpPre`, then rewrite via `tglWpPre_eq_step Hnv`
    -- to expose the glm-shaped form. (Same trick as `tglWp_bind` in
    -- `TotalWeakestpre.lean:540` — `ihave H : iprop(...) $$ [HwpUnfold] ;
    -- · rw [← heqS] ; iexact HwpUnfold`.)
    ihave HwpUnfold := (BI.equiv_iff.mp tglWp_unfold).1 $$ HwpRes
    have heqS := tglWpPre_eq_step (wp := tglWp) (E := E) (e := e) (Φ := Φ) Hnv
    ihave HwpStep : iprop(∀ (σ : State rT) (ε : ENNReal),
        (stateInterp σ ∗ errInterp (rT := rT) ε) -∗
          |={E, ∅}=> glm e σ ε (fun ρ ε₂ =>
            iprop(|={∅, E}=>
              stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ tglWp E ρ.expr Φ)))
      $$ [HwpUnfold]
    · rw [← heqS]; iexact HwpUnfold
    -- Instantiate at σ₁ / (ε₂ + (ε' - ε₂)) using Hσ₁ and HsuppNew.
    ispecialize HwpStep $$ %σ₁ %(ε₂ + (ε' - ε₂)) [Hσ₁ HsuppNew]
    · isplitl [Hσ₁]; · iexact Hσ₁
      iexact HsuppNew
    -- Transition mask: ∅ → E via Hclose, then E → ∅ via HwpStep.
    imod Hclose with _
    imod HwpStep with HGlm
    -- HGlm : glm e σ₁ (ε₂ + (ε' - ε₂)) cont. Rewrite `ε₂ + (ε' - ε₂) = ε'`
    -- on the iris hyp via a typed-`ihave`, then `execStutter_free`.
    have heqEps : ε₂ + (ε' - ε₂) = ε' := add_tsub_cancel_of_le hle
    ihave HGlm' : iprop(glm e σ₁ ε'
        (fun ρ ε₂ => iprop(|={∅, E}=>
          stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ tglWp E ρ.expr Φ))) $$ [HGlm]
    · conv_rhs => rw [← heqEps]
      iexact HGlm
    imodintro
    iapply execStutter_free
    iexact HGlm'

/-- "Error from thin air": when the expression is not a value, we may
assume ownership of an arbitrary positive amount of error credits. Rocq:
`twp_err_pos` (`error_rules.v:967`). Derived from `twp_err_incr` +
`ec_zero` (start from zero credits, bump to any ε > 0). -/
theorem twp_err_pos {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    (Hnv : e.toVal? = none) :
    iprop(∀ (ε : ENNReal), ⌜0 < ε⌝ -∗ ↯ε -∗ tglWp E e Φ)
      ⊢@{IProp GF} tglWp E e Φ := by
  iintro Hwp
  -- Lift the goal into a `|={E}=>` so that `elimModal_bupd_fupd` can fire
  -- on `ec_zero`'s `|==>`.
  iapply ErisWpGS.fupd_tglWp
  ihave HzBupd : iprop(|==> ↯0) $$ []
  · iapply ec_zero
  imod HzBupd with Herr
  imodintro
  iapply (twp_err_incr Hnv)
  isplitl [Herr]; · iexact Herr
  iintro %ε' %Hε' Hcr
  iapply Hwp; · ipure_intro; exact Hε'
  iexact Hcr

/-- Expectation-preserving uniform sample. From `↯ε₁` and an "error
distribution" function `ε₂ : ℕ → ENNReal` whose average over `[0,z)` is
bounded by `ε₁`, we may sample `n : Int` in `[0, z)` and recover `↯(ε₂ n)`
in the postcondition. Rocq: `twp_rand_exp_nat` (`error_rules.v:165`). -/
theorem twp_rand_exp_nat {E : CoPset} {z : Int} {ε₁ : ENNReal}
    {ε₂ : ℕ → ENNReal} {Φ : Val rT → IProp GF} (Hz : 0 < z)
    (Hbd : ∀ n, ε₂ n ≤ 1)
    (HSum : (∑' n : ℕ, if n < z.toNat then ε₂ n / z.toNat else 0) ≤ ε₁) :
    iprop(↯ε₁) ⊢@{IProp GF}
      iprop((∀ (n : Int), ⌜0 ≤ n ∧ n < z⌝ ∗ ↯(ε₂ n.toNat) -∗
        Φ (⟨.lit (.int n), IsVal.lit⟩ : Val rT)) -∗
      tglWp E (.rand (.lit (.int z)) (.lit .unit)) Φ) := by
  iintro Herr Hcont
  -- The expression `rand z ()` is not a value.
  have Hnv : (Exp.rand (Exp.lit (.int z)) (Exp.lit .unit) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (twp_lift_step_fupd_glm Hnv)
  iintro %σ₁ %ε_now ⟨Hσ, Hε_now⟩
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset) with Hclose
  imodintro
  -- Extract `ε₁ ≤ ε_now` (the supply-bound) as a Lean hypothesis. This is
  -- the key fact for the integral bound + per-outcome carried-supply trick.
  ihave ⟨Hε_now, Herr, %hLe⟩ : iprop(ErisWpGS.errInterp (rT := rT) ε_now ∗ ↯ε₁ ∗ ⌜ε₁ ≤ ε_now⌝)
      $$ [Hε_now Herr]
  · iapply errInterp_supply_bound
    isplitl [Hε_now]; · iexact Hε_now
    iexact Herr
  -- Apply `glm_prim_step` (advanced composition). Witnesses:
  --   R ρ  := "ρ = (val n, σ₁) for some `0 ≤ n < z`"
  --   ε₁'  := 0 (we pay nothing at the coupling level; credit goes via X₂)
  --   X₂ ρ := ε₂(n.toNat) if ρ matches val-n with valid n; else 0
  --   r    := 1 (from `Hbd : ∀ n, ε₂ n ≤ 1`)
  -- Carried-supply slack `ε₃ := ε_now - ε₁`. Lemma's `↯ε₁` accounts for
  -- `ε₁`; the remaining `ε₃` rides along with each outcome's X₂.
  iapply glm_prim_step
  iexists (fun ρ => ∃ (n : Int), 0 ≤ n ∧ n < z ∧
    ρ = (⟨.lit (.int n), σ₁⟩ : Cfg rT))
  iexists 0
  iexists (fun ρ : Cfg rT => (ε_now - ε₁) + match ρ.1 with
    | .lit (.int n) =>
        if h : 0 ≤ n ∧ n < z then ε₂ n.toNat else 0
    | _ => 0)
  iexists ((ε_now - ε₁) + 1)
  -- Sub-goal 1: Discrete.Reducible. Use `primStep_pos_of_headStep` + `RandNoTapeS`.
  isplitr
  · ipure_intro
    refine ⟨⟨.lit (.int 0), σ₁⟩, primStep_pos_of_headStep ?_⟩
    rw [Discrete.headStep_support_iff]
    exact .RandNoTapeS Hz (_root_.le_refl _) Hz
  -- Sub-goal 2: X₂ ρ ≤ ε₃ + 1. The carried `ε₃ = ε_now - ε₁` is constant
  -- across ρ; only the right summand varies. Case-split as before.
  isplitr
  · ipure_intro
    intro ρ
    simp only
    gcongr
    split
    · split <;> first | exact Hbd _ | exact zero_le _
    · exact zero_le _
  -- Sub-goal 3: integral bound `0 + ∫ X₂ dμ ≤ ε_now`.
  -- Strategy: linearity splits `∫ (ε₃ + g) = ε₃ * μ(univ) + ∫ g`. For
  -- primStep of `rand z ()`, `μ(univ) = 1`. The remaining `∫ g dμ` equals
  -- `(1/(z+1)) * ∑_{n<z+1} ε₂ n` (≤ ε₁ by HSum). Then `ε₃ + ε₁ = ε_now`
  -- via `hLe : ε₁ ≤ ε_now` (`tsub_add_cancel_of_le`).
  isplitr
  · ipure_intro
    rw [zero_add, MeasureTheory.lintegral_add_left measurable_const,
        MeasureTheory.lintegral_const]
    -- `(ε_now - ε₁) * μ(univ) ≤ ε_now - ε₁` since `μ(univ) ≤ 1`.
    have hμ_le_one : (primStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁⟩) Set.univ ≤ 1 := primStep_univ_le_one _
    calc (ε_now - ε₁) * (primStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁⟩) Set.univ +
            ∫⁻ (a : Cfg rT), (match a.expr with
                | .lit (.int n) => if h : 0 ≤ n ∧ n < z then ε₂ n.toNat else 0
                | _ => 0)
              ∂primStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁⟩
        ≤ (ε_now - ε₁) * 1 + ε₁ := by
          gcongr
          · -- Bound `∫ g dμ ≤ ε₁` from `HSum` by computing
            -- `primStep ⟨rand z (), σ₁⟩` as `Cfg.uniform z σ₁`, pushing
            -- the integral through `Measure.map`, restricting to the
            -- `Finset.Ico 0 z` support, and reindexing `n : Int` ↦
            -- `n.toNat : ℕ` to match HSum's form.
            -- Reduce primStep to headStep (= Cfg.uniform on rand z ()).
            have hheadred : ∃ ρ : Cfg rT,
                0 < (headStep ⟨.rand (.lit (.int z)) (.lit .unit), σ₁⟩) {ρ} :=
              ⟨⟨.lit (.int 0), σ₁⟩, by
                rw [Discrete.headStep_support_iff]
                exact .RandNoTapeS Hz (_root_.le_refl _) Hz⟩
            rw [primStep_eq_headStep hheadred]
            -- headStep ⟨rand z (), σ⟩ definitionally equals Cfg.uniform z σ.
            show ∫⁻ a, (match a.expr with
                | .lit (.int n) => if h : 0 ≤ n ∧ n < z then ε₂ n.toNat else 0
                | _ => 0) ∂(Cfg.uniform z σ₁) ≤ ε₁
            -- Unfold Cfg.uniform using 0 < z.
            have hCfgUniform :
                Cfg.uniform z σ₁ =
                  (PMF.uniformOfFinset (Finset.Ico (0:Int) z)
                      (Finset.nonempty_Ico.mpr Hz)).toMeasure.map
                    (fun n : Int => (⟨.lit (.int n), σ₁⟩ : Cfg rT)) := by
              unfold Cfg.uniform
              simp only [Int.isPos, dif_pos Hz]
            rw [hCfgUniform]
            -- Push the integral through `Measure.map`.
            rw [MeasureTheory.lintegral_map .of_discrete .of_discrete]
            -- Goal: ∫⁻ (n : Int), (if h : 0 ≤ n ∧ n < z then ε₂ n.toNat else 0)
            --        ∂(uniformOfFinset (Ico 0 z) _).toMeasure ≤ ε₁
            -- Use `lintegral_finset` after reducing to the support set.
            have hCard : (Finset.Ico (0:Int) z).card = z.toNat := by
              rw [Int.card_Ico, sub_zero]
            -- Compute the lintegral as a finite sum.
            have hLI :
                ∫⁻ (n : Int), (if h : 0 ≤ n ∧ n < z then ε₂ n.toNat else 0)
                  ∂((PMF.uniformOfFinset (Finset.Ico (0:Int) z)
                      (Finset.nonempty_Ico.mpr Hz)).toMeasure)
                = ∑ n ∈ Finset.Ico (0:Int) z, ε₂ n.toNat / (z.toNat : ℝ≥0∞) := by
              -- First, restrict to the Finset support since integrand vanishes off it.
              have hIndic : (fun n : Int => (if h : 0 ≤ n ∧ n < z then ε₂ n.toNat else 0))
                  = ((Finset.Ico (0:Int) z) : Set Int).indicator
                    (fun n : Int => (if h : 0 ≤ n ∧ n < z then ε₂ n.toNat else 0)) := by
                funext n
                by_cases hn : n ∈ Finset.Ico (0:Int) z
                · rw [Set.indicator_of_mem]; exact hn
                · rw [Set.indicator_of_notMem (by exact hn)]
                  simp only [Finset.mem_Ico, not_and, _root_.not_lt] at hn
                  by_cases h0 : 0 ≤ n
                  · have hnz : ¬ n < z := _root_.not_lt.mpr (hn h0)
                    rw [dif_neg]; exact fun ⟨_, h⟩ => hnz h
                  · rw [dif_neg]; exact fun ⟨h, _⟩ => h0 h
              rw [hIndic, MeasureTheory.lintegral_indicator
                  ((Finset.Ico (0:Int) z).measurableSet)]
              rw [MeasureTheory.lintegral_finset]
              refine Finset.sum_congr rfl fun n hn => ?_
              rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton n),
                  PMF.uniformOfFinset_apply, if_pos hn, hCard]
              simp only [Finset.mem_Ico] at hn
              rw [dif_pos ⟨hn.1, hn.2⟩, ENNReal.div_eq_inv_mul, mul_comm]
            rw [hLI]
            -- Reindex Finset.Ico 0 z (over ℤ) as Finset.range z.toNat (over ℕ).
            have hReindex : ∑ n ∈ Finset.Ico (0:Int) z, ε₂ n.toNat / (z.toNat : ℝ≥0∞)
                = ∑ k ∈ Finset.range z.toNat, ε₂ k / (z.toNat : ℝ≥0∞) := by
              refine Finset.sum_nbij' (i := fun n : Int => n.toNat)
                (j := fun k : Nat => (k : Int)) ?_ ?_ ?_ ?_ ?_
              · intro n hn
                simp only [Finset.mem_Ico] at hn
                simp only [Finset.mem_range]
                have hnz : n < (z.toNat : Int) := by
                  rw [Int.toNat_of_nonneg (_root_.le_of_lt Hz)]; exact hn.2
                exact_mod_cast (Int.toNat_lt hn.1).mpr hnz
              · intro k hk
                simp only [Finset.mem_range] at hk
                simp only [Finset.mem_Ico]
                refine ⟨Int.natCast_nonneg _, ?_⟩
                have : (k : Int) < (z.toNat : Int) := by exact_mod_cast hk
                rwa [Int.toNat_of_nonneg (_root_.le_of_lt Hz)] at this
              · intro n hn
                simp only [Finset.mem_Ico] at hn
                exact Int.toNat_of_nonneg hn.1
              · intro k _
                exact Int.toNat_natCast k
              · intro n _
                rfl
            rw [hReindex]
            -- Compare with HSum.
            have hSumExt : ∑ k ∈ Finset.range z.toNat, ε₂ k / (z.toNat : ℝ≥0∞)
                = ∑' n : ℕ, if n < z.toNat then ε₂ n / (z.toNat : ℝ≥0∞) else 0 := by
              rw [tsum_eq_sum (s := Finset.range z.toNat) (f := fun n =>
                  if n < z.toNat then ε₂ n / (z.toNat : ℝ≥0∞) else 0) ?_]
              · refine Finset.sum_congr rfl fun k hk => ?_
                rw [if_pos (Finset.mem_range.mp hk)]
              · intro n hn
                simp only [Finset.mem_range, _root_.not_lt] at hn
                show (if n < z.toNat then ε₂ n / (z.toNat : ℝ≥0∞) else 0) = 0
                rw [if_neg (_root_.not_lt.mpr hn)]
            rw [hSumExt]
            exact HSum
      _ = ε_now := by
          rw [mul_one]; exact tsub_add_cancel_of_le hLe
  -- Sub-goal 4: Pgl 0 R. Use `Pgl.mono_pred` from `Pgl.zero_positive`:
  -- every config in the positive-mass support of `primStep ⟨rand z (), σ₁⟩`
  -- must be of the form `⟨lit n, σ₁⟩` with `0 ≤ n < z` (i.e., `R`).
  isplitr
  · ipure_intro
    have hheadred : ∃ ρ : Cfg rT, 0 < (headStep ⟨_, σ₁⟩) {ρ} :=
      ⟨⟨.lit (.int 0), σ₁⟩, by
        rw [Discrete.headStep_support_iff]; exact .RandNoTapeS Hz (_root_.le_refl _) Hz⟩
    have hps_eq : primStep ⟨Exp.rand (Exp.lit (.int z)) (Exp.lit .unit), σ₁⟩
        = headStep ⟨Exp.rand (Exp.lit (.int z)) (Exp.lit .unit), σ₁⟩ :=
      primStep_eq_headStep hheadred
    refine Pgl.mono_pred ?_ (Pgl.zero_positive _)
    intro ρ hpos
    rw [hps_eq, Discrete.headStep_support_iff] at hpos
    obtain ⟨e', σ'⟩ := ρ
    cases hpos with
    | RandNoTapeS Hz' Hv0 Hvz => exact ⟨_, Hv0, Hvz, rfl⟩
    | RandNonposS hnz => exact absurd Hz hnz
  -- Sub-goal 5: per-outcome continuation.
  iintro %ρ %HRρ
  obtain ⟨n, Hn₁, Hn₂, Hρ_eq⟩ := HRρ
  -- After substituting `ρ = ⟨.lit (.int n), σ₁⟩`, the `X₂ ρ` reduces to
  -- `ε_now - ε₁ + ε₂ n.toNat` (the match arm fires; `dif_pos` discharges
  -- the `0 ≤ n ∧ n < z` side condition).
  subst Hρ_eq
  simp only [dif_pos (And.intro Hn₁ Hn₂)]
  -- Decrease supply: consume `↯ε₁` to drop supply from `ε_now` to
  -- `ε_now - ε₁`. Mirrors Rocq's `ec_supply_decrease`. The outer
  -- `|={∅}=>` absorbs the `|==>`.
  ihave Hsupp1 : iprop(|==> ErisWpGS.errInterp (rT := rT) (ε_now - ε₁)) $$ [Hε_now Herr]
  · iapply errInterp_supply_decrease
    isplitl [Hε_now]; · iexact Hε_now
    iexact Herr
  imod Hsupp1 with Hε_minus
  imodintro
  -- Case-split on whether the new supply `(ε_now - ε₁) + ε₂ n.toNat`
  -- still validates as a credit supply (< 1). If not, take the
  -- `execStutter_spend` branch; otherwise take `execStutter_free` and
  -- do the supply-increase to produce `↯(ε₂ n.toNat)`.
  by_cases hlt : (ε_now - ε₁) + ε₂ n.toNat < 1
  case neg =>
    push Not at hlt
    iapply execStutter_spend hlt
  case pos =>
    iapply execStutter_free
    imod (errInterp_supply_increase hlt) $$ Hε_minus with ⟨Hε_new, Hcr⟩
    imod Hclose with _
    -- Feed `Hcr` + bounds into `Hcont` to obtain `Φ ⟨lit n, IsVal.lit⟩`.
    ihave HΦ : iprop(Φ ⟨.lit (.int n), IsVal.lit⟩) $$ [Hcont Hcr]
    · iapply Hcont $$ %n
      isplitr
      · ipure_intro; exact ⟨Hn₁, Hn₂⟩
      iexact Hcr
    imodintro
    isplitl [Hσ]; · iexact Hσ
    isplitl [Hε_new]; · iexact Hε_new
    iapply (ErisWpGS.tglWp_value_of_toVal (v := ⟨.lit (.int n), IsVal.lit⟩) rfl)
    iexact HΦ

/-- Tutorial wrapper around `twp_rand_exp_nat` matching the form used in
`eris_rules.v:118` — phrases the sum as `∑ k < N+1, ε₂ k ≤ (N+1) * ε₁`.
Unlike the underlying `twp_rand_exp_nat`, this wrapper does NOT require
`ε₂ n ≤ 1`; values above 1 are clamped internally (see `eris_rules.v`). -/
theorem twp_rand_exp {E : CoPset} {z : Int} {ε₁ : ENNReal}
    {ε₂ : ℕ → ENNReal} {Φ : Val rT → IProp GF} (Hz : 0 < z)
    (HSum : (∑ n ∈ Finset.range z.toNat, ε₂ n) ≤ z.toNat * ε₁) :
    iprop(↯ε₁) ⊢@{IProp GF}
      iprop((∀ (n : Int), ⌜0 ≤ n ∧ n < z⌝ ∗ ↯(ε₂ n.toNat) -∗
        Φ (⟨.lit (.int n), IsVal.lit⟩ : Val rT)) -∗
      tglWp E (.rand (.lit (.int z)) (.lit .unit)) Φ) := by
  -- Apply `twp_rand_exp_nat` with the clamped `F n := min (ε₂ n) 1`.
  iintro Herr Hcont
  iapply (twp_rand_exp_nat (ε₂ := fun n => min (ε₂ n) 1) Hz
    (fun n => min_le_right _ _) ?_) $$ Herr
  · -- HSum side condition: chain of inequalities ending with the wrapper's HSum.
    have hz_ne : (z.toNat : ENNReal) ≠ 0 := by
      exact_mod_cast Int.toNat_eq_zero.not.mpr (_root_.not_le.mpr Hz)
    calc (∑' n : ℕ, if n < z.toNat then min (ε₂ n) 1 / z.toNat else 0)
        ≤ (∑' n : ℕ, if n < z.toNat then ε₂ n / z.toNat else 0) := by
          apply ENNReal.tsum_le_tsum
          intro n
          by_cases h : n < z.toNat <;> simp [h]
          exact ENNReal.div_le_div_right (_root_.min_le_left _ _) _
      _ = (∑ n ∈ Finset.range z.toNat, ε₂ n / z.toNat) := by
          refine (tsum_eq_sum (s := Finset.range z.toNat) ?_).trans ?_
          · intro n hn
            rw [Finset.mem_range] at hn
            simp [hn]
          · apply Finset.sum_congr rfl
            intro n hn
            rw [Finset.mem_range] at hn
            simp [hn]
      _ = (∑ n ∈ Finset.range z.toNat, ε₂ n) / z.toNat := by
          -- Pull the constant divisor out. ENNReal isn't a DivisionSemiring,
          -- but `ENNReal.add_div` gives us the inductive step.
          induction Finset.range z.toNat using Finset.induction with
          | empty => simp
          | @insert i s hi ih =>
            rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, ENNReal.add_div]
      _ ≤ (z.toNat * ε₁) / z.toNat := by
          -- monotonicity of division by `HSum`.
          exact ENNReal.div_le_div_right HSum _
      _ = ε₁ := by
          rw [mul_comm]
          exact ENNReal.mul_div_cancel_right hz_ne (ENNReal.natCast_ne_top z.toNat)
  -- Continuation: case-split on `ε₂ n ≤ 1`.
  iintro %n ⟨%Hn, Hcr⟩
  by_cases h : ε₂ n.toNat ≤ 1
  · -- `min (ε₂ n) 1 = ε₂ n`. Convert Hcr's type via `ec_eq` and feed Hcont.
    iapply Hcont $$ %n
    isplitr
    · ipure_intro; exact Hn
    iapply (ec_eq (show min (ε₂ n.toNat) 1 = ε₂ n.toNat from _root_.min_eq_left h))
    iexact Hcr
  · -- `1 < ε₂ n`, so `min = 1` and `↯1` is contradictory.
    push Not at h
    iexfalso
    iapply (ec_contradict (show (1 : ENNReal) ≤ 1 from _root_.le_refl _))
    iapply (ec_eq (show min (ε₂ n.toNat) 1 = 1 from _root_.min_eq_right h.le))
    iexact Hcr

end ErisGSStubs

end TotalEris
end ProbLang
