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


variable {rT : Type _} [ProbLang.ProbLangℝ rT]

/-- Measurability of an integer-literal reader
`fun e => match e with | .lit (.int n) => g n | _ => 0` on `Exp rT`, for any
`g : Int → ENNReal`. Countability-free: built from the `Exp`/`BaseLit` structural
recursion measurability keystones (`measurable_struct_rec` / `BaseLit.measurable_rec`).
Shared by the advanced-composition rules' integral side conditions
(`twp_rand_adv_comp`, `twp_presample_adv_comp`). -/
theorem measurable_litInt_elim (g : Int → ENNReal) :
    Measurable (fun e : Exp rT => match e with
      | .lit (.int n) => g n
      | _ => (0 : ENNReal)) := by
  -- The `.lit` branch's combinator, proved measurable via `BaseLit.measurable_rec`
  -- after bridging the `match` to its `casesOn` normal form.
  have hlit : Measurable (fun b : BaseLit rT =>
      match b with | .int n => g n | _ => (0 : ENNReal)) := by
    have heq : (fun b : BaseLit rT => match b with | .int n => g n | _ => (0 : ENNReal))
        = (fun b : BaseLit rT => BaseLit.casesOn (motive := fun _ => ENNReal) b
            g (fun _ => 0) 0 (fun _ => 0) (fun _ => 0) (fun _ => 0)) := by
      funext b; cases b <;> rfl
    rw [heq]
    exact BaseLit.measurable_rec g (fun _ => 0) (fun _ => 0) (fun _ => 0)
      (fun _ => 0) (fun _ => 0) measurable_const
  apply Exp.measurable_struct_rec
    (f := fun e : Exp rT => match e with | .lit (.int n) => g n | _ => (0 : ENNReal))
    (c_bvar := fun _ => 0) (c_fvar := fun _ => 0)
    (c_lit := fun b => match b with | .int n => g n | _ => (0 : ENNReal))
    (c_lam := fun _ => 0) (c_fix := fun _ => 0)
    (c_app := fun _ _ => 0) (c_unop := fun _ _ => 0) (c_binop := fun _ _ _ => 0)
    (c_cond := fun _ _ _ => 0) (c_pair := fun _ _ => 0)
    (c_fst := fun _ => 0) (c_snd := fun _ => 0)
    (c_inl := fun _ => 0) (c_inr := fun _ => 0) (c_case := fun _ _ _ => 0)
    (c_alloc := fun _ => 0) (c_load := fun _ => 0) (c_store := fun _ _ => 0)
    (c_tape := fun _ => 0) (c_rand := fun _ _ => 0) (c_fail := (0 : ENNReal))
    (c_scrut := fun _ _ => 0)
  all_goals first
    | (intros; rfl)
    | rfl
    | exact hlit
    | (intro b; cases b <;> rfl)
    | fun_prop

/-- Continuous analogue of `measurable_litInt_elim`: the real-literal eliminator
is measurable when its payload map `g : rT → ENNReal` is. Used to push the
error-credit integrand through the `urand` pushforward `unifUnit.map (⟨.lit (.real ·), σ⟩)`. -/
theorem measurable_litReal_elim (g : rT → ENNReal) (hg : Measurable g) :
    Measurable (fun e : Exp rT => match e with
      | .lit (.real r) => g r
      | _ => (0 : ENNReal)) := by
  have hlit : Measurable (fun b : BaseLit rT =>
      match b with | .real r => g r | _ => (0 : ENNReal)) := by
    have heq : (fun b : BaseLit rT => match b with | .real r => g r | _ => (0 : ENNReal))
        = (fun b : BaseLit rT => BaseLit.casesOn (motive := fun _ => ENNReal) b
            (fun _ => 0) (fun _ => 0) 0 (fun _ => 0) (fun _ => 0) g) := by
      funext b; cases b <;> rfl
    rw [heq]
    exact BaseLit.measurable_rec (fun _ => 0) (fun _ => 0) (fun _ => 0)
      (fun _ => 0) (fun _ => 0) g hg
  apply Exp.measurable_struct_rec
    (f := fun e : Exp rT => match e with | .lit (.real r) => g r | _ => (0 : ENNReal))
    (c_bvar := fun _ => 0) (c_fvar := fun _ => 0)
    (c_lit := fun b => match b with | .real r => g r | _ => (0 : ENNReal))
    (c_lam := fun _ => 0) (c_fix := fun _ => 0)
    (c_app := fun _ _ => 0) (c_unop := fun _ _ => 0) (c_binop := fun _ _ _ => 0)
    (c_cond := fun _ _ _ => 0) (c_pair := fun _ _ => 0)
    (c_fst := fun _ => 0) (c_snd := fun _ => 0)
    (c_inl := fun _ => 0) (c_inr := fun _ => 0) (c_case := fun _ _ _ => 0)
    (c_alloc := fun _ => 0) (c_load := fun _ => 0) (c_store := fun _ _ => 0)
    (c_tape := fun _ => 0) (c_rand := fun _ _ => 0) (c_fail := (0 : ENNReal))
    (c_scrut := fun _ _ => 0)
  all_goals first
    | (intros; rfl)
    | rfl
    | exact hlit
    | (intro b; cases b <;> rfl)
    | fun_prop

namespace TotalEris

variable {hlc : HasLC} {GF : BundledGFunctors}

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

theorem errInterp_supply_decrease {εₛ ε : ENNReal} :
    iprop(ErisWpGS.errInterp (rT := rT) εₛ ∗ ↯ε)
      ⊢@{IProp GF} iprop(|==> ErisWpGS.errInterp (rT := rT) (εₛ - ε)) := by
  show iprop(ecAuth εₛ ∗ ↯ε) ⊢ iprop(|==> ecAuth (εₛ - ε))
  iintro ⟨Hs, Hε⟩
  iapply (ErrorCredit.supply_decrease (GF := GF)) $$ Hs Hε

theorem errInterp_supply_bound {εₛ ε : ENNReal} :
    iprop(ErisWpGS.errInterp (rT := rT) εₛ ∗ ↯ε)
      ⊢@{IProp GF} iprop(ErisWpGS.errInterp (rT := rT) εₛ ∗ ↯ε ∗ ⌜ε ≤ εₛ⌝) := by
  show iprop(ecAuth εₛ ∗ ↯ε) ⊢ iprop(ecAuth εₛ ∗ ↯ε ∗ ⌜ε ≤ εₛ⌝)
  iintro ⟨Hs, Hε⟩
  ihave %hLe := ErrorCredit.supply_bound (GF := GF) $$ Hs Hε
  isplitl [Hs]; · iexact Hs
  isplitl [Hε]; · iexact Hε
  ipureintro; exact hLe

theorem errInterp_supply_increase {ε δ : ENNReal} (h : ε + δ < 1) :
    iprop(ErisWpGS.errInterp (rT := rT) ε)
      ⊢@{IProp GF} iprop(|==> (ErisWpGS.errInterp (rT := rT) (ε + δ) ∗ ↯δ)) := by
  simp only [erisWpGS_errInterp_eq]
  exact ErrorCredit.supply_increase h

theorem twp_err_incr {E : CoPset} {e : Exp rT} {ε : ENNReal} {Φ : Val rT → IProp GF}
    (Hnv : e.toVal? = none) :
    iprop(↯ε ∗ ∀ (ε' : ENNReal), ⌜ε < ε'⌝ -∗ ↯ε' -∗ tglWp E e Φ)
      ⊢@{IProp GF} tglWp E e Φ := by
  iintro ⟨Herr, Hwp⟩
  iapply (twp_lift_step_fupd_glm Hnv)
  iintro %σ₁ %ε₂ ⟨Hσ₁, Hε₂⟩
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset) with Hclose
  imodintro
  iapply glm'_credit_bump
  iintro %ε' %Hε'
  by_cases hlt : ε' < 1
  case neg =>
    push Not at hlt
    imodintro
    iapply execStutter_spend hlt
  case pos =>
    have hle : ε₂ ≤ ε' := Hε'.le
    have hbnd : ε₂ + (ε' - ε₂) < 1 := by
      rw [add_tsub_cancel_of_le hle]; exact hlt
    imod (errInterp_supply_increase hbnd) $$ Hε₂ with ⟨HsuppNew, Hfrag⟩
    ihave Herr' : iprop(↯(ε + (ε' - ε₂))) $$ [Herr Hfrag]
    · iapply ErrorCredit.combine (ε₁ := ε) (ε₂ := ε' - ε₂)
      isplitl [Herr]; · iexact Herr
      iexact Hfrag
    ihave %hValid := ErrorCredit.valid $$ Herr'
    have hsub_ne : (ε' - ε₂) ≠ 0 := by
      rw [Ne, _root_.tsub_eq_zero_iff_le]; exact _root_.not_le.mpr Hε'
    have hε_ne_top : ε ≠ (⊤ : ENNReal) := by
      intro hε_top
      rw [hε_top, _root_.top_add] at hValid
      exact absurd hValid (by simp)
    have hlt_hwp : ε < ε + (ε' - ε₂) := ENNReal.lt_add_right hε_ne_top hsub_ne
    ihave HwpRes := Hwp $$ %(ε + (ε' - ε₂)) %hlt_hwp Herr'
    ihave HwpUnfold := (BI.equiv_iff.mp tglWp_unfold).1 $$ HwpRes
    have heqS := tglWpPre_eq_step (wp := tglWp) (E := E) (e := e) (Φ := Φ) Hnv
    ihave HwpStep : iprop(∀ (σ : State rT) (ε : ENNReal),
        (stateInterp σ ∗ errInterp (rT := rT) ε) -∗
          |={E, ∅}=> glm' e σ ε (fun ρ ε₂ =>
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
    have heqEps : ε₂ + (ε' - ε₂) = ε' := add_tsub_cancel_of_le hle
    ihave HGlm' : iprop(glm' e σ₁ ε'
        (fun ρ ε₂ => iprop(|={∅, E}=>
          stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ tglWp E ρ.expr Φ))) $$ [HGlm]
    · conv_rhs => rw [← heqEps]
      iexact HGlm
    imodintro
    iapply execStutter_free
    iexact HGlm'

theorem twp_err_pos {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    (Hnv : e.toVal? = none) :
    iprop(∀ (ε : ENNReal), ⌜0 < ε⌝ -∗ ↯ε -∗ tglWp E e Φ)
      ⊢@{IProp GF} tglWp E e Φ := by
  iintro Hwp
  iapply ErisWpGS.fupd_tglWp
  ihave HzBupd : iprop(|==> ↯0) $$ []
  · iapply ec_zero
  imod HzBupd with Herr
  imodintro
  iapply (twp_err_incr Hnv)
  isplitl [Herr]; · iexact Herr
  iintro %ε' %Hε' Hcr
  iapply Hwp; · ipureintro; exact Hε'
  iexact Hcr

theorem twp_rand_exp_nat {E : CoPset} {z : Int} {ε₁ : ENNReal}
    {ε₂ : ℕ → ENNReal} {Φ : Val rT → IProp GF} (Hz : 0 < z)
    (Hbd : ∀ n, ε₂ n ≤ 1)
    (HSum : (∑' n : ℕ, if n < z.toNat then ε₂ n / z.toNat else 0) ≤ ε₁) :
    iprop(↯ε₁) ⊢@{IProp GF}
      iprop((∀ (n : Int), ⌜0 ≤ n ∧ n < z⌝ ∗ ↯(ε₂ n.toNat) -∗
        Φ (⟨.lit (.int n), IsVal.lit⟩ : Val rT)) -∗
      tglWp E (.rand (.lit (.int z)) (.lit .unit)) Φ) := by
  iintro Herr Hcont
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
  iapply glm'_prim_step
  iexists (fun ρ => ∃ (n : Int), 0 ≤ n ∧ n < z ∧
    ρ = (⟨.lit (.int n), σ₁⟩ : Cfg rT))
  iexists 0
  iexists (fun ρ : Cfg rT => (ε_now - ε₁) + match ρ.1 with
    | .lit (.int n) =>
        if h : 0 ≤ n ∧ n < z then ε₂ n.toNat else 0
    | _ => 0)
  iexists ((ε_now - ε₁) + 1)
  -- Sub-goal 1: Reducible, via the measurability-free `HeadStepSupport.possible`.
  isplitr
  · ipureintro
    exact Reducible.of_head (HeadStepSupport.RandNoTapeS Hz (_root_.le_refl _) Hz).possible.ne_zero
  -- Sub-goal 1b: the support predicate is an explicit countable set of int-configs.
  isplitr
  · ipureintro
    have hctble : {ρ : Cfg rT | ∃ n : Int, 0 ≤ n ∧ n < z ∧ ρ = (⟨.lit (.int n), σ₁⟩ : Cfg rT)}.Countable := by
      apply Set.Countable.mono (s₂ := (fun n : Int => (⟨.lit (.int n), σ₁⟩ : Cfg rT)) '' Set.univ)
      · rintro ρ ⟨n, _, _, rfl⟩; exact ⟨n, trivial, rfl⟩
      · exact (Set.countable_univ).image _
    exact hctble.measurableSet
  isplitr
  · ipureintro
    intro ρ
    simp only
    gcongr
    split
    · split <;> first | exact Hbd _ | exact zero_le
    · exact zero_le
  isplitr
  · ipureintro
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
            have hhead : HeadReducible (.rand (.lit (.int z)) (.lit .unit)) σ₁ :=
              (HeadStepSupport.RandNoTapeS Hz (_root_.le_refl _) Hz).possible.ne_zero
            rw [primStep_eq_headStep hhead]
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
            rw [MeasureTheory.lintegral_map ?G1 ?G2]
            -- G1/G2: `Measurable` of the concrete integrand / the `Int → Cfg` map.
            -- G1: the expr-match integrand, via the countability-free
            -- `measurable_litInt_elim` composed with `Cfg.measurable_expr`.
            case G1 => exact (measurable_litInt_elim _).comp Cfg.measurable_expr
            case G2 => exact Measurable.of_discrete
            have hCard : (Finset.Ico (0:Int) z).card = z.toNat := by
              rw [Int.card_Ico, sub_zero]
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
  · ipureintro
    -- `Pgl 0 R μ` means `μ {¬R} = 0`. Compute `μ = Cfg.uniform z σ₁` as the pushforward
    -- of `PMF.uniformOfFinset (Ico 0 z)` under `n ↦ ⟨lit n, σ₁⟩`; its support is exactly
    -- the `R`-states, so the complement has measure 0. Countability-free: the support
    -- is a finite Finset, and `{¬R}` is measurable as the complement of a countable set.
    show (primStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁⟩)
        {ρ : Cfg rT | ¬ ∃ (n : Int), 0 ≤ n ∧ n < z ∧ ρ = (⟨.lit (.int n), σ₁⟩ : Cfg rT)} ≤ 0
    refine _root_.le_of_eq ?_
    have hhead : HeadReducible (.rand (.lit (.int z)) (.lit .unit)) σ₁ :=
      (HeadStepSupport.RandNoTapeS Hz (_root_.le_refl _) Hz).possible.ne_zero
    rw [primStep_eq_headStep hhead]
    show (Cfg.uniform z σ₁)
        {ρ : Cfg rT | ¬ ∃ (n : Int), 0 ≤ n ∧ n < z ∧ ρ = (⟨.lit (.int n), σ₁⟩ : Cfg rT)} = 0
    have hCfgUniform :
        Cfg.uniform z σ₁ =
          (PMF.uniformOfFinset (Finset.Ico (0:Int) z)
              (Finset.nonempty_Ico.mpr Hz)).toMeasure.map
            (fun n : Int => (⟨.lit (.int n), σ₁⟩ : Cfg rT)) := by
      unfold Cfg.uniform; simp only [Int.isPos, dif_pos Hz]
    have hg : Measurable (fun n : Int => (⟨.lit (.int n), σ₁⟩ : Cfg rT)) := Measurable.of_discrete
    have hRc : MeasurableSet
        {ρ : Cfg rT | ¬ ∃ (n : Int), 0 ≤ n ∧ n < z ∧ ρ = (⟨.lit (.int n), σ₁⟩ : Cfg rT)} := by
      refine MeasurableSet.compl ?_
      have hctble : {ρ : Cfg rT | ∃ n : Int, 0 ≤ n ∧ n < z ∧
          ρ = (⟨.lit (.int n), σ₁⟩ : Cfg rT)}.Countable := by
        apply Set.Countable.mono
          (s₂ := (fun n : Int => (⟨.lit (.int n), σ₁⟩ : Cfg rT)) '' Set.univ)
        · rintro ρ ⟨n, _, _, rfl⟩; exact ⟨n, trivial, rfl⟩
        · exact (Set.countable_univ).image _
      exact hctble.measurableSet
    rw [hCfgUniform, MeasureTheory.Measure.map_apply hg hRc,
      PMF.toMeasure_apply_eq_zero_iff _ (hg hRc), PMF.support_uniformOfFinset, Set.disjoint_left]
    intro n hn hcontra
    rw [Finset.mem_coe, Finset.mem_Ico] at hn
    exact hcontra ⟨n, hn.1, hn.2, rfl⟩
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
      · ipureintro; exact ⟨Hn₁, Hn₂⟩
      iexact Hcr
    imodintro
    isplitl [Hσ]; · iexact Hσ
    isplitl [Hε_new]; · iexact Hε_new
    iapply (ErisWpGS.tglWp_value_of_toVal (v := ⟨.lit (.int n), IsVal.lit⟩) rfl)
    iexact HΦ

/-- **Continuous error-credit conditioning at a uniform sample.** Given an error
budget `ε₁` and a measurable per-outcome credit map `ε₂ : rT → ℝ≥0∞` whose
**Lebesgue integral over the unit interval** `∫⁻ r, ε₂ r ∂unifUnit` is at most
`ε₁`, the continuous uniform sample `urand` can spend `↯ε₁` to deliver `↯(ε₂ r)`
at each real outcome `r`.

This is the continuous analogue of `twp_rand_exp_nat` (where the discrete `∑`/`z`
average is replaced by `∫⁻ … ∂unifUnit`). It uses NO atomicity: the support
certificate is `Concentrated (primStep …) (real-image)` via `concentratedOn_map`,
and the integral bound goes through `unifUnit.map (⟨.lit (.real ·), σ⟩)` change of
variables (`lintegral_map`). -/
theorem twp_urand_exp {E : CoPset} {ε₁ : ENNReal}
    {ε₂ : rT → ENNReal} {Φ : Val rT → IProp GF}
    (hε₂ : Measurable ε₂) (Hbd : ∀ r, ε₂ r ≤ 1)
    (HInt : (∫⁻ r, ε₂ r ∂(ProbLangℝ.unifUnit (T := rT))) ≤ ε₁) :
    iprop(↯ε₁) ⊢@{IProp GF}
      iprop((∀ (r : rT), ↯(ε₂ r) -∗ Φ (⟨.lit (.real r), IsVal.lit⟩ : Val rT)) -∗
      tglWp E Exp.urand Φ) := by
  iintro Herr Hcont
  have Hnv : (Exp.urand : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  -- The real-literal image map and its measurable-embedding facts.
  have hg : ∀ σ₁ : State rT, Measurable (fun r : rT => (⟨.lit (.real r), σ₁⟩ : Cfg rT)) :=
    fun σ₁ => Cfg.measurable_iff.mpr
      ⟨Exp.lit.measurable.comp BaseLit.real.measurable, measurable_const⟩
  have hgemb : ∀ σ₁ : State rT,
      MeasurableEmbedding (fun r : rT => (⟨.lit (.real r), σ₁⟩ : Cfg rT)) := fun σ₁ => by
    have hcomp : (fun r : rT => (⟨.lit (.real r), σ₁⟩ : Cfg rT))
        = Cfg.measurableEquivProd.symm ∘ (fun e : Exp rT => (e, σ₁))
            ∘ Exp.lit ∘ BaseLit.real := rfl
    rw [hcomp]
    exact Cfg.measurableEquivProd.symm.measurableEmbedding.comp
      ((measurableEmbedding_prod_mk_right σ₁).comp
        (Exp.lit.measurableEmbedding.comp BaseLit.real.measurableEmbedding))
  iapply (twp_lift_step_fupd_glm Hnv)
  iintro %σ₁ %ε_now ⟨Hσ, Hε_now⟩
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset) with Hclose
  imodintro
  ihave ⟨Hε_now, Herr, %hLe⟩ : iprop(ErisWpGS.errInterp (rT := rT) ε_now ∗ ↯ε₁ ∗ ⌜ε₁ ≤ ε_now⌝)
      $$ [Hε_now Herr]
  · iapply errInterp_supply_bound
    isplitl [Hε_now]; · iexact Hε_now
    iexact Herr
  -- `urand` is reducible (probability measure), and `primStep = headStep = uniformReal`.
  have hhead : HeadReducible (Exp.urand : Exp rT) σ₁ := by
    show Cfg.uniformReal σ₁ ≠ 0; exact MeasureTheory.IsProbabilityMeasure.ne_zero _
  have hps : primStep (⟨Exp.urand, σ₁⟩ : Cfg rT) = Cfg.uniformReal σ₁ :=
    primStep_eq_headStep hhead
  -- The reach set is the real-literal image — measurable, and (via `concentratedOn_map`)
  -- co-null for the diffuse `uniformReal`.
  have hrange : {ρ : Cfg rT | ∃ r : rT, ρ = ⟨.lit (.real r), σ₁⟩}
      = (fun r : rT => (⟨.lit (.real r), σ₁⟩ : Cfg rT)) '' Set.univ := by
    ext ρ; simp only [Set.image_univ, Set.mem_range, Set.mem_setOf_eq]
    exact ⟨fun ⟨r, h⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm⟩⟩
  have hRmeas : MeasurableSet {ρ : Cfg rT | ∃ r : rT, ρ = ⟨.lit (.real r), σ₁⟩} := by
    rw [hrange, Set.image_univ]; exact (hgemb σ₁).measurableSet_range
  iapply glm'_prim_step
  iexists (fun ρ => ∃ (r : rT), ρ = (⟨.lit (.real r), σ₁⟩ : Cfg rT))
  iexists 0
  iexists (fun ρ : Cfg rT => (ε_now - ε₁) + match ρ.1 with
    | .lit (.real r) => ε₂ r
    | _ => 0)
  iexists ((ε_now - ε₁) + 1)
  -- Sub-goal 1: Reducible.
  isplitr
  · ipureintro; exact reducible_of_headReducible hhead
  -- Sub-goal 2: the reach support is measurable.
  isplitr
  · ipureintro; exact hRmeas
  -- Sub-goal 3: the per-outcome credit is bounded.
  isplitr
  · ipureintro
    intro ρ; simp only; gcongr
    split
    · exact Hbd _
    · exact zero_le
  -- Sub-goal 4: the integral budget — a genuine Lebesgue integral over `unifUnit`.
  isplitr
  · ipureintro
    rw [zero_add, MeasureTheory.lintegral_add_left measurable_const,
        MeasureTheory.lintegral_const]
    have hμ_le_one : (primStep ⟨Exp.urand, σ₁⟩) Set.univ ≤ 1 := primStep_univ_le_one _
    calc (ε_now - ε₁) * (primStep ⟨Exp.urand, σ₁⟩) Set.univ +
            ∫⁻ a : Cfg rT, (match a.1 with | .lit (.real r) => ε₂ r | _ => 0)
              ∂primStep ⟨Exp.urand, σ₁⟩
        ≤ (ε_now - ε₁) * 1 + ε₁ := by
          gcongr
          · have hGmeas : Measurable (fun a : Cfg rT =>
                match a.expr with | .lit (.real r) => ε₂ r | _ => (0 : ENNReal)) :=
              (measurable_litReal_elim ε₂ hε₂).comp Cfg.measurable_expr
            rw [hps,
              show Cfg.uniformReal σ₁
                  = (ProbLangℝ.unifUnit (T := rT)).map
                      (fun r : rT => (⟨.lit (.real r), σ₁⟩ : Cfg rT)) from rfl,
              MeasureTheory.lintegral_map hGmeas (hg σ₁)]
            exact HInt
      _ = ε_now := by rw [mul_one]; exact tsub_add_cancel_of_le hLe
  -- Sub-goal 5: `Pgl 0 R` — the `Concentrated`-on-image certificate (NO atoms).
  isplitr
  · ipureintro
    apply Pgl.of_concentrated
    rw [hps, hrange,
      show Cfg.uniformReal σ₁
          = (ProbLangℝ.unifUnit (T := rT)).map
              (fun r : rT => (⟨.lit (.real r), σ₁⟩ : Cfg rT)) from rfl]
    exact concentratedOn_map (hg σ₁)
      (by rw [Set.image_univ]; exact (hgemb σ₁).measurableSet_range) Concentrated.univ
  -- Sub-goal 6: per-outcome continuation, delivering `↯(ε₂ r)`.
  iintro %ρ %HRρ
  obtain ⟨r, Hρ_eq⟩ := HRρ
  subst Hρ_eq
  simp only
  ihave Hsupp1 : iprop(|==> ErisWpGS.errInterp (rT := rT) (ε_now - ε₁)) $$ [Hε_now Herr]
  · iapply errInterp_supply_decrease
    isplitl [Hε_now]; · iexact Hε_now
    iexact Herr
  imod Hsupp1 with Hε_minus
  imodintro
  by_cases hlt : (ε_now - ε₁) + ε₂ r < 1
  case neg =>
    push Not at hlt
    iapply execStutter_spend hlt
  case pos =>
    iapply execStutter_free
    imod (errInterp_supply_increase hlt) $$ Hε_minus with ⟨Hε_new, Hcr⟩
    imod Hclose with _
    ihave HΦ : iprop(Φ ⟨.lit (.real r), IsVal.lit⟩) $$ [Hcont Hcr]
    · iapply Hcont $$ %r
      iexact Hcr
    imodintro
    isplitl [Hσ]; · iexact Hσ
    isplitl [Hε_new]; · iexact Hε_new
    iapply (ErisWpGS.tglWp_value_of_toVal (v := ⟨.lit (.real r), IsVal.lit⟩) rfl)
    iexact HΦ

/-- **Demonstration of continuous error-credit conditioning at a uniform sample.**
A self-contained Total Eris proof: spend `↯ε₁` at a `urand` draw, where the
per-outcome credit is the constant `ε₁`. The budget side-condition is discharged
by the **Lebesgue integral** `∫⁻ r, ε₁ ∂unifUnit = ε₁ · unifUnit(univ) = ε₁`
(`unifUnit` is a probability measure). This is exactly the continuous analogue of
discrete `rand` error conditioning — the average is a `∫⁻ … ∂unifUnit`. -/
example {E : CoPset} {ε₁ : ENNReal} (hε₁ : ε₁ ≤ 1) {Φ : Val rT → IProp GF} :
    iprop(↯ε₁) ⊢@{IProp GF}
      iprop((∀ (r : rT), ↯ε₁ -∗ Φ (⟨.lit (.real r), IsVal.lit⟩ : Val rT)) -∗
      tglWp E Exp.urand Φ) :=
  twp_urand_exp measurable_const (fun _ => hε₁)
    (_root_.le_of_eq (by rw [MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]))

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
    · ipureintro; exact Hn
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
