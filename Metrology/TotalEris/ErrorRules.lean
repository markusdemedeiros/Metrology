module

public import Metrology.TotalEris.ErisGS
public import Metrology.TotalEris.TotalPrimitiveLaws

@[expose] public section

/-! # Error credit rules  -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped ENNReal AppGS

namespace ProbLang

variable {rT : Type _} [ProbLang.ProbLangℝ rT]

-- TODO: Move me
def Exp.asLit (default : ℝ≥0∞) (value : BaseLit rT → ℝ≥0∞) : Exp rT → ℝ≥0∞ :=
  (fun x => x.getD default) ∘ Option.map value ∘ Exp.lit.π

@[fun_prop]
theorem Exp.asValue_measurable (default : ℝ≥0∞) (value : BaseLit rT → ℝ≥0∞) (Hm : Measurable value) :
    Measurable (Exp.asLit default value) := by unfold Exp.asLit; fun_prop

def BaseLit.asInt (default : ℝ≥0∞) (value : Int → ℝ≥0∞) : BaseLit rT → ℝ≥0∞ :=
  (fun x => x.getD default) ∘ Option.map value ∘ BaseLit.int.π

@[fun_prop]
theorem BaseLit.asInt_measurable (default : ℝ≥0∞) (value : Int → ℝ≥0∞) :
    Measurable (BaseLit.asInt (rT := rT) default value) := by unfold asInt; fun_prop

def BaseLit.asReal (default : ℝ≥0∞) (value : rT → ℝ≥0∞) : BaseLit rT → ℝ≥0∞ :=
  (fun x => x.getD default) ∘ Option.map value ∘ BaseLit.real.π

@[fun_prop]
theorem BaseLit.asReal_measurable (default : ℝ≥0∞) (value : rT → ℝ≥0∞) (hv : Measurable value) :
    Measurable (BaseLit.asReal default value) := by unfold asReal; fun_prop

theorem measurable_litInt_elim (g : Int → ENNReal) :
    Measurable (fun e : Exp rT => match e with | .lit (.int n) => g n | _ => 0) := by
  convert_to Measurable (Exp.asLit 0 (BaseLit.asInt 0 g))
  swap; fun_prop
  ext e
  cases e <;> try rfl
  case lit b => cases b <;> rfl

theorem measurable_litReal_elim (g : rT → ENNReal) (hg : Measurable g) :
    Measurable (fun e : Exp rT => match e with | .lit (.real r) => g r | _ => 0) := by
  convert_to Measurable (Exp.asLit 0 (BaseLit.asReal 0 g))
  swap; fun_prop
  ext e
  cases e <;> try rfl
  case lit r => cases r <;> rfl

namespace TotalEris

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]

open ErrorCredit

-- TODO: Delete me? trivial wrapper around supply_bound that changes sep for wand
-- Only here for unfolding
theorem errInterp_supply_decrease {εₛ ε : ENNReal} : iprop%
    errInterp (rT := rT) εₛ ∗ ↯ε ⊢@{IProp GF} |==> errInterp (rT := rT) (εₛ - ε) := by
  show iprop% ecAuth εₛ ∗ ↯ε ⊢ |==> ecAuth (εₛ - ε)
  iintro ⟨Hs, Hε⟩
  iapply supply_decrease $$ Hs Hε

-- TODO: Delete me? trivial wrapper around supply_bound that changes sep for wand
-- Only here for unfolding
theorem errInterp_supply_bound {εₛ ε : ENNReal} : iprop%
    errInterp (rT := rT) εₛ ∗ ↯ε ⊢@{IProp GF} errInterp (rT := rT) εₛ ∗ ↯ε ∗ ⌜ε ≤ εₛ⌝ := by
  show iprop% ●↯ εₛ ∗ ↯ε ⊢ ●↯ εₛ ∗ ↯ε ∗ ⌜ε ≤ εₛ⌝
  iintro ⟨Hs, Hε⟩
  ihave %hLe := supply_bound $$ Hs Hε
  iframe Hs Hε %hLe

-- TODO: Delete me?
-- Only here for unfolding
theorem errInterp_supply_increase {ε δ : ENNReal} (h : ε + δ < 1) : iprop%
    errInterp (rT := rT) ε ⊢@{IProp GF} |==> (errInterp (rT := rT) (ε + δ) ∗ ↯δ) :=
  ErrorCredit.supply_increase h

theorem twp_err_incr {E : CoPset} {e : Exp rT} {ε : ENNReal} {Φ : Val rT → IProp GF}
    (Hnv : e.toVal? = none) : iprop%
    (↯ε ∗ ∀ (ε' : ENNReal), ⌜ε < ε'⌝ -∗ ↯ε' -∗ tglWp E e Φ) ⊢@{IProp GF} tglWp E e Φ := by
  iintro ⟨Herr, Hwp⟩
  iapply twp_lift_step_fupd_glm Hnv
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
    imod Hclose with -
    have hbnd : ε₂ + (ε' - ε₂) < 1 := by rw [add_tsub_cancel_of_le Hε'.le]; exact hlt
    conv_rhs => rw [← add_tsub_cancel_of_le Hε'.le]
    imod errInterp_supply_increase hbnd $$ Hε₂ with ⟨HsuppNew, Hfrag⟩
    icombine Herr Hfrag as Herr'
    ihave %hValid := valid $$ Herr'
    ispecialize Hwp $$ %(ε + (ε' - ε₂)) %?bound Herr'
    case bound =>
      refine ENNReal.lt_add_right ?_ ?_
      · intro hε_top; simp [hε_top] at hValid
      · rw [Ne, _root_.tsub_eq_zero_iff_le]; exact _root_.not_le.mpr Hε'
    ihave Hwp := (BI.equiv_iff.mp tglWp_unfold).1 $$ Hwp
    rw (occs := [2]) [tglWpPre_eq_step Hnv]
    imod Hwp $$ %σ₁ %(ε₂ + (ε' - ε₂)) [$] with HGlm
    imodintro
    iapply execStutter_free
    iexact HGlm

/-- Thin-air credit rule: A client is free to assume an arbitrarily small error credit. -/
theorem twp_err_pos {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} (Hnv : e.toVal? = none) :
    iprop% (∀ ε, ⌜0 < ε⌝ -∗ ↯ε -∗ tglWp E e Φ) ⊢@{IProp GF} tglWp E e Φ := by
  iintro Hwp
  iapply fupd_tglWp
  imod zero with Herr
  imodintro
  iapply twp_err_incr (ε := 0) Hnv
  iframe

/-- Countability-free `lintegral` against `Cfg.uniform`: for a **measurable** `φ`,
the integral is the `Ico`-average. Unlike `Cfg.lintegral_uniform`, measurability of `φ`
is supplied rather than derived from discreteness, so no `[Countable rT]` is needed. -/
theorem Cfg.lintegral_uniform' {z : Int} (Hz : 0 < z) (σ : State rT)
    {φ : Cfg rT → ENNReal} (hφ : Measurable φ) :
    ∫⁻ c, φ c ∂(Cfg.uniform z σ)
      = (z.toNat : ENNReal)⁻¹ * ∑ n ∈ Finset.Ico (0 : Int) z, φ ⟨.lit (.int n), σ⟩ := by
  have Huniform : Cfg.uniform z σ
      = ((PMF.uniformOfFinset (Finset.Ico (0 : Int) z)
          (Finset.nonempty_Ico.mpr Hz)).toMeasure).map
            (fun n : Int => (⟨.lit (.int n), σ⟩ : Cfg rT)) := by
    unfold Cfg.uniform Int.isPos; simp only [Hz, dite_true]
  have hcard : (Finset.Ico (0 : Int) z).card = z.toNat := by rw [Int.card_Ico]; omega
  rw [Huniform, MeasureTheory.lintegral_map hφ Measurable.of_discrete,
      MeasureTheory.lintegral_countable',
      tsum_eq_sum (s := Finset.Ico (0 : Int) z) fun n hn => by
        rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
            PMF.uniformOfFinset_apply_of_notMem _ hn, mul_zero],
      Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
      PMF.uniformOfFinset_apply_of_mem _ hn, hcard, mul_comm]

/-- Generic error-spending presample rule, factoring out the `glm'` plumbing shared by
`twp_rand_exp_nat` and `twp_urand_exp`.

Given a reach predicate `R σ₁` (the configurations reachable from `⟨e₁, σ₁⟩` that the
continuation must handle), a per-outcome credit `f`, reducibility, measurability, a `Pgl 0`
certificate and an integral budget `∫ f ≤ ε₁`, it discharges `tglWp E e₁ Φ` from a
continuation that, for each reached `ρ`, consumes exactly `↯(f ρ)`.

The whole proof spends the supply `ε₁` up front (leaving `ε_now - ε₁`), pushes the credit
through `glm'_prim_step` with offset `0` and bound `(ε_now - ε₁) + 1`, and on each reached
`ρ` either stutters (when `(ε_now - ε₁) + f ρ ≥ 1`) or hands `↯(f ρ)` to the continuation. -/
theorem twp_glm_spend {E : CoPset} {e₁ : Exp rT} {ε₁ : ENNReal}
    {Φ : Val rT → IProp GF} {R : State rT → Cfg rT → Prop} {f : Cfg rT → ENNReal}
    (hv : e₁.toVal? = none)
    (Hbd : ∀ ρ, f ρ ≤ 1)
    (Hstate : ∀ {σ₁ : State rT} {ρ : Cfg rT}, R σ₁ ρ → ρ.state = σ₁)
    (Hred : ∀ σ₁, Reducible e₁ σ₁)
    (hRmeas : ∀ σ₁, MeasurableSet {ρ : Cfg rT | R σ₁ ρ})
    (hPgl : ∀ σ₁, Pgl 0 (R σ₁) (primStep ⟨e₁, σ₁⟩))
    (HInt : ∀ σ₁, (∫⁻ ρ, f ρ ∂(primStep ⟨e₁, σ₁⟩)) ≤ ε₁) :
    iprop(↯ε₁) ⊢@{IProp GF}
      iprop((∀ (σ₁ : State rT) (ρ : Cfg rT), ⌜R σ₁ ρ⌝ -∗ ↯(f ρ) -∗ tglWp E ρ.expr Φ) -∗
      tglWp E e₁ Φ) := by
  iintro Herr Hcont
  iapply (twp_lift_step_fupd_glm hv)
  iintro %σ₁ %ε_now ⟨Hσ, Hε_now⟩
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset) with Hclose
  imodintro
  ihave ⟨Hε_now, Herr, %hLe⟩ : iprop(ErisWpGS.errInterp (rT := rT) ε_now ∗ ↯ε₁ ∗ ⌜ε₁ ≤ ε_now⌝)
      $$ [Hε_now Herr]
  · iapply errInterp_supply_bound; iframe Hε_now Herr
  iapply glm'_prim_step
  iexists (R σ₁), 0, (fun ρ : Cfg rT => (ε_now - ε₁) + f ρ), ((ε_now - ε₁) + 1)
  -- (1) reducible  (2) measurable reach set  (3) per-outcome credit bounded
  isplitr; · ipureintro; exact Hred σ₁
  isplitr; · ipureintro; exact hRmeas σ₁
  isplitr; · ipureintro; intro ρ; simp only; gcongr; exact Hbd ρ
  -- (4) integral budget: `(ε_now - ε₁)·μ(univ) + ∫ f ≤ (ε_now - ε₁) + ε₁ = ε_now`.
  isplitr
  · ipureintro
    rw [zero_add, MeasureTheory.lintegral_add_left measurable_const,
        MeasureTheory.lintegral_const]
    calc (ε_now - ε₁) * (primStep ⟨e₁, σ₁⟩) Set.univ + ∫⁻ ρ, f ρ ∂primStep ⟨e₁, σ₁⟩
        ≤ (ε_now - ε₁) * 1 + ε₁ := by gcongr; exacts [primStep_univ_le_one _, HInt σ₁]
      _ = ε_now := by rw [mul_one]; exact tsub_add_cancel_of_le hLe
  -- (5) the `Pgl 0` certificate.
  isplitr; · ipureintro; exact hPgl σ₁
  -- (6) per-outcome continuation: refund the spent supply, then either stutter or continue.
  iintro %ρ %HRρ
  ihave Hsupp1 : iprop(|==> ErisWpGS.errInterp (rT := rT) (ε_now - ε₁)) $$ [Hε_now Herr]
  · iapply errInterp_supply_decrease; iframe Hε_now Herr
  imod Hsupp1 with Hε_minus
  imodintro
  by_cases hlt : (ε_now - ε₁) + f ρ < 1
  -- The budget for `ρ` already covers a full unit of credit: stutter.
  case neg => push Not at hlt; iapply execStutter_spend hlt
  -- Otherwise, top the supply back up to `(ε_now - ε₁) + f ρ`, freeing `↯(f ρ)` for `Hcont`.
  case pos =>
    iapply execStutter_free
    imod (errInterp_supply_increase hlt) $$ Hε_minus with ⟨Hε_new, Hcr⟩
    imod Hclose with _
    imodintro
    isplitl [Hσ]; · rw [Hstate HRρ]; iexact Hσ
    isplitl [Hε_new]; · iexact Hε_new
    iapply Hcont $$ %σ₁ %ρ %HRρ
    iexact Hcr

/-- Use twp_rand_exp instead. It loses the boundedness hypothesis. -/
theorem twp_rand_exp_nat {E : CoPset} {z : Int} {ε₁ : ENNReal} {ε₂ : ℕ → ENNReal}
    {Φ : Val rT → IProp GF} (Hz : 0 < z) (Hbd : ∀ n, ε₂ n ≤ 1)
    (HSum : (∑ n ∈ Finset.range z.toNat, ε₂ n) / z.toNat ≤ ε₁) :
    -- (HSum : (∑' n : ℕ, if n < z.toNat then ε₂ n / z.toNat else 0) ≤ ε₁) :
    iprop(↯ε₁) ⊢@{IProp GF}
      iprop((∀ (n : Int), ⌜0 ≤ n ∧ n < z⌝ ∗ ↯(ε₂ n.toNat) -∗
        Φ (.int n : Val rT)) -∗
      tglWp E (.rand (.lit (.int z)) (.lit .unit)) Φ) := by
  -- `rand z ()` is a non-value, head-reducible at every state (`primStep = Cfg.uniform z`).
  have Hnv : (Exp.rand (Exp.lit (.int z)) (Exp.lit .unit) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  have hhead : ∀ σ₁ : State rT, HeadReducible (Exp.rand (.lit (.int z)) (.lit .unit)) σ₁ :=
    fun σ₁ => (HeadStepSupport.RandNoTapeS Hz (_root_.le_refl _) Hz).ne_zero
  -- Reach predicate `R` (the integers `0 ≤ n < z`) and per-outcome credit `f`.
  set R : State rT → Cfg rT → Prop :=
    fun σ₁ ρ => ∃ n : Int, 0 ≤ n ∧ n < z ∧ ρ = (⟨.lit (.int n), σ₁⟩ : Cfg rT)
  set f : Cfg rT → ENNReal := fun ρ => match ρ.expr with
    | .lit (.int n) => if h : 0 ≤ n ∧ n < z then ε₂ n.toNat else 0
    | _ => 0 with hf
  -- Discharge the six `twp_glm_spend` obligations, in signature order.
  have hbd : ∀ ρ : Cfg rT, f ρ ≤ 1 := by
    intro ρ; simp only [hf]; split
    · split <;> first | exact Hbd _ | exact zero_le
    · exact zero_le
  have hstate : ∀ {σ₁ : State rT} {ρ : Cfg rT}, R σ₁ ρ → ρ.state = σ₁ := by
    rintro σ₁ ρ ⟨n, _, _, rfl⟩; rfl
  have hred : ∀ σ₁, Reducible (Exp.rand (.lit (.int z)) (.lit .unit)) σ₁ :=
    fun σ₁ => Reducible.of_head (by is_lc) (hhead σ₁)
  have hrmeas : ∀ σ₁ : State rT, MeasurableSet {ρ : Cfg rT | R σ₁ ρ} := fun σ₁ => by
    apply Set.Countable.measurableSet
    apply Set.Countable.mono (s₂ := (fun n : Int => (⟨.lit (.int n), σ₁⟩ : Cfg rT)) '' Set.univ)
    · rintro ρ ⟨n, _, _, rfl⟩; exact ⟨n, trivial, rfl⟩
    · exact Set.countable_univ.image _
  -- `Pgl 0`: the complement of the reach set is null under the uniform step.
  have hpgl : ∀ σ₁ : State rT,
      Pgl 0 (R σ₁) (primStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁⟩) := fun σ₁ => by
    show (primStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁⟩) {ρ : Cfg rT | ¬ R σ₁ ρ} ≤ 0
    refine _root_.le_of_eq ?_
    rw [primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible (by is_lc) (hhead σ₁))]
    show (Cfg.uniform z σ₁) {ρ : Cfg rT | ¬ R σ₁ ρ} = 0
    have hCfgUniform :
        Cfg.uniform z σ₁ =
          (PMF.uniformOfFinset (Finset.Ico (0:Int) z)
              (Finset.nonempty_Ico.mpr Hz)).toMeasure.map
            (fun n : Int => (⟨.lit (.int n), σ₁⟩ : Cfg rT)) := by
      unfold Cfg.uniform; simp only [Int.isPos, dif_pos Hz]
    have hg : Measurable (fun n : Int => (⟨.lit (.int n), σ₁⟩ : Cfg rT)) := Measurable.of_discrete
    have hRc : MeasurableSet {ρ : Cfg rT | ¬ R σ₁ ρ} := (hrmeas σ₁).compl
    rw [hCfgUniform, MeasureTheory.Measure.map_apply hg hRc,
      PMF.toMeasure_apply_eq_zero_iff _ (hg hRc), PMF.support_uniformOfFinset,
      Set.disjoint_left]
    intro n hn hcontra
    rw [Finset.mem_coe, Finset.mem_Ico] at hn
    exact hcontra ⟨n, hn.1, hn.2, rfl⟩
  -- Integral budget: averaging `f` over `Ico 0 z` (the `dif` is always taken) gives `HSum`.
  have hint : ∀ σ₁ : State rT,
      (∫⁻ ρ, f ρ ∂(primStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁⟩)) ≤ ε₁ := fun σ₁ => by
    have hφ : Measurable f := (measurable_litInt_elim _).comp Cfg.measurable_expr
    rw [primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible (by is_lc) (hhead σ₁))]
    show (∫⁻ ρ, f ρ ∂(Cfg.uniform z σ₁)) ≤ ε₁
    rw [Cfg.lintegral_uniform' Hz σ₁ hφ, ← ENNReal.div_eq_inv_mul]
    convert HSum using 2
    refine Finset.sum_nbij' (i := fun n : Int => n.toNat) (j := (Nat.cast : ℕ → Int))
      ?_ ?_ (fun n hn => Int.toNat_of_nonneg (Finset.mem_Ico.mp hn).1)
      (fun k _ => Int.toNat_natCast k) ?_
    · intro n hn; simp only [Finset.mem_Ico] at hn; simp only [Finset.mem_range]; omega
    · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Ico]; omega
    · intro n hn
      simp only [Finset.mem_Ico] at hn
      show (if h : 0 ≤ n ∧ n < z then ε₂ n.toNat else 0) = ε₂ n.toNat
      exact dif_pos ⟨hn.1, hn.2⟩
  iintro Herr Hcont
  iapply (twp_glm_spend (R := R) (f := f) Hnv hbd hstate hred hrmeas hpgl hint) $$ Herr
  -- The reached value is `.int n`, carrying `↯(ε₂ n.toNat)`; hand it to `Hcont`.
  iintro %σ₁ %ρ %HRρ Hcr
  obtain ⟨n, Hn₁, Hn₂, rfl⟩ := HRρ
  have hfe : f (⟨.lit (.int n), σ₁⟩ : Cfg rT) = ε₂ n.toNat := by
    simp only [hf]; exact dif_pos ⟨Hn₁, Hn₂⟩
  iapply (ErisWpGS.tglWp_value_of_toVal (v := (.int n : Val rT)) rfl)
  iapply Hcont $$ %n
  isplitr
  · ipureintro; exact ⟨Hn₁, Hn₂⟩
  rw [← hfe]; iexact Hcr

theorem twp_urand_exp {E : CoPset} {ε₁ : ENNReal}
    {ε₂ : rT → ENNReal} {Φ : Val rT → IProp GF}
    (hε₂ : Measurable ε₂) (Hbd : ∀ r, ε₂ r ≤ 1)
    (HInt : (∫⁻ r, ε₂ r ∂(ProbLangℝ.unifUnit (T := rT))) ≤ ε₁) :
    iprop(↯ε₁) ⊢@{IProp GF}
      iprop((∀ (r : rT), (⌜r ∈ ProbLangℝ.unifUnitSupport⌝ ∗ ↯(ε₂ r)) -∗ Φ (.real r)) -∗
      tglWp E Exp.urand Φ) := by
  -- `urand` is a non-value, head-reducible at every state (`primStep = uniformReal`).
  have Hnv : (Exp.urand : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  have hhead : ∀ σ₁ : State rT, HeadReducible (Exp.urand : Exp rT) σ₁ :=
    fun σ₁ => show Cfg.uniformReal σ₁ ≠ 0 from MeasureTheory.IsProbabilityMeasure.ne_zero _
  -- The real-literal injection: `primStep = uniformReal = unifUnit.map inj`, and `inj` embeds.
  have hps : ∀ σ₁ : State rT, primStep (⟨Exp.urand, σ₁⟩ : Cfg rT)
      = (ProbLangℝ.unifUnit (T := rT)).map (fun r : rT => (⟨.lit (.real r), σ₁⟩ : Cfg rT)) :=
    fun σ₁ => primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible (by is_lc) (hhead σ₁))
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
  -- Reach predicate `R` (the real-literal image) and per-outcome credit `f`.
  set R : State rT → Cfg rT → Prop :=
    fun σ₁ ρ => ∃ r : rT, ρ = (⟨.lit (.real r), σ₁⟩ : Cfg rT) ∧ r ∈ ProbLangℝ.unifUnitSupport
    with hR
  set f : Cfg rT → ENNReal := fun ρ => match ρ.expr with
    | .lit (.real r) => ε₂ r
    | _ => 0 with hf
  -- The reach set is exactly the image of the injection (used by `hrmeas` and `hpgl`).
  have hrange : ∀ σ₁ : State rT, {ρ : Cfg rT | R σ₁ ρ}
      = (fun r : rT => (⟨.lit (.real r), σ₁⟩ : Cfg rT)) '' ProbLangℝ.unifUnitSupport := fun σ₁ => by
    ext ρ; simp only [Set.mem_image, Set.mem_setOf_eq, hR]
    exact ⟨fun ⟨r, h, hr⟩ => ⟨r, hr, h.symm⟩, fun ⟨r, hr, h⟩ => ⟨r, h.symm, hr⟩⟩
  -- Discharge the six `twp_glm_spend` obligations, in signature order.
  have hbd : ∀ ρ : Cfg rT, f ρ ≤ 1 := by
    intro ρ; simp only [hf]; split
    · exact Hbd _
    · exact zero_le
  have hstate : ∀ {σ₁ : State rT} {ρ : Cfg rT}, R σ₁ ρ → ρ.state = σ₁ := by
    rintro σ₁ ρ ⟨r, rfl, _⟩; rfl
  have hred : ∀ σ₁, Reducible (Exp.urand : Exp rT) σ₁ :=
    fun σ₁ => reducible_of_headReducible (by is_lc) (hhead σ₁)
  have hrmeas : ∀ σ₁ : State rT, MeasurableSet {ρ : Cfg rT | R σ₁ ρ} := fun σ₁ => by
    rw [hrange σ₁]
    exact (hgemb σ₁).measurableSet_image.mpr ProbLangℝ.unifUnitSupportMeasurable
  -- `Pgl 0`: the diffuse `uniformReal` is concentrated on the (co-null) image.
  have hpgl : ∀ σ₁ : State rT, Pgl 0 (R σ₁) (primStep ⟨Exp.urand, σ₁⟩) := fun σ₁ => by
    apply Pgl.of_concentrated
    rw [hps σ₁, hrange σ₁]
    exact concentratedOn_map (hg σ₁)
      ((hgemb σ₁).measurableSet_image.mpr ProbLangℝ.unifUnitSupportMeasurable)
      ProbLangℝ.unifUnitIsConcentrated
  -- Integral budget: push `f` through the real-literal map onto `unifUnit`, then `HInt`.
  have hint : ∀ σ₁ : State rT,
      (∫⁻ ρ, f ρ ∂(primStep ⟨Exp.urand, σ₁⟩)) ≤ ε₁ := fun σ₁ => by
    have hφ : Measurable f := (measurable_litReal_elim ε₂ hε₂).comp Cfg.measurable_expr
    rw [hps σ₁, MeasureTheory.lintegral_map hφ (hg σ₁)]
    exact HInt
  iintro Herr Hcont
  iapply (twp_glm_spend (R := R) (f := f) Hnv hbd hstate hred hrmeas hpgl hint) $$ Herr
  -- The reached value is `.real r`, carrying `↯(ε₂ r)`; hand it to `Hcont`.
  iintro %σ₁ %ρ %HRρ Hcr
  obtain ⟨r, rfl, hrsupp⟩ := HRρ
  have hfe : f (⟨.lit (.real r), σ₁⟩ : Cfg rT) = ε₂ r := by simp only [hf]
  iapply (ErisWpGS.tglWp_value_of_toVal (v := (.real r : Val rT)) rfl)
  iapply Hcont $$ %r
  isplitr [Hcr]
  · ipureintro; exact hrsupp
  · rw [← hfe]; iexact Hcr

/-- Bound-free `urand` error rule: applies `twp_urand_exp` with the clamped credit
`F r := min (ε₂ r) 1`. Clamping only shrinks the integral, so `HInt` still holds;
per-outcome, either `ε₂ r ≤ 1` (clamp is a no-op) or `ε₂ r > 1` (then `↯1` is already
contradictory). -/
theorem twp_urand_exp' {E : CoPset} {ε₁ : ENNReal}
    {ε₂ : rT → ENNReal} {Φ : Val rT → IProp GF}
    (hε₂ : Measurable ε₂)
    (HInt : (∫⁻ r, ε₂ r ∂(ProbLangℝ.unifUnit (T := rT))) ≤ ε₁) :
    iprop(↯ε₁) ⊢@{IProp GF}
      iprop((∀ (r : rT), (⌜r ∈ ProbLangℝ.unifUnitSupport⌝ ∗ ↯(ε₂ r)) -∗ Φ (.real r)) -∗
      tglWp E Exp.urand Φ) := by
  iintro Herr Hcont
  -- Clamping shrinks the integrand pointwise, so the budget `HInt` survives.
  have hint : (∫⁻ r, min (ε₂ r) 1 ∂(ProbLangℝ.unifUnit (T := rT))) ≤ ε₁ :=
    (MeasureTheory.lintegral_mono fun r => _root_.min_le_left _ _).trans HInt
  iapply (twp_urand_exp (ε₂ := fun r => min (ε₂ r) 1) (hε₂.min measurable_const)
    (fun r => _root_.min_le_right _ _) hint) $$ Herr
  -- Continuation: case-split on whether `ε₂ r` is already `≤ 1`.
  iintro %r ⟨%hrsupp, Hcr⟩
  by_cases h : ε₂ r ≤ 1
  · -- `min (ε₂ r) 1 = ε₂ r`: rewrite the credit and feed `Hcont`.
    iapply Hcont $$ %r
    isplitr [Hcr]
    · ipureintro; exact hrsupp
    · iapply (ErrorCredit.ext (show min (ε₂ r) 1 = ε₂ r from _root_.min_eq_left h))
      iexact Hcr
  · -- `1 < ε₂ r`, so the clamp gives `↯1`, which is contradictory.
    push Not at h
    iexfalso
    iapply (ErrorCredit.contradict (le_min h.le (_root_.le_refl 1)))
    iexact Hcr

/-- Bound-free rand error rule: applies `twp_rand_exp_nat` with the clamped credit
`F n := min (ε₂ n) 1`. Clamping only shrinks the sum, so `HSum` still holds; per-outcome,
either `ε₂ n ≤ 1` (clamp is a no-op) or `ε₂ n > 1` (then `↯1` is already contradictory). -/
theorem twp_rand_exp {E : CoPset} {z : Int} {ε₁ : ENNReal}
    {ε₂ : ℕ → ENNReal} {Φ : Val rT → IProp GF} (Hz : 0 < z)
    (HSum : (∑ n ∈ Finset.range z.toNat, ε₂ n) / z.toNat ≤ ε₁) :
    iprop(↯ε₁) ⊢@{IProp GF}
      iprop((∀ (n : Int), ⌜0 ≤ n ∧ n < z⌝ ∗ ↯(ε₂ n.toNat) -∗
        Φ (.int n : Val rT)) -∗
      tglWp E (.rand (.lit (.int z)) (.lit .unit)) Φ) := by
  iintro Herr Hcont
  -- Clamping shrinks each summand, so the averaged bound `HSum` survives.
  have hsum : (∑ n ∈ Finset.range z.toNat, min (ε₂ n) 1) / (z.toNat : ENNReal) ≤ ε₁ :=
    (ENNReal.div_le_div_right
      (Finset.sum_le_sum fun n _ => _root_.min_le_left _ _) _).trans HSum
  iapply (twp_rand_exp_nat (ε₂ := fun n => min (ε₂ n) 1) Hz
    (fun n => _root_.min_le_right _ _) hsum) $$ Herr
  -- Continuation: case-split on whether `ε₂ n` is already `≤ 1`.
  iintro %n ⟨%Hn, Hcr⟩
  by_cases h : ε₂ n.toNat ≤ 1
  · -- `min (ε₂ n) 1 = ε₂ n`: rewrite the credit and feed `Hcont`.
    iapply Hcont $$ %n
    isplitr
    · ipureintro; exact Hn
    iapply (ErrorCredit.ext (show min (ε₂ n.toNat) 1 = ε₂ n.toNat from _root_.min_eq_left h))
    iexact Hcr
  · -- `1 < ε₂ n`, so the clamp gives `↯1`, which is contradictory.
    push Not at h
    iexfalso
    iapply (ErrorCredit.contradict (le_min h.le (_root_.le_refl 1)))
    iexact Hcr

end TotalEris
end ProbLang
