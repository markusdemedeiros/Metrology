module

public import Metrology.TotalEris.ErisGS
public import Metrology.TotalEris.TotalPrimitiveLaws

@[expose] public section

/-! # Error credit rules  -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
open scoped ENNReal AppGS

namespace ProbLang

variable {rT : Type _} [ProbLang.ProbLangℝ rT]

-- TODO: Move me
def Exp.asLit (default : ℝ≥0∞) (value : BaseLit rT → ℝ≥0∞) : Exp rT → ℝ≥0∞ :=
  (fun x => x.getD default) ∘ Option.map value ∘ Exp.lit.π

-- TODO: Move me
-- TODO: Prove all of my siblings, for all measurable types
@[fun_prop]
theorem Exp.lit.π.measurable : Measurable (Exp.lit.π : Exp rT → Option (BaseLit rT)) := by
  refine Measurable.option_of_cov (cov := Set.range (Exp.lit : BaseLit rT → Exp rT))
    Exp.lit.measurableEmbedding.measurableSet_range ?_ ?_
  · ext e; cases e <;> simp [Exp.lit.π]
  · intro S hS
    have h : (Exp.lit.π : Exp rT → Option (BaseLit rT)) ⁻¹' (some '' S) = Exp.lit '' S := by
      ext e; cases e <;> simp [Exp.lit.π]
    rw [h]; exact Exp.lit.measurableEmbedding.measurableSet_image' hS

-- TODO: Move me
@[fun_prop]
theorem Exp.asValue_measurable (default : ℝ≥0∞) (value : BaseLit rT → ℝ≥0∞) (Hm : Measurable value) :
    Measurable (Exp.asLit default value) :=
  -- TODO: I should be by fun_prop
  ((Option.measurable_getD default).comp (Measurable.option_map Hm)).comp Exp.lit.π.measurable

def BaseLit.asInt (default : ℝ≥0∞) (value : Int → ℝ≥0∞) : BaseLit rT → ℝ≥0∞ :=
  (fun x => x.getD default) ∘ Option.map value ∘ BaseLit.int.π

@[fun_prop]
theorem BaseLit.int.π.measurable : Measurable (BaseLit.int.π : BaseLit rT → Option Int) := by
  refine Measurable.option_of_cov (cov := Set.range (BaseLit.int : Int → BaseLit rT))
    BaseLit.int.measurableEmbedding.measurableSet_range ?_ ?_
  · ext b; cases b <;> simp [BaseLit.int.π]
  · intro S hS
    have h : (BaseLit.int.π : BaseLit rT → Option Int) ⁻¹' (some '' S) = BaseLit.int '' S := by
      ext b; cases b <;> simp [BaseLit.int.π]
    rw [h]; exact BaseLit.int.measurableEmbedding.measurableSet_image' hS

-- `value : Int → ℝ≥0∞` needs no measurability hypothesis: `Int` carries the `⊤` σ-algebra.
@[fun_prop]
theorem BaseLit.asInt_measurable (default : ℝ≥0∞) (value : Int → ℝ≥0∞) :
    Measurable (BaseLit.asInt (rT := rT) default value) :=
  ((Option.measurable_getD default).comp (Measurable.option_map measurable_from_top)).comp
    BaseLit.int.π.measurable

def BaseLit.asReal (default : ℝ≥0∞) (value : rT → ℝ≥0∞) : BaseLit rT → ℝ≥0∞ :=
  (fun x => x.getD default) ∘ Option.map value ∘ BaseLit.real.π

@[fun_prop]
theorem BaseLit.real.π.measurable : Measurable (BaseLit.real.π : BaseLit rT → Option rT) := by
  refine Measurable.option_of_cov (cov := Set.range (BaseLit.real : rT → BaseLit rT))
    BaseLit.real.measurableEmbedding.measurableSet_range ?_ ?_
  · ext b; cases b <;> simp [BaseLit.real.π]
  · intro S hS
    have h : (BaseLit.real.π : BaseLit rT → Option rT) ⁻¹' (some '' S) = BaseLit.real '' S := by
      ext b; cases b <;> simp [BaseLit.real.π]
    rw [h]; exact BaseLit.real.measurableEmbedding.measurableSet_image' hS

@[fun_prop]
theorem BaseLit.asReal_measurable (default : ℝ≥0∞) (value : rT → ℝ≥0∞) (hv : Measurable value) :
    Measurable (BaseLit.asReal default value) :=
  ((Option.measurable_getD default).comp (Measurable.option_map hv)).comp
    BaseLit.real.π.measurable

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

/-- Use twp_rand_exp instead. It loses the boundedness hypothesis. -/
theorem twp_rand_exp_nat {E : CoPset} {z : Int} {ε₁ : ENNReal} {ε₂ : ℕ → ENNReal}
    {Φ : Val rT → IProp GF} (Hz : 0 < z) (Hbd : ∀ n, ε₂ n ≤ 1)
    (HSum : (∑ n ∈ Finset.range z.toNat, ε₂ n) / z.toNat ≤ ε₁) :
    -- (HSum : (∑' n : ℕ, if n < z.toNat then ε₂ n / z.toNat else 0) ≤ ε₁) :
    iprop(↯ε₁) ⊢@{IProp GF}
      iprop((∀ (n : Int), ⌜0 ≤ n ∧ n < z⌝ ∗ ↯(ε₂ n.toNat) -∗
        Φ (.int n : Val rT)) -∗
      tglWp E (.rand (.lit (.int z)) (.lit .unit)) Φ) := by
  iintro Herr Hcont
  have Hnv : (Exp.rand (Exp.lit (.int z)) (Exp.lit .unit) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (twp_lift_step_fupd_glm Hnv)
  iintro %σ₁ %ε_now ⟨Hσ, Hε_now⟩
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset) with Hclose
  imodintro
  ihave ⟨Hε_now, Herr, %hLe⟩ : iprop(ErisWpGS.errInterp (rT := rT) ε_now ∗ ↯ε₁ ∗ ⌜ε₁ ≤ ε_now⌝)
      $$ [Hε_now Herr]
  · iapply errInterp_supply_bound
    isplitl [Hε_now]; · iexact Hε_now
    iexact Herr
  -- Shared facts: `rand z ()` is head-reducible, and the support set is measurable.
  have hhead : HeadReducible (Exp.rand (.lit (.int z)) (.lit .unit)) σ₁ :=
    (HeadStepSupport.RandNoTapeS Hz (_root_.le_refl _) Hz).ne_zero
  have hRmeas : MeasurableSet
      {ρ : Cfg rT | ∃ n : Int, 0 ≤ n ∧ n < z ∧ ρ = (⟨.lit (.int n), σ₁⟩ : Cfg rT)} := by
    apply Set.Countable.measurableSet
    apply Set.Countable.mono (s₂ := (fun n : Int => (⟨.lit (.int n), σ₁⟩ : Cfg rT)) '' Set.univ)
    · rintro ρ ⟨n, _, _, rfl⟩; exact ⟨n, trivial, rfl⟩
    · exact Set.countable_univ.image _
  iapply glm'_prim_step
  iexists (fun ρ => ∃ (n : Int), 0 ≤ n ∧ n < z ∧ ρ = (⟨.lit (.int n), σ₁⟩ : Cfg rT))
  iexists 0
  iexists (fun ρ : Cfg rT => (ε_now - ε₁) + match ρ.1 with
    | .lit (.int n) => if h : 0 ≤ n ∧ n < z then ε₂ n.toNat else 0
    | _ => 0)
  iexists ((ε_now - ε₁) + 1)
  -- (1) the redex is reducible
  isplitr
  · ipureintro; exact Reducible.of_head hhead
  -- (2) the support set is measurable
  isplitr
  · ipureintro; exact hRmeas
  -- (3) the per-outcome credit never exceeds the supplied bound
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
    -- The variable credit is measurable, and `μ(univ) ≤ 1` lets `gcongr` discharge the
    -- multiplicative part automatically.
    have hφ : Measurable (fun a : Cfg rT => match a.expr with
        | .lit (.int n) => if h : 0 ≤ n ∧ n < z then ε₂ n.toNat else 0
        | _ => 0) := (measurable_litInt_elim _).comp Cfg.measurable_expr
    have hμ_le_one : (primStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁⟩) Set.univ ≤ 1 :=
      primStep_univ_le_one _
    calc (ε_now - ε₁) * (primStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁⟩) Set.univ +
            ∫⁻ (a : Cfg rT), (match a.expr with
                | .lit (.int n) => if h : 0 ≤ n ∧ n < z then ε₂ n.toNat else 0
                | _ => 0)
              ∂primStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁⟩
        ≤ (ε_now - ε₁) * 1 + ε₁ := by
          gcongr
          rw [primStep_eq_headStep hhead]
          show ∫⁻ a, (match a.expr with
              | .lit (.int n) => if h : 0 ≤ n ∧ n < z then ε₂ n.toNat else 0
              | _ => 0) ∂(Cfg.uniform z σ₁) ≤ ε₁
          -- Average over `Ico 0 z`; the `dif` is always taken there, so the sum is
          -- exactly `(∑ k < z, ε₂ k) / z` — i.e. `HSum`.
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
      _ = ε_now := by rw [mul_one]; exact tsub_add_cancel_of_le hLe
  isplitr
  · ipureintro
    show (primStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁⟩)
        {ρ : Cfg rT | ¬ ∃ (n : Int), 0 ≤ n ∧ n < z ∧ ρ = (⟨.lit (.int n), σ₁⟩ : Cfg rT)} ≤ 0
    refine _root_.le_of_eq ?_
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
        {ρ : Cfg rT | ¬ ∃ (n : Int), 0 ≤ n ∧ n < z ∧ ρ = (⟨.lit (.int n), σ₁⟩ : Cfg rT)} :=
      hRmeas.compl
    rw [hCfgUniform, MeasureTheory.Measure.map_apply hg hRc,
      PMF.toMeasure_apply_eq_zero_iff _ (hg hRc), PMF.support_uniformOfFinset,
      Set.disjoint_left]
    intro n hn hcontra
    rw [Finset.mem_coe, Finset.mem_Ico] at hn
    exact hcontra ⟨n, hn.1, hn.2, rfl⟩
  iintro %ρ %HRρ
  obtain ⟨n, Hn₁, Hn₂, Hρ_eq⟩ := HRρ
  subst Hρ_eq
  simp only [dif_pos (And.intro Hn₁ Hn₂)]
  ihave Hsupp1 : iprop(|==> ErisWpGS.errInterp (rT := rT) (ε_now - ε₁)) $$ [Hε_now Herr]
  · iapply errInterp_supply_decrease
    isplitl [Hε_now]; · iexact Hε_now
    iexact Herr
  imod Hsupp1 with Hε_minus
  imodintro
  by_cases hlt : (ε_now - ε₁) + ε₂ n.toNat < 1
  case neg =>
    push Not at hlt
    iapply execStutter_spend hlt
  case pos =>
    iapply execStutter_free
    imod (errInterp_supply_increase hlt) $$ Hε_minus with ⟨Hε_new, Hcr⟩
    imod Hclose with _
    ihave HΦ : iprop(Φ (.int n)) $$ [Hcont Hcr]
    · iapply Hcont $$ %n
      isplitr
      · ipureintro; exact ⟨Hn₁, Hn₂⟩
      iexact Hcr
    imodintro
    isplitl [Hσ]; · iexact Hσ
    isplitl [Hε_new]; · iexact Hε_new
    iapply (ErisWpGS.tglWp_value_of_toVal (v := (.int n : Val rT)) rfl)
    iexact HΦ

theorem twp_urand_exp {E : CoPset} {ε₁ : ENNReal}
    {ε₂ : rT → ENNReal} {Φ : Val rT → IProp GF}
    (hε₂ : Measurable ε₂) (Hbd : ∀ r, ε₂ r ≤ 1)
    (HInt : (∫⁻ r, ε₂ r ∂(ProbLangℝ.unifUnit (T := rT))) ≤ ε₁) :
    iprop(↯ε₁) ⊢@{IProp GF}
      iprop((∀ (r : rT), ↯(ε₂ r) -∗ Φ (.real r)) -∗
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
    ihave HΦ : iprop(Φ (.real r)) $$ [Hcont Hcr]
    · iapply Hcont $$ %r
      iexact Hcr
    imodintro
    isplitl [Hσ]; · iexact Hσ
    isplitl [Hε_new]; · iexact Hε_new
    iapply (ErisWpGS.tglWp_value_of_toVal (v := (.real r : Val rT)) rfl)
    iexact HΦ


theorem twp_rand_exp {E : CoPset} {z : Int} {ε₁ : ENNReal}
    {ε₂ : ℕ → ENNReal} {Φ : Val rT → IProp GF} (Hz : 0 < z)
    (HSum : (∑ n ∈ Finset.range z.toNat, ε₂ n) / z.toNat ≤ ε₁) :
    iprop(↯ε₁) ⊢@{IProp GF}
      iprop((∀ (n : Int), ⌜0 ≤ n ∧ n < z⌝ ∗ ↯(ε₂ n.toNat) -∗
        Φ (.int n : Val rT)) -∗
      tglWp E (.rand (.lit (.int z)) (.lit .unit)) Φ) := by
  sorry

/-
/-- Tutorial wrapper around `twp_rand_exp_nat` matching the form used in
`eris_rules.v:118` — phrases the sum as `∑ k < N+1, ε₂ k ≤ (N+1) * ε₁`.
Unlike the underlying `twp_rand_exp_nat`, this wrapper does NOT require
`ε₂ n ≤ 1`; values above 1 are clamped internally (see `eris_rules.v`). -/
theorem twp_rand_exp {E : CoPset} {z : Int} {ε₁ : ENNReal}
    {ε₂ : ℕ → ENNReal} {Φ : Val rT → IProp GF} (Hz : 0 < z)
    (HSum : (∑ n ∈ Finset.range z.toNat, ε₂ n) ≤ z.toNat * ε₁) :
    iprop(↯ε₁) ⊢@{IProp GF}
      iprop((∀ (n : Int), ⌜0 ≤ n ∧ n < z⌝ ∗ ↯(ε₂ n.toNat) -∗
        Φ (.int n : Val rT)) -∗
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
    iapply (ErrorCredit.ext (show min (ε₂ n.toNat) 1 = ε₂ n.toNat from _root_.min_eq_left h))
    iexact Hcr
  · -- `1 < ε₂ n`, so `min = 1` and `↯1` is contradictory.
    push Not at h
    iexfalso
    iapply (ErrorCredit.contradict (show (1 : ENNReal) ≤ 1 from _root_.le_refl _))
    iapply (ErrorCredit.ext (show min (ε₂ n.toNat) 1 = 1 from _root_.min_eq_right h.le))
    iexact Hcr
-/

end TotalEris
end ProbLang
