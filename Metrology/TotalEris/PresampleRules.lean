module

public import Metrology.TotalEris.TotalPrimitiveLaws
public import Metrology.TotalEris.TotalLifting
public import Metrology.TotalEris.Glm
public import Metrology.TotalEris.ErrorRules

@[expose] public section

/-! # Presample rules (port of `clutch/theories/eris/presample_rules.v`). -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal

namespace ProbLang
namespace TotalEris

variable {rT : Type _} [ProbLang.ProbLangℝ rT]

omit [ProbLang.ProbLangℝ rT] in
/-- Distinct samples append distinct tape suffixes, so the presample state-update is injective. -/
theorem presample_update_injective {σ : State rT} {α : Loc} {N : Int}
    {bs : List { z : Int // 0 ≤ z ∧ z < N }} :
    Function.Injective (fun n : { z : Int // 0 ≤ z ∧ z < N } =>
      σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) := by
  intro n₁ n₂ heq
  have htape_eq : (σ.tapes.insert α ⟨N, bs ++ [n₁]⟩) = (σ.tapes.insert α ⟨N, bs ++ [n₂]⟩) := by
    have := congrArg State.tapes heq
    simpa [State.update_tapes] using this
  have hget₁ : (σ.tapes.insert α ⟨N, bs ++ [n₁]⟩)[α]? = some ⟨N, bs ++ [n₁]⟩ :=
    Std.ExtTreeMap.getElem?_insert_self
  have hget₂ : (σ.tapes.insert α ⟨N, bs ++ [n₂]⟩)[α]? = some ⟨N, bs ++ [n₂]⟩ :=
    Std.ExtTreeMap.getElem?_insert_self
  rw [htape_eq] at hget₁
  rw [hget₂] at hget₁
  have hbs : bs ++ [n₂] = bs ++ [n₁] := by simpa using hget₁
  exact ((List.cons.injEq _ _ _ _).mp (List.append_cancel_left hbs)).1.symm

/-- The presample support is a countable set of tape-updated states, hence measurable. -/
theorem presample_support_measurableSet {σ₁ : State rT} {α : Loc} {N : Int}
    {bs : List { z : Int // 0 ≤ z ∧ z < N }} :
    MeasurableSet {σ' : State rT | ∃ n : { z : Int // 0 ≤ z ∧ z < N },
      σ' = σ₁.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)} := by
  apply Set.Countable.measurableSet
  apply Set.Countable.mono (s₂ := (fun n : { z : Int // 0 ≤ z ∧ z < N } =>
    σ₁.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) '' Set.univ)
  · rintro σ' ⟨n, rfl⟩; exact ⟨n, trivial, rfl⟩
  · exact Set.countable_univ.image _

open Classical in
/-- Per-outcome credit for advanced composition: `ε₂ n` on the `n`-update, `0` off-support. -/
noncomputable def presampleAdvCompX₂
    (σ : State rT) (α : Loc) (N : Int)
    (bs : List { z : Int // 0 ≤ z ∧ z < N })
    (ε₂ : { z : Int // 0 ≤ z ∧ z < N } → ENNReal) (σ' : State rT) : ENNReal :=
  if h : ∃ n : { z : Int // 0 ≤ z ∧ z < N },
      σ' = σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)
    then ε₂ (Classical.choose h)
    else 0

open Classical in
/-- `presampleAdvCompX₂` is measurable: a countable sum of singleton indicators. -/
theorem presampleAdvCompX₂.measurable
    (σ : State rT) (α : Loc) (N : Int)
    (bs : List { z : Int // 0 ≤ z ∧ z < N })
    (ε₂ : { z : Int // 0 ≤ z ∧ z < N } → ENNReal) :
    Measurable (presampleAdvCompX₂ σ α N bs ε₂) := by
  have hrw : presampleAdvCompX₂ σ α N bs ε₂
      = fun σ' => ∑' n : { z : Int // 0 ≤ z ∧ z < N },
          ({σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)} : Set (State rT)).indicator
            (fun _ => ε₂ n) σ' := by
    funext σ'
    unfold presampleAdvCompX₂
    by_cases h : ∃ n : { z : Int // 0 ≤ z ∧ z < N },
        σ' = σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)
    · rw [dif_pos h]
      have hc : σ' = σ.update_tapes (·.insert α ⟨N, bs ++ [Classical.choose h]⟩) :=
        Classical.choose_spec h
      rw [tsum_eq_single (Classical.choose h) ?_]
      · rw [Set.indicator_of_mem (Set.mem_singleton_iff.mpr hc)]
      · intro n hn
        apply Set.indicator_of_notMem
        rw [Set.mem_singleton_iff]
        intro hcontra
        exact hn (presample_update_injective (hc.symm.trans hcontra)).symm
    · rw [dif_neg h]
      refine (ENNReal.tsum_eq_zero.mpr fun n => ?_).symm
      apply Set.indicator_of_notMem
      rw [Set.mem_singleton_iff]
      intro hcontra
      exact h ⟨n, hcontra⟩
  rw [hrw]
  exact Measurable.tsum fun n =>
    measurable_const.indicator (measurableSet_singleton _)

open Classical in
omit [ProbLang.ProbLangℝ rT] in
/-- On the `n`-update state, `presampleAdvCompX₂` extracts exactly `ε₂ n`. -/
@[simp] theorem presampleAdvCompX₂_update (σ : State rT) (α : Loc) (N : Int)
    (bs : List { z : Int // 0 ≤ z ∧ z < N })
    (ε₂ : { z : Int // 0 ≤ z ∧ z < N } → ENNReal) (n : { z : Int // 0 ≤ z ∧ z < N }) :
    presampleAdvCompX₂ σ α N bs ε₂ (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) = ε₂ n := by
  unfold presampleAdvCompX₂
  rw [dif_pos ⟨n, rfl⟩, show Classical.choose _ = n from (presample_update_injective
    (Classical.choose_spec (⟨n, rfl⟩ : ∃ n' : { z : Int // 0 ≤ z ∧ z < N },
      σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩) =
        σ.update_tapes (·.insert α ⟨N, bs ++ [n']⟩)))).symm]

open Classical in
omit [ProbLang.ProbLangℝ rT] in
/-- `presampleAdvCompX₂` inherits the per-outcome bound `ε₂ n ≤ 1`. -/
theorem presampleAdvCompX₂_le_one {σ : State rT} {α : Loc} {N : Int}
    {bs : List { z : Int // 0 ≤ z ∧ z < N }}
    {ε₂ : { z : Int // 0 ≤ z ∧ z < N } → ENNReal} (Hbd : ∀ n, ε₂ n ≤ 1) (σ' : State rT) :
    presampleAdvCompX₂ σ α N bs ε₂ σ' ≤ 1 := by
  unfold presampleAdvCompX₂; split <;> first | exact Hbd _ | exact zero_le

/-- The presample integral of `presampleAdvCompX₂` is the `Ico`-average of `ε₂`, bounded by `HSum`.
The chain rewrites the integral against `tapePresample` into a finite average, step by step:
`tapePresample → tapeIndexUniform → Cfg.uniform → indicator-sum → (∑ ε₂)/N`. -/
theorem presampleAdvCompX₂_lintegral_le {σ₁ : State rT} {α : Loc} {N : Int}
    {bs : List { z : Int // 0 ≤ z ∧ z < N }}
    {ε₂ : { z : Int // 0 ≤ z ∧ z < N } → ENNReal} {ε₁ : ENNReal}
    (hlookup : σ₁.tapes[α]? = some ⟨N, bs⟩) (hN : 0 < N)
    (HSum : (∑ n ∈ (Finset.Ico 0 N).attach.image
              (fun ⟨z, hz⟩ => (⟨z, by rw [Finset.mem_Ico] at hz; exact hz⟩ :
                { z : Int // 0 ≤ z ∧ z < N })), ε₂ n) / N.toNat ≤ ε₁) :
    ∫⁻ σ', presampleAdvCompX₂ σ₁ α N bs ε₂ σ' ∂(tapePresample σ₁ α) ≤ ε₁ := by
  classical
  set F : Int → ℝ≥0∞ := fun z => if hz : 0 ≤ z ∧ z < N then ε₂ ⟨z, hz⟩ else 0 with hF
  have hNonempty : (Finset.Ico (0:Int) N).Nonempty := ⟨0, Finset.mem_Ico.mpr ⟨_root_.le_refl _, hN⟩⟩
  have hCard : (Finset.Ico (0:Int) N).card = N.toNat := by rw [Int.card_Ico, sub_zero]
  have hSumImage : (∑ n ∈ (Finset.Ico (0:Int) N).attach.image
        (fun x : { z : Int // z ∈ Finset.Ico (0:Int) N } =>
          (⟨x.1, Finset.mem_Ico.mp x.2⟩ : { z : Int // 0 ≤ z ∧ z < N })), ε₂ n)
      = ∑ z ∈ Finset.Ico (0:Int) N, F z := by
    rw [Finset.sum_image (by
          intro x _ y _ hxy
          apply Subtype.ext
          have h := congrArg Subtype.val hxy
          simpa using h), ← Finset.sum_attach (Finset.Ico (0:Int) N) F]
    exact Finset.sum_congr rfl fun a _ => by simp only [hF, dif_pos (Finset.mem_Ico.mp a.2)]
  calc ∫⁻ σ', presampleAdvCompX₂ σ₁ α N bs ε₂ σ' ∂(tapePresample σ₁ α)
      = ∫⁻ n : { z : Int // 0 ≤ z ∧ z < N }, ε₂ n ∂tapeIndexUniform N := by
        rw [tapePresample_lintegral hlookup _ (presampleAdvCompX₂.measurable σ₁ α N bs ε₂)]
        simp_rw [presampleAdvCompX₂_update]
    _ = ∑ z ∈ Finset.Ico (0:Int) N, F z / (N.toNat : ℝ≥0∞) := by
        have hf_eq : ∀ n : { z : Int // 0 ≤ z ∧ z < N },
            ε₂ n = (fun ρ : Cfg rT => match ρ.expr with | .lit (.int m) => F m | _ => 0)
              ⟨.lit (.int (↑n)), σ₁⟩ := fun n => by rw [hF]; simp only [dif_pos n.2]
        have hCfgUniform : Cfg.uniform N σ₁
            = (PMF.uniformOfFinset (Finset.Ico (0:Int) N) hNonempty).toMeasure.map
                (fun n : Int => (⟨.lit (.int n), σ₁⟩ : Cfg rT)) := by
          unfold Cfg.uniform; simp only [Int.isPos, dif_pos hN]
        have hIndic : (fun z : Int => (match (⟨.lit (.int z), σ₁⟩ : Cfg rT).expr with
              | .lit (.int m) => F m | _ => 0)) = ((Finset.Ico (0:Int) N) : Set Int).indicator F := by
          funext z
          by_cases hz : z ∈ Finset.Ico (0:Int) N
          · rw [Set.indicator_of_mem hz]
          · rw [Set.indicator_of_notMem hz]
            simp only [Finset.mem_Ico, not_and, _root_.not_lt] at hz
            show F z = 0
            simp only [hF]
            by_cases h0 : 0 ≤ z
            · rw [dif_neg]; exact fun ⟨_, h⟩ => (_root_.not_lt.mpr (hz h0)) h
            · rw [dif_neg]; exact fun ⟨h, _⟩ => h0 h
        simp_rw [hf_eq]
        rw [tapeIndexUniform_lintegral_eq_cfg_uniform hN σ₁
              (fun ρ => match ρ.expr with | .lit (.int m) => F m | _ => 0)
              ((measurable_litInt_elim F).comp Cfg.measurable_expr),
            hCfgUniform, MeasureTheory.lintegral_map
              (f := fun ρ : Cfg rT => match ρ.expr with | .lit (.int m) => F m | _ => 0)
              ((measurable_litInt_elim F).comp Cfg.measurable_expr) .of_discrete,
            hIndic, MeasureTheory.lintegral_indicator ((Finset.Ico (0:Int) N).measurableSet),
            MeasureTheory.lintegral_finset]
        refine Finset.sum_congr rfl fun z hz => ?_
        rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z),
            PMF.uniformOfFinset_apply, if_pos hz, hCard, ENNReal.div_eq_inv_mul, mul_comm]
    _ = (∑ z ∈ Finset.Ico (0:Int) N, F z) / (N.toNat : ℝ≥0∞) := by
        simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]
    _ ≤ ε₁ := by rw [← hSumImage]; exact HSum

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]

/-- **Advanced-composition presample rule** (Rocq `twp_presample_adv_comp`): presample tape
`α` of positive bound, spending per-outcome credit `↯(ε₂ n)` whose `Ico`-average is `≤ ε₁`. -/
theorem twp_presample_adv_comp {E : CoPset} {e : Exp rT} {α : Loc}
    {Φ : Val rT → IProp GF} {t : Tape} (hN : 0 < t.bound)
    {ε₁ : ENNReal}
    {ε₂ : { z : Int // 0 ≤ z ∧ z < t.bound } → ENNReal}
    (Hbd : ∀ n, ε₂ n ≤ 1)
    (HSum : (∑ n ∈ (Finset.Ico 0 t.bound).attach.image
              (fun ⟨z, hz⟩ => (⟨z, by
                rw [Finset.mem_Ico] at hz; exact hz⟩ :
                { z : Int // 0 ≤ z ∧ z < t.bound })),
              ε₂ n) / t.bound.toNat ≤ ε₁)
    (hv : e.toVal? = none) :
    iprop(↯ε₁ ∗ α ↪ₐ t ∗
      (∀ (n : { z : Int // 0 ≤ z ∧ z < t.bound }),
        ↯(ε₂ n) ∗
        α ↪ₐ ⟨t.bound, t.presamples ++ [n]⟩ -∗ tglWp E e Φ))
      ⊢@{IProp GF} tglWp E e Φ := by
  iintro ⟨Herr, Htape, Hcont⟩
  iapply (twp_lift_step_fupd_glm hv)
  iintro %σ₁ %ε_now ⟨Hσ, Hε_now⟩
  ihave %hlookup := app_state_lookup_tape (GF := GF) $$ Hσ Htape
  obtain ⟨N, bs⟩ := t
  simp only at hN hlookup Hbd ε₂ HSum
  ihave ⟨Hε_now, Herr, %hLe⟩ : iprop(ErisWpGS.errInterp (rT := rT) ε_now ∗ ↯ε₁ ∗ ⌜ε₁ ≤ ε_now⌝)
      $$ [Hε_now Herr]
  · iapply errInterp_supply_bound
    isplitl [Hε_now]; · iexact Hε_now
    iexact Herr
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset) with Hclose
  imodintro
  iapply glm'_erasable_step
  iexists (tapePresample σ₁ α),
    (fun σ' => ∃ n : { z : Int // 0 ≤ z ∧ z < N },
              σ' = σ₁.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)),
    0, (fun σ' => (ε_now - ε₁) + presampleAdvCompX₂ σ₁ α N bs ε₂ σ'),
    ((ε_now - ε₁) + 1)
  isplitr; · ipureintro; exact ErasableExpr.tapePresample hlookup hN
  isplitr; · ipureintro; exact presample_support_measurableSet
  isplitr; · ipureintro; intro σ'; simp only; gcongr; exact presampleAdvCompX₂_le_one Hbd σ'
  isplitr
  · ipureintro
    rw [zero_add]
    haveI : MeasureTheory.IsProbabilityMeasure (tapePresample σ₁ α) :=
      ⟨tapePresample_univ_eq_one hlookup hN⟩
    rw [MeasureTheory.lintegral_add_left measurable_const,
        MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]
    calc (ε_now - ε₁) + ∫⁻ σ', presampleAdvCompX₂ σ₁ α N bs ε₂ σ' ∂(tapePresample σ₁ α)
        ≤ (ε_now - ε₁) + ε₁ := by gcongr; exact presampleAdvCompX₂_lintegral_le hlookup hN HSum
      _ = ε_now := tsub_add_cancel_of_le hLe
  isplitr
  · ipureintro
    show (tapePresample σ₁ α) {σ' | ¬ _} ≤ 0
    refine _root_.le_of_eq ?_
    rw [← MeasureTheory.ae_iff]
    exact tapePresample_ae hlookup presample_support_measurableSet (fun n => ⟨n, rfl⟩)
  iintro %σ' %hR
  rcases hR with ⟨n, hσ'⟩
  subst hσ'
  imod Hclose with _
  imod (app_state_update_tape (GF := GF) (l := α) (t := ⟨N, bs⟩)
        (s := ⟨N, bs ++ [n]⟩)) $$ Hσ Htape with ⟨Hσ', Htape'⟩
  ihave HbupdDec : iprop(|==> ErisWpGS.errInterp (rT := rT) (ε_now - ε₁)) $$ [Hε_now Herr]
  · iapply errInterp_supply_decrease
    isplitl [Hε_now]; · iexact Hε_now
    iexact Herr
  imod HbupdDec with Hε_rem
  by_cases hlt : ε_now - ε₁ + ε₂ n < 1
  · ihave HbupdInc : iprop(|==> (ErisWpGS.errInterp (rT := rT) (ε_now - ε₁ + ε₂ n) ∗ ↯(ε₂ n))) $$ [Hε_rem]
    · iapply errInterp_supply_increase hlt
      iexact Hε_rem
    imod HbupdInc with ⟨Hε_new, Hε₂_cr⟩
    simp only [presampleAdvCompX₂_update]
    ihave Hwp := Hcont $$ %n [Hε₂_cr Htape']
    · isplitl [Hε₂_cr]; · iexact Hε₂_cr
      iexact Htape'
    ihave Hwp' := (BI.equiv_iff.mp (tglWp_unfold_step hv)).1 $$ Hwp
    ihave HwpBody := Hwp' $$ %_ %(ε_now - ε₁ + ε₂ n) [Hσ' Hε_new]
    · isplitl [Hσ']; · iexact Hσ'
      iexact Hε_new
    imod HwpBody with HGlm
    imodintro
    iapply execStutter_free
    simp only [ExtTreeMap.insert_eq_PartialMap_insert]
    iexact HGlm
  · push Not at hlt
    simp only [presampleAdvCompX₂_update]
    imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset) with _
    imodintro
    iapply execStutter_spend hlt

/-- Basic total presample rule: append a freshly sampled `n` to tape `α`, spending no credit.
The `ε₂ := 0` instance of `twp_presample_adv_comp`. -/
theorem twp_presample {E : CoPset} {e : Exp rT} {α : Loc} {Φ : Val rT → IProp GF}
    {t : Tape} (hN : 0 < t.bound) (hv : e.toVal? = none) :
    iprop(α ↪ₐ t ∗
      (∀ (n : { z : Int // 0 ≤ z ∧ z < t.bound }),
        α ↪ₐ ⟨t.bound, t.presamples ++ [n]⟩ -∗ tglWp E e Φ))
      ⊢@{IProp GF} tglWp E e Φ := by
  iintro ⟨Htape, Hcont⟩
  iapply fupd_tglWp
  imod ErrorCredit.zero with Herr
  imodintro
  iapply (twp_presample_adv_comp hN (ε₁ := 0) (ε₂ := fun _ => 0) (fun _ => zero_le) (by simp) hv)
  isplitl [Herr]; · iexact Herr
  isplitl [Htape]; · iexact Htape
  iintro %n ⟨_, Htape'⟩
  iapply Hcont $$ %n
  iexact Htape'

end TotalEris
end ProbLang
