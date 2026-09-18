module

public import Metrology.Approxis.Lifting
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Approxis.PrimitiveLaws
public import Metrology.ProbLang.Metatheory

@[expose] public section

set_option linter.discrete false


/-!
# Coupling Rules

Coupling rules used by Compatibility/Fundamental/Soundness.
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS
open scoped AppGS

namespace ProbLang


variable {rT : Type _} [ProbLang.ProbLangℝ rT]

/-! ## Timeless instances for tape predicates -/

section TimelessTapes
open scoped AppGS

variable {GF : BundledGFunctors}

instance heapView_tape_frag_discreteE (l : Loc) (t : Tape) :
    OFE.DiscreteE (HeapView.Frag (H := LocHeap) l (.own 1) (toAgree t)) :=
  View.frag_discrete

instance appTapesFrag_timeless [MeasurableSingletonClass rT] [AppGS rT GF] (l : Loc)
    (t : Tape) :
    BI.Timeless (iprop(l ↪ₐ t) : IProp GF) := iOwn_timeless

instance specTapesFrag_timeless [MeasurableSingletonClass rT] [ISpec : SpecGS rT GF]
    (l : Loc) (t : Tape) :
    BI.Timeless (l ↪ₛ t : IProp GF) := iOwn_timeless

instance heapView_heap_frag_discreteE (l : Loc) (v : Val rT) :
    OFE.DiscreteE (HeapView.Frag (H := LocHeap) l (.own 1) (toAgree v)) := by
  unfold HeapView.Frag
  exact View.frag_discrete

instance appHeapFrag_timeless [MeasurableSingletonClass rT] [IApp : AppGS rT GF]
    (l : Loc) (v : Val rT) :
    BI.Timeless (iprop(l ↦ v) : IProp GF) := by
  unfold appHeapFrag
  exact iOwn_timeless

instance specHeapFrag_timeless [MeasurableSingletonClass rT] [ISpec : SpecGS rT GF]
    (l : Loc) (v : Val rT) :
    BI.Timeless (iprop(l ↦ₛ v) : IProp GF) := by
  unfold specHeapFrag
  exact iOwn_timeless

instance appNatTape_timeless [MeasurableSingletonClass rT] [IApp : AppGS rT GF]
    (l : Loc) (z : Int) (ns : List Int) :
    BI.Timeless (appNatTape l z ns : IProp GF) := by
  unfold appNatTape
  infer_instance

instance specNatTape_timeless [MeasurableSingletonClass rT] [ISpec : SpecGS rT GF]
    (l : Loc) (z : Int) (ns : List Int) :
    BI.Timeless (specNatTape l z ns : IProp GF) := by
  unfold specNatTape
  infer_instance

/-- Strip `▷` from a Timeless hypothesis when the continuation is in `fupd`
position. Mirrors Rocq's `iMod ">Hα"` automation. -/
theorem later_timeless_fupd {PROP : Type _} [BI PROP] [BIUpdate PROP] [BIFUpdate PROP]
    {P : PROP} [BI.Timeless P] {E₁ E₂ : CoPset} {Q : PROP} :
    (iprop(▷ P) ∗ (P -∗ |={E₁, E₂}=> Q)) ⊢ (iprop(|={E₁, E₂}=> Q) : PROP) := by
  refine BIBase.Entails.trans ?_ IsExcept0.is_except0
  refine BI.sep_mono_left BI.Timeless.timeless |>.trans ?_
  refine BIBase.Entails.trans ?_ (BI.except0_mono (BI.wand_elim_right (P := P) (Q := iprop(|={E₁,E₂}=> Q))))
  refine BIBase.Entails.trans ?_ BI.except0_sep.2
  exact BI.sep_mono_right BI.except0_intro

end TimelessTapes

/-! ## Core probability fact: uniform coupling under bijection -/

/-- Uniform-measure coupling under a bijection on the support: for `f` that
restricts to a bijection on `Ico 0 z`, `Cfg.uniform z σ` and `Cfg.uniform z σ'`
are exactly coupled along `{(⟨#n, σ⟩, ⟨#(f n), σ'⟩) | n ∈ Ico 0 z}`. -/
theorem Cfg.uniform_addCoupl_bij [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    (σ σ' : State rT)
    (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m) :
    AddCoupl 0
      {p : Cfg rT × Cfg rT | ∃ n : Int, 0 ≤ n ∧ n < z ∧
        p.1 = ⟨pl(#(.int n)), σ⟩ ∧ p.2 = ⟨pl(#(.int (f n))), σ'⟩}
      (Cfg.uniform z σ) (Cfg.uniform z σ') := by
  classical
  rintro ⟨φ, Hφm, Hφb⟩ ⟨ψ, Hψm, Hψb⟩ Hle
  simp only [add_zero]
  show ∫⁻ c, φ c ∂(Cfg.uniform z σ) ≤ ∫⁻ c, ψ c ∂(Cfg.uniform z σ')
  rw [Cfg.lintegral_uniform' Hz σ Hφm, Cfg.lintegral_uniform' Hz σ' Hψm]
  refine mul_le_mul_right ?_ _
  rw [← Finset.sum_Ico_comp_of_bijOn hdom hbij (fun m => ψ (⟨pl(#(.int m)), σ'⟩ : Cfg rT))]
  refine Finset.sum_le_sum fun n hn => ?_
  simp only [Finset.mem_Ico] at hn
  exact Hle ⟨n, hn.1, hn.2, rfl, rfl⟩

/-- `primStep` of `rand #z ()` (unlabeled) equals `Cfg.uniform z σ`. -/
theorem primStep_rand_unit [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    (σ : State rT) :
    primStep (⟨pl(rand(#(.int z), #(.unit))), σ⟩ : Cfg rT) = Cfg.uniform z σ := by
  have Hhead : 0 < headStep ⟨pl(rand(#(.int z), #(.unit))), σ⟩
        ({⟨pl(#(.int 0)), σ⟩} : Set (Cfg rT)) :=
    HeadStepSupport.pos (.RandNoTapeS Hz (_root_.le_refl _) Hz)
  rw [primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible (by is_lc) (fun hz => by rw [hz] at Hhead; simp at Hhead))]
  rfl

/-- `primStep` of `rand #z (lbl α)` when the tape has the wrong bound. -/
theorem primStep_rand_lbl_wrong [MeasurableSingletonClass rT] {z M : Int}
    (Hz : 0 < z) (HneM : z ≠ M)
    (σ : State rT) (l : Loc) (fs : List { z' : Int // 0 ≤ z' ∧ z' < M })
    (Hlk : σ.tapes[l]? = some ⟨M, fs⟩) :
    primStep (⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ : Cfg rT) = Cfg.uniform z σ := by
  have Hhead : 0 < headStep ⟨pl(rand(#(.int z), #(.lbl l))), σ⟩
        ({⟨pl(#(.int 0)), σ⟩} : Set (Cfg rT)) :=
    HeadStepSupport.pos
      (.RandTapeOtherS Hz Hlk HneM (_root_.le_refl _) Hz rfl)
  rw [primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible (by is_lc) (fun hz => by rw [hz] at Hhead; simp at Hhead))]
  show (match σ.tapes[l]? with
        | none => (0 : MeasureTheory.Measure (Cfg rT))
        | some ⟨M, ns⟩ =>
          if M = z then
            match ns with
            | [] => Cfg.uniform z σ
            | n :: ns => MeasureTheory.Measure.dirac ⟨.lit <| .int n,
                σ.update_tapes fun t => t.insert l ⟨M, ns⟩⟩
          else Cfg.uniform z σ) = Cfg.uniform z σ
  rw [Hlk]
  simp only [if_neg (Ne.symm HneM)]

/-- `primStep` of `rand #z (lbl α)` when the tape has the correct bound and is empty. -/
theorem primStep_rand_lbl_empty [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    (σ : State rT) (l : Loc)
    (Hlk : σ.tapes[l]? = some ⟨z, []⟩) :
    primStep (⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ : Cfg rT) = Cfg.uniform z σ := by
  have Hhead : 0 < headStep ⟨pl(rand(#(.int z), #(.lbl l))), σ⟩
        ({⟨pl(#(.int 0)), σ⟩} : Set (Cfg rT)) :=
    HeadStepSupport.pos
      (.RandTapeEmptyS Hz Hlk rfl (_root_.le_refl _) Hz rfl)
  rw [primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible (by is_lc) (fun hz => by rw [hz] at Hhead; simp at Hhead))]
  show (match σ.tapes[l]? with
        | none => (0 : MeasureTheory.Measure (Cfg rT))
        | some ⟨M, ns⟩ =>
          if M = z then
            match ns with
            | [] => Cfg.uniform z σ
            | n :: ns => MeasureTheory.Measure.dirac ⟨.lit <| .int n,
                σ.update_tapes fun t => t.insert l ⟨M, ns⟩⟩
          else Cfg.uniform z σ) = Cfg.uniform z σ
  rw [Hlk]
  simp only [↓reduceIte]

/-! ## Coupling-context helpers -/

open MeasureTheory in
/-- Lift a coupling between `μ` and `primStep ⟨e, σ⟩` to one between `μ` and
`primStep ⟨K.fill e, σ⟩` via `λ a (e', σ'). ∃ e'', e' = K.fill e'' ∧ R a (e'', σ')`. -/
theorem AddCoupl_steps_ctx_bind_r [MeasurableSingletonClass rT] {α}
    [MeasurableSpace α]
    {μ : Measure α} {e : Exp rT} {σ : State rT} {R : Set (α × Cfg rT)} {ε : ENNReal}
    {K : Ectx rT} (hv : ¬ e.isValue)
    (Hcpl : AddCoupl ε R μ (primStep ⟨e, σ⟩)) :
    AddCoupl ε
      {p : α × Cfg rT | ∃ e'', p.2.expr = K.fill e'' ∧ R (p.1, ⟨e'', p.2.state⟩)}
      μ (primStep ⟨K.fill e, σ⟩) := by
  rw [primStep_fill (K := K) hv]
  rw [show μ = μ.map id from (MeasureTheory.Measure.map_id).symm]
  refine AddCoupl.map (f := id) (g := K.fillCfg)
    measurable_id (Ectx.fillCfg.measurable K)
    (R := {p : α × Cfg rT | ∃ e'', p.2.expr = K.fill e'' ∧ R (p.1, ⟨e'', p.2.state⟩)}) ?_ Hcpl
  intro a ⟨e', σ'⟩ HR
  refine ⟨e', rfl, ?_⟩
  exact HR

open MeasureTheory in
/-- Variant of `AddCoupl_steps_ctx_bind_r` where the relation only depends on
the expression of the second component. -/
theorem AddCoupl_steps_ctx_bind_r_no_state [MeasurableSingletonClass rT]
    {μ : Measure (Cfg rT)} {e : Exp rT} {σ : State rT} {R : Exp rT → Exp rT → Prop} {ε : ENNReal}
    {K : Ectx rT} (hv : ¬ e.isValue)
    (Hcpl : AddCoupl ε {p : Cfg rT × Cfg rT | R p.1.expr p.2.expr} μ (primStep ⟨e, σ⟩)) :
    AddCoupl ε
      {p : Cfg rT × Cfg rT | ∃ e'', p.2.expr = K.fill e'' ∧ R p.1.expr e''}
      μ (primStep ⟨K.fill e, σ⟩) := by
  rw [primStep_fill (K := K) hv]
  rw [show μ = μ.map id from (MeasureTheory.Measure.map_id).symm]
  refine AddCoupl.map (f := id) (g := K.fillCfg)
    measurable_id (Ectx.fillCfg.measurable K)
    (R := {p : Cfg rT × Cfg rT | ∃ e'', p.2.expr = K.fill e'' ∧ R p.1.expr e''}) ?_ Hcpl
  intro a b HR
  refine ⟨b.expr, rfl, ?_⟩
  exact HR

section CouplingRules

variable {hlc : HasLC} {GF : BundledGFunctors}
    [MeasurableSingletonClass rT] [ApproxisGS rT hlc GF]

/-- Same-bound bijective coupling: `f : Int → Int` restricts to a bijection on
`[0, z)`. -/
theorem wp_couple_rand_rand (z : Int) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) :
    iprop((⤇ K.fill (pl(rand(#(.int z), #(.unit))))) ∗
        (∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗
          (⤇ K.fill (pl(#(.int (f n))))) -∗
          Φ (.int n : Val rT)))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.unit)))) Φ := by
  iintro ⟨Hj, Hcnt⟩
  have Hv : (pl(rand(#(.int z), #(.unit))) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_prim_steps_coupl Hv)
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  have HheadL : 0 < headStep ⟨pl(rand(#(.int z), #(.unit))), σ₁⟩
        {⟨pl(#(.int 0)), σ₁⟩} :=
    HeadStepSupport.pos (.RandNoTapeS Hz (_root_.le_refl _) Hz)
  have HredL : Discrete.Reducible (pl(rand(#(.int z), #(.unit)))) σ₁ :=
    Reducible.toDiscrete (by no_urand) (reducible_of_headReducible (by is_lc) (fun hz => by rw [hz] at HheadL; simp at HheadL))
  have HheadR : 0 < headStep ⟨pl(rand(#(.int z), #(.unit))), σ₁'⟩
        {⟨pl(#(.int 0)), σ₁'⟩} :=
    HeadStepSupport.pos (.RandNoTapeS Hz (_root_.le_refl _) Hz)
  have HredR_rand : Discrete.Reducible (pl(rand(#(.int z), #(.unit)))) σ₁' :=
    Reducible.toDiscrete (by no_urand) (reducible_of_headReducible (by is_lc) (fun hz => by rw [hz] at HheadR; simp at HheadR))
  have HredR : Discrete.Reducible (K.fill (pl(rand(#(.int z), #(.unit))))) σ₁' :=
    Reducible.toDiscrete (by no_urand) (HredR_rand.toReducible.fill K)
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  let R : Cfg rT → Cfg rT → Prop := fun c₁ c₂ =>
    ∃ n : Int, 0 ≤ n ∧ n < z ∧
      c₁ = ⟨pl(#(.int n)), σ₁⟩ ∧ c₂ = ⟨K.fill (pl(#(.int (f n)))), σ₁'⟩
  iexists R, 0, ε
  isplitr; · ipureintro; rw [zero_add]
  isplitr; · ipureintro; exact HredL.toReducible
  isplitr; · ipureintro; exact HredR.toReducible
  isplitr
  · ipureintro
    rw [primStep_rand_unit Hz]
    have Hv_rand : ¬ (pl(rand(#(.int z), #(.unit))) : Exp rT).isValue := by
      intro ⟨w⟩; nomatch w
    rw [primStep_fill Hv_rand, primStep_rand_unit Hz]
    have Hbase := Cfg.uniform_addCoupl_bij Hz σ₁ σ₁' f hdom hbij
    have : AddCoupl 0
        {p : Cfg rT × Cfg rT | R p.1 p.2}
        ((Cfg.uniform z σ₁).map id)
        ((Cfg.uniform z σ₁').map (fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT))) := by
      refine AddCoupl.map (f := id) (g := K.fillCfg)
        measurable_id (Ectx.fillCfg.measurable K)
        (R := {p : Cfg rT × Cfg rT | R p.1 p.2})
        ?_
        Hbase
      intro a b hab
      obtain ⟨n, h0, hz, heqL, heqR⟩ := hab
      refine ⟨n, h0, hz, heqL, ?_⟩
      subst heqR
      rfl
    rw [MeasureTheory.Measure.map_id] at this
    exact this
  iintro %e₂ %σ₂ %e₂' %σ₂' %HR
  obtain ⟨n, hn0, hnz, heq1, heq2⟩ := HR
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq2
  imodintro
  iintro !>
  ihave HUpd := specProg_update (GF := GF)
    (e3 := K.fill (pl(#(.int (f n))))) $$ Hs Hj
  imod HUpd with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  isplitl [Hσ]; · iexact Hσ
  isplitl [Hs']; · iexact Hs'
  isplitl [Hε]; · iexact Hε
  iapply (wp_value_of_toVal (v := (.int n : Val rT)) rfl)
  iapply Hcnt
  · ipureintro; exact ⟨hn0, hnz⟩
  · iexact Hj'

/-- **Adversarial same-bound coupling.** Both sides draw from `[0, z)` and `f`
links the draws; the caller spends the amortized credit `ε₁` up front and the
continuation is handed the per-draw credit `ε₂ n`. -/
theorem wp_couple_rand_rand_adv (z : Int) (f : Int → Int) (ε₁ : ENNReal) (ε₂ : Int → ENNReal)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z)
    (hamort : (∑ n ∈ Finset.Ico (0 : Int) z, ε₂ n) / (z.toNat : ENNReal) ≤ ε₁)
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) :
    iprop((⤇ K.fill (pl(rand(#(.int z), #(.unit))))) ∗ ↯ ε₁ ∗
        (∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗ ↯ (ε₂ n) -∗
          (⤇ K.fill (pl(#(.int (f n))))) -∗ Φ (.int n : Val rT)))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.unit)))) Φ := by
  classical
  iintro ⟨Hj, Herr, Hcnt⟩
  have Hv : (pl(rand(#(.int z), #(.unit))) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  have Hv_rand : ¬ (pl(rand(#(.int z), #(.unit))) : Exp rT).isValue := fun ⟨w⟩ => nomatch w
  iapply (wp_lift_prim_steps_coupl_adv_err_le_1 Hv)
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  have HheadL : 0 < headStep ⟨pl(rand(#(.int z), #(.unit))), σ₁⟩
        {⟨pl(#(.int 0)), σ₁⟩} :=
    HeadStepSupport.pos (.RandNoTapeS Hz (_root_.le_refl _) Hz)
  have HredL : Discrete.Reducible (pl(rand(#(.int z), #(.unit)))) σ₁ :=
    Reducible.toDiscrete (by no_urand)
      (reducible_of_headReducible (by is_lc) (fun hz => by rw [hz] at HheadL; simp at HheadL))
  have HheadR : 0 < headStep ⟨pl(rand(#(.int z), #(.unit))), σ₁'⟩
        {⟨pl(#(.int 0)), σ₁'⟩} :=
    HeadStepSupport.pos (.RandNoTapeS Hz (_root_.le_refl _) Hz)
  have HredR : Discrete.Reducible (K.fill (pl(rand(#(.int z), #(.unit))))) σ₁' :=
    Reducible.toDiscrete (by no_urand)
      ((Reducible.toDiscrete (by no_urand)
        (reducible_of_headReducible (by is_lc)
          (fun hz => by rw [hz] at HheadR; simp at HheadR))).toReducible.fill K)
  set P : Cfg rT → Cfg rT → Int → Prop := fun ρ₁ ρ₂ n =>
    (0 ≤ n ∧ n < z) ∧ ρ₁ = (⟨pl(#(.int n)), σ₁⟩ : Cfg rT) ∧
      ρ₂ = (⟨K.fill pl(#(.int (f n))), σ₁'⟩ : Cfg rT) with hP
  set X : Cfg rT → Cfg rT → ENNReal :=
    fun ρ₁ ρ₂ => 1 ⊓ ⨅ n, ⨅ (_ : P ρ₁ ρ₂ n), ε₂ n with hX
  have hXle1 : ∀ ρ₁ ρ₂, X ρ₁ ρ₂ ≤ 1 := fun _ _ => inf_le_left
  have hXgraph : ∀ n : Int, 0 ≤ n → n < z →
      X ⟨pl(#(.int n)), σ₁⟩ ⟨K.fill pl(#(.int (f n))), σ₁'⟩ = 1 ⊓ ε₂ n := by
    intro n h0 hn
    refine _root_.le_antisymm (inf_le_inf_left _ (iInf₂_le n ⟨⟨h0, hn⟩, rfl, rfl⟩))
      (le_inf inf_le_left (le_iInf₂ fun n' hn' => ?_))
    obtain ⟨-, h1, -⟩ := hn'
    obtain ⟨he, -⟩ := (Cfg.mk.injEq ..).mp h1
    simp only [Exp.lit.injEq, BaseLit.int.injEq] at he
    subst he
    exact inf_le_right
  have hXoff : ∀ ρ₁ ρ₂, (¬ ∃ n, P ρ₁ ρ₂ n) → X ρ₁ ρ₂ = 1 := fun ρ₁ ρ₂ h =>
    _root_.le_antisymm inf_le_left (le_inf le_rfl (le_iInf₂ fun n hn => absurd ⟨n, hn⟩ h))
  have Hkant : ∀ h₁ h₂ : Cfg rT → ENNReal, Measurable h₁ → Measurable h₂ →
      (∀ a, h₁ a ≤ 1) → (∀ b, h₂ b ≤ 1) → (∀ a b, h₁ a ≤ h₂ b + X a b) →
      (∫⁻ a, h₁ a ∂(primStep (⟨pl(rand(#(.int z), #(.unit))), σ₁⟩ : Cfg rT))) ≤
        (∫⁻ b, h₂ b ∂(primStep (⟨K.fill pl(rand(#(.int z), #(.unit))), σ₁'⟩ : Cfg rT))) + ε₁ := by
    intro h₁ h₂ hm₁ hm₂ _ _ hle
    have hR : (∫⁻ b, h₂ b ∂(primStep (⟨K.fill pl(rand(#(.int z), #(.unit))), σ₁'⟩ : Cfg rT)))
        = ((z.toNat : ENNReal))⁻¹ *
            ∑ m ∈ Finset.Ico (0 : Int) z, h₂ (⟨K.fill pl(#(.int m)), σ₁'⟩ : Cfg rT) := by
      rw [primStep_fill Hv_rand, primStep_rand_unit Hz,
        MeasureTheory.lintegral_map hm₂
          (g := fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT))
          (Ectx.fillCfg.measurable K),
        Cfg.lintegral_uniform' Hz σ₁'
          (φ := fun a : Cfg rT => h₂ ⟨K.fill a.expr, a.state⟩)
          (hm₂.comp (Ectx.fillCfg.measurable K))]
    rw [primStep_rand_unit Hz, Cfg.lintegral_uniform' Hz σ₁ hm₁, hR,
      ← Finset.sum_Ico_comp_of_bijOn hdom hbij
        (fun m => h₂ (⟨K.fill pl(#(.int m)), σ₁'⟩ : Cfg rT))]
    have hstep : ∑ n ∈ Finset.Ico (0 : Int) z, h₁ (⟨pl(#(.int n)), σ₁⟩ : Cfg rT) ≤
        (∑ n ∈ Finset.Ico (0 : Int) z, h₂ (⟨K.fill pl(#(.int (f n))), σ₁'⟩ : Cfg rT)) +
          ∑ n ∈ Finset.Ico (0 : Int) z, ε₂ n := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun n hn => ?_
      simp only [Finset.mem_Ico] at hn
      refine (hle _ (⟨K.fill pl(#(.int (f n))), σ₁'⟩ : Cfg rT)).trans ?_
      gcongr
      rw [hXgraph n hn.1 hn.2]
      exact inf_le_right
    calc ((z.toNat : ENNReal))⁻¹ * ∑ n ∈ Finset.Ico (0 : Int) z, h₁ (⟨pl(#(.int n)), σ₁⟩ : Cfg rT)
        ≤ ((z.toNat : ENNReal))⁻¹ *
            ((∑ n ∈ Finset.Ico (0 : Int) z, h₂ (⟨K.fill pl(#(.int (f n))), σ₁'⟩ : Cfg rT)) +
              ∑ n ∈ Finset.Ico (0 : Int) z, ε₂ n) := by gcongr
      _ = ((z.toNat : ENNReal))⁻¹ *
            (∑ n ∈ Finset.Ico (0 : Int) z, h₂ (⟨K.fill pl(#(.int (f n))), σ₁'⟩ : Cfg rT)) +
          ((z.toNat : ENNReal))⁻¹ * ∑ n ∈ Finset.Ico (0 : Int) z, ε₂ n := mul_add ..
      _ ≤ _ := by
          gcongr
          rwa [← ENNReal.div_eq_inv_mul]
  ihave %Hεle := ErrorCredit.supply_bound (GF := GF) $$ Hε Herr
  ihave Hdec := ErrorCredit.supply_decrease (GF := GF) $$ Hε Herr
  imod Hdec
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset) with Hclose
  imodintro
  iexists X, ε₁, (ε - ε₁)
  isplitr; · ipureintro; exact _root_.le_of_eq (add_tsub_cancel_of_le Hεle)
  isplitr; · ipureintro; exact HredL.toReducible
  isplitr; · ipureintro; exact HredR.toReducible
  isplitr; · ipureintro; exact hXle1
  isplitr; · ipureintro; exact Hkant
  iintro %e₂ %σ₂ %e₂' %σ₂'
  iintro !>
  by_cases hg : ∃ n : Int, P ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ n
  · obtain ⟨n, ⟨hn0, hnz⟩, h1, h2⟩ := hg
    obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp h1
    obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp h2
    rw [hXgraph n hn0 hnz]
    by_cases hbig : (1 : ENNReal) ≤ (1 ⊓ ε₂ n) + (ε - ε₁)
    · imod Hclose
      imodintro
      ileft
      ipureintro
      exact hbig
    · rw [_root_.not_le] at hbig
      have hinf : (1 : ENNReal) ⊓ ε₂ n < 1 := _root_.lt_of_le_of_lt le_self_add hbig
      have hlt : ε₂ n < 1 := by
        by_contra hge
        exact absurd (inf_eq_left.mpr (_root_.not_lt.mp hge)) hinf.ne
      rw [inf_eq_right.mpr hlt.le]
      have hsum : (ε - ε₁) + ε₂ n < 1 := by
        rw [inf_eq_right.mpr hlt.le] at hbig
        rwa [add_comm]
      ihave HUpd := specProg_update (GF := GF)
        (e3 := K.fill (pl(#(.int (f n))))) $$ Hs Hj
      imod HUpd with ⟨Hs', Hj'⟩
      ihave Hinc := ErrorCredit.supply_increase (GF := GF) (ε₂ := ε₂ n) hsum $$ Hdec
      imod Hinc with ⟨HdecA, Hfrag⟩
      imod Hclose
      imodintro
      iright
      isplitl [Hσ]; · iexact Hσ
      isplitl [Hs']; · iexact Hs'
      isplitl [HdecA]
      · iapply ErrorCredit.extAuth (add_comm _ _)
        iexact HdecA
      iapply (wp_value_of_toVal (v := (.int n : Val rT)) rfl)
      ispecialize Hcnt $$ %n %⟨hn0, hnz⟩ Hfrag Hj'
      iexact Hcnt
  · imod Hclose
    imodintro
    ileft
    ipureintro
    rw [hXoff _ _ hg]
    exact le_self_add

/-- Avoidance: both sides draw the same value from `[0, z)`, and the caller pays
`1/z` to learn that the value is not `bad`. -/
theorem wp_couple_rand_rand_avoid (z bad : Int) (Hz : 0 < z) (K : Ectx rT) (E : CoPset)
    (Φ : Val rT → IProp GF) :
    iprop((⤇ K.fill (pl(rand(#(.int z), #(.unit))))) ∗ ↯ ((z.toNat : ENNReal))⁻¹ ∗
        (∀ (n : Int), (⌜(0 ≤ n ∧ n < z) ∧ n ≠ bad⌝) -∗
          (⤇ K.fill (pl(#(.int n)))) -∗ Φ (.int n : Val rT)))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.unit)))) Φ := by
  classical
  iintro ⟨Hj, Herr, Hcnt⟩
  have hamort : (∑ n ∈ Finset.Ico (0 : Int) z, if n = bad then (1 : ENNReal) else 0)
      / (z.toNat : ENNReal) ≤ ((z.toNat : ENNReal))⁻¹ := by
    rw [← one_div]
    gcongr
    rw [Finset.sum_ite_eq' (Finset.Ico (0 : Int) z) bad (fun _ => (1 : ENNReal))]
    split <;> simp
  iapply (wp_couple_rand_rand_adv z id ((z.toNat : ENNReal))⁻¹
    (fun n => if n = bad then 1 else 0) (fun _ h1 h2 => ⟨h1, h2⟩)
    (fun m h1 h2 => ⟨m, ⟨⟨h1, h2⟩, rfl⟩, fun _ hn' => hn'.2⟩) Hz hamort K E Φ)
  isplitl [Hj]; · iexact Hj
  isplitl [Herr]; · iexact Herr
  iintro %n %hn Hec Hj'
  by_cases hb : n = bad
  · rw [if_pos hb]
    iexfalso
    iapply ErrorCredit.contradict (_root_.le_refl 1) $$ Hec
  · simp only [id_eq]
    iapply Hcnt
    · ipureintro; exact ⟨hn, hb⟩
    · iexact Hj'

/-- `wp_couple_tapes_bij`: presample both tapes in lockstep along a bijection
`f` on `[0, z)`. No program step and no error. -/
theorem wp_couple_tapes_bij {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    {z : Int} {α αₛ : Loc} {ns nsₛ : List Int} (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) :
    iprop(appNatTape α z ns ∗ specNatTape αₛ z nsₛ ∗
        (∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗ appNatTape α z (ns ++ [n]) -∗
          specNatTape αₛ z (nsₛ ++ [f n]) -∗ wp E e Φ))
      ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨Hα, Hαₛ, Hcnt⟩
  unfold appNatTape specNatTape
  icases Hα with ⟨%fs, %Hfs, Hα⟩
  icases Hαₛ with ⟨%fsₛ, %Hfsₛ, Hαₛ⟩
  iapply wp_couple_erasables
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  ihave %hlk := app_state_lookup_tape (GF := GF) (σ := σ₁) $$ Hσ Hα
  ihave %hlk' := spec_auth_lookup_tape (GF := GF) (σ := σ₁') $$ Hs Hαₛ
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset) with Hclose
  imodintro
  iexists (fun σ₂ σ₂' => ∃ n : Int, 0 ≤ n ∧ n < z ∧
      σ₂ = σ₁.update_tapes (·.insert α ⟨z, fs ++ [tapeIdxOf Hz n]⟩) ∧
      σ₂' = σ₁'.update_tapes (·.insert αₛ ⟨z, fsₛ ++ [tapeIdxOf Hz (f n)]⟩)),
    tapePresample σ₁ α, tapePresample σ₁' αₛ
  isplitr; · ipureintro; exact ErasableExpr.tapePresample hlk Hz
  isplitr; · ipureintro; exact ErasableExpr.tapePresample hlk' Hz
  isplitr; · ipureintro; exact tapePresample_addCoupl_bij hlk hlk' Hz f hdom hbij
  iintro %σ₂ %σ₂' %HR
  obtain ⟨n, hn0, hnz, rfl, rfl⟩ := HR
  ihave HU := app_state_update_tape (GF := GF) (σ := σ₁)
    (s := ⟨z, fs ++ [tapeIdxOf Hz n]⟩) $$ Hσ Hα
  imod HU with ⟨Hσ', Hα'⟩
  ihave HU' := spec_auth_update_tape (GF := GF) (σ := σ₁')
    (s := ⟨z, fsₛ ++ [tapeIdxOf Hz (f n)]⟩) $$ Hs Hαₛ
  imod HU' with ⟨Hs', Hαₛ'⟩
  imod Hclose
  imodintro
  simp only [approxisWpGS_stateInterp_eq, approxisWpGS_specInterp_eq,
    ExtTreeMap.insert_eq_PartialMap_insert]
  isplitl [Hσ']; · iexact Hσ'
  isplitl [Hs']; · iexact Hs'
  isplitl [Hε]; · iexact Hε
  ihave HnatA : iprop(∃ gs : List { z' : Int // 0 ≤ z' ∧ z' < z },
      (⌜gs.map (fun x => x.val) = ns ++ [n]⌝) ∗ α ↪ₐ ⟨z, gs⟩) $$ [Hα']
  · iexists (fs ++ [tapeIdxOf Hz n])
    isplitr
    · ipureintro; simp [← Hfs, tapeIdxOf_val Hz hn0 hnz]
    · iexact Hα'
  ihave HnatS : iprop(∃ gs : List { z' : Int // 0 ≤ z' ∧ z' < z },
      (⌜gs.map (fun x => x.val) = nsₛ ++ [f n]⌝) ∗ αₛ ↪ₛ ⟨z, gs⟩) $$ [Hαₛ']
  · iexists (fsₛ ++ [tapeIdxOf Hz (f n)])
    isplitr
    · ipureintro
      have hd := hdom n hn0 hnz
      simp [← Hfsₛ, tapeIdxOf_val Hz hd.1 hd.2]
    · iexact Hαₛ'
  ispecialize Hcnt $$ %n %⟨hn0, hnz⟩ HnatA HnatS
  iexact Hcnt

/-- Labeled-rand coupling where both tapes have the wrong bound `M ≠ z`.
Both tapes are unchanged; the draw is uniform and `f` links the values. -/
theorem wp_couple_rand_lbl_rand_lbl_wrong (z M : Int) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (HneM : z ≠ M) (K : Ectx rT) (E : CoPset) (α α' : Loc)
    (xs ys : List Int) (Φ : Val rT → IProp GF) :
    iprop(▷ appNatTape α M xs ∗ ▷ specNatTape α' M ys ∗
        (⤇ K.fill (pl(rand(#(.int z), #(.lbl α'))))) ∗
        (∀ (n : Int),
          appNatTape α M xs ∗ specNatTape α' M ys ∗
            (⤇ K.fill (pl(#(.int (f n))))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗
          Φ (.int n : Val rT)))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.lbl α)))) Φ := by
  iintro ⟨Hα, Hα', Hj, Hcnt⟩
  have Hv : (pl(rand(#(.int z), #(.lbl α))) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_prim_steps_coupl Hv)
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  iapply (later_timeless_fupd (P := appNatTape α M xs))
  isplitl [Hα]; · iexact Hα
  iintro Hα
  iapply (later_timeless_fupd (P := specNatTape α' M ys))
  isplitl [Hα']; · iexact Hα'
  iintro Hα'
  ihave HαEx := show appNatTape α M xs ⊢@{IProp GF}
      iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < M },
        (⌜fs.map (fun x => x.val) = xs⌝) ∗ α ↪ₐ ⟨M, fs⟩) from
    BI.BIBase.Entails.rfl $$ Hα
  icases HαEx with ⟨%fs, %hmap_fs, Hα_b⟩
  ihave Hα'Ex := show specNatTape α' M ys ⊢@{IProp GF}
      iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < M },
        (⌜fs.map (fun x => x.val) = ys⌝) ∗ α' ↪ₛ ⟨M, fs⟩) from
    BI.BIBase.Entails.rfl $$ Hα'
  icases Hα'Ex with ⟨%fs', %hmap_fs', Hα'_b⟩
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  ihave %Hlk_α := app_state_lookup_tape (GF := GF) (σ := σ₁) $$ Hσ Hα_b
  ihave %Hlk_α' := spec_auth_lookup_tape (GF := GF) (σ := σ₁') $$ Hs Hα'_b
  have HheadL : 0 < headStep ⟨pl(rand(#(.int z), #(.lbl α))), σ₁⟩
        {⟨pl(#(.int 0)), σ₁⟩} :=
    HeadStepSupport.pos
      (.RandTapeOtherS Hz Hlk_α HneM (_root_.le_refl _) Hz rfl)
  have HredL : Discrete.Reducible (pl(rand(#(.int z), #(.lbl α)))) σ₁ :=
    Reducible.toDiscrete (by no_urand) (reducible_of_headReducible (by is_lc) (fun hz => by rw [hz] at HheadL; simp at HheadL))
  have HheadR : 0 < headStep ⟨pl(rand(#(.int z), #(.lbl α'))), σ₁'⟩
        {⟨pl(#(.int 0)), σ₁'⟩} :=
    HeadStepSupport.pos
      (.RandTapeOtherS Hz Hlk_α' HneM (_root_.le_refl _) Hz rfl)
  have HredR_rand : Discrete.Reducible (pl(rand(#(.int z), #(.lbl α')))) σ₁' :=
    Reducible.toDiscrete (by no_urand) (reducible_of_headReducible (by is_lc) (fun hz => by rw [hz] at HheadR; simp at HheadR))
  have HredR : Discrete.Reducible (K.fill (pl(rand(#(.int z), #(.lbl α'))))) σ₁' :=
    Reducible.toDiscrete (by no_urand) (HredR_rand.toReducible.fill K)
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  let R : Cfg rT → Cfg rT → Prop := fun c₁ c₂ =>
    ∃ n : Int, 0 ≤ n ∧ n < z ∧
      c₁ = ⟨pl(#(.int n)), σ₁⟩ ∧ c₂ = ⟨K.fill (pl(#(.int (f n)))), σ₁'⟩
  iexists R, 0, ε
  isplitr; · ipureintro; rw [zero_add]
  isplitr; · ipureintro; exact HredL.toReducible
  isplitr; · ipureintro; exact HredR.toReducible
  isplitr
  · ipureintro
    rw [primStep_rand_lbl_wrong Hz HneM σ₁ α fs Hlk_α]
    have Hv_rand : ¬ (pl(rand(#(.int z), #(.lbl α'))) : Exp rT).isValue := by
      intro ⟨w⟩; nomatch w
    rw [primStep_fill Hv_rand, primStep_rand_lbl_wrong Hz HneM σ₁' α' fs' Hlk_α']
    have Hbase := Cfg.uniform_addCoupl_bij Hz σ₁ σ₁' f hdom hbij
    have : AddCoupl 0
        {p : Cfg rT × Cfg rT | R p.1 p.2}
        ((Cfg.uniform z σ₁).map id)
        ((Cfg.uniform z σ₁').map (fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT))) := by
      refine AddCoupl.map (f := id) (g := K.fillCfg)
        measurable_id (Ectx.fillCfg.measurable K)
        (R := {p : Cfg rT × Cfg rT | R p.1 p.2})
        ?_
        Hbase
      intro a b hab
      obtain ⟨n, h0, hz, heqL, heqR⟩ := hab
      refine ⟨n, h0, hz, heqL, ?_⟩
      subst heqR
      rfl
    rw [MeasureTheory.Measure.map_id] at this
    exact this
  iintro %e₂ %σ₂ %e₂' %σ₂' %HR
  obtain ⟨n, hn0, hnz, heq1, heq2⟩ := HR
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq2
  imodintro
  iintro !>
  ihave HUpd := specProg_update (GF := GF)
    (e3 := K.fill (pl(#(.int (f n))))) $$ Hs Hj
  imod HUpd with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  isplitl [Hσ]; · iexact Hσ
  isplitl [Hs']; · iexact Hs'
  isplitl [Hε]; · iexact Hε
  iapply (wp_value_of_toVal (v := (.int n : Val rT)) rfl)
  ihave HαNat := show (α ↪ₐ ⟨M, fs⟩) ⊢@{IProp GF} appNatTape α M xs by
    iintro Hb
    unfold appNatTape
    iexists fs
    isplitr; · ipureintro; exact hmap_fs
    iexact Hb
  ihave HαNat' := HαNat $$ Hα_b
  ihave Hα'Nat := show (α' ↪ₛ ⟨M, fs'⟩) ⊢@{IProp GF} specNatTape α' M ys by
    iintro Hb
    unfold specNatTape
    iexists fs'
    isplitr; · ipureintro; exact hmap_fs'
    iexact Hb
  ihave Hα'Nat' := Hα'Nat $$ Hα'_b
  iapply Hcnt
  isplitl [HαNat']; · iexact HαNat'
  isplitl [Hα'Nat']; · iexact Hα'Nat'
  isplitl [Hj']; · iexact Hj'
  ipureintro; exact ⟨hn0, hnz⟩

/-- Fully labeled two-sided coupling via a bijection `f`, both tapes empty. -/
theorem wp_couple_rand_lbl_rand_lbl (z : Int) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (α α' : Loc) (Φ : Val rT → IProp GF) :
    iprop(▷ appNatTape α z [] ∗ ▷ specNatTape α' z [] ∗
        (⤇ K.fill (pl(rand(#(.int z), #(.lbl α'))))) ∗
        (∀ (n : Int),
          appNatTape α z [] ∗ specNatTape α' z [] ∗
            (⤇ K.fill (pl(#(.int (f n))))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗
          Φ (.int n : Val rT)))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.lbl α)))) Φ := by
  iintro ⟨Hα, Hα', Hj, Hcnt⟩
  have Hv : (pl(rand(#(.int z), #(.lbl α))) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_prim_steps_coupl Hv)
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  iapply (later_timeless_fupd (P := appNatTape α z []))
  isplitl [Hα]; · iexact Hα
  iintro Hα
  iapply (later_timeless_fupd (P := specNatTape α' z []))
  isplitl [Hα']; · iexact Hα'
  iintro Hα'
  ihave HαEx := show appNatTape α z [] ⊢@{IProp GF}
      iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < z },
        (⌜fs.map (fun x => x.val) = []⌝) ∗ α ↪ₐ ⟨z, fs⟩) from
    BI.BIBase.Entails.rfl $$ Hα
  icases HαEx with ⟨%fs, %hmap_fs, Hα_b⟩
  ihave Hα'Ex := show specNatTape α' z [] ⊢@{IProp GF}
      iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < z },
        (⌜fs.map (fun x => x.val) = []⌝) ∗ α' ↪ₛ ⟨z, fs⟩) from
    BI.BIBase.Entails.rfl $$ Hα'
  icases Hα'Ex with ⟨%fs', %hmap_fs', Hα'_b⟩
  have hfs_nil : fs = [] := List.map_eq_nil_iff.mp hmap_fs
  have hfs'_nil : fs' = [] := List.map_eq_nil_iff.mp hmap_fs'
  subst hfs_nil; subst hfs'_nil
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  ihave %Hlk_α := app_state_lookup_tape (GF := GF) (σ := σ₁) $$ Hσ Hα_b
  ihave %Hlk_α' := spec_auth_lookup_tape (GF := GF) (σ := σ₁') $$ Hs Hα'_b
  have HheadL : 0 < headStep ⟨pl(rand(#(.int z), #(.lbl α))), σ₁⟩
        {⟨pl(#(.int 0)), σ₁⟩} :=
    HeadStepSupport.pos
      (.RandTapeEmptyS Hz Hlk_α rfl (_root_.le_refl _) Hz rfl)
  have HredL : Discrete.Reducible (pl(rand(#(.int z), #(.lbl α)))) σ₁ :=
    Reducible.toDiscrete (by no_urand) (reducible_of_headReducible (by is_lc) (fun hz => by rw [hz] at HheadL; simp at HheadL))
  have HheadR : 0 < headStep ⟨pl(rand(#(.int z), #(.lbl α'))), σ₁'⟩
        {⟨pl(#(.int 0)), σ₁'⟩} :=
    HeadStepSupport.pos
      (.RandTapeEmptyS Hz Hlk_α' rfl (_root_.le_refl _) Hz rfl)
  have HredR_rand : Discrete.Reducible (pl(rand(#(.int z), #(.lbl α')))) σ₁' :=
    Reducible.toDiscrete (by no_urand) (reducible_of_headReducible (by is_lc) (fun hz => by rw [hz] at HheadR; simp at HheadR))
  have HredR : Discrete.Reducible (K.fill (pl(rand(#(.int z), #(.lbl α'))))) σ₁' :=
    Reducible.toDiscrete (by no_urand) (HredR_rand.toReducible.fill K)
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  let R : Cfg rT → Cfg rT → Prop := fun c₁ c₂ =>
    ∃ n : Int, 0 ≤ n ∧ n < z ∧
      c₁ = ⟨pl(#(.int n)), σ₁⟩ ∧ c₂ = ⟨K.fill (pl(#(.int (f n)))), σ₁'⟩
  iexists R, 0, ε
  isplitr; · ipureintro; rw [zero_add]
  isplitr; · ipureintro; exact HredL.toReducible
  isplitr; · ipureintro; exact HredR.toReducible
  isplitr
  · ipureintro
    rw [primStep_rand_lbl_empty Hz σ₁ α Hlk_α]
    have Hv_rand : ¬ (pl(rand(#(.int z), #(.lbl α'))) : Exp rT).isValue := by
      intro ⟨w⟩; nomatch w
    rw [primStep_fill Hv_rand, primStep_rand_lbl_empty Hz σ₁' α' Hlk_α']
    have Hbase := Cfg.uniform_addCoupl_bij Hz σ₁ σ₁' f hdom hbij
    have : AddCoupl 0
        {p : Cfg rT × Cfg rT | R p.1 p.2}
        ((Cfg.uniform z σ₁).map id)
        ((Cfg.uniform z σ₁').map (fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT))) := by
      refine AddCoupl.map (f := id) (g := K.fillCfg)
        measurable_id (Ectx.fillCfg.measurable K)
        (R := {p : Cfg rT × Cfg rT | R p.1 p.2})
        ?_
        Hbase
      intro a b hab
      obtain ⟨n, h0, hz, heqL, heqR⟩ := hab
      refine ⟨n, h0, hz, heqL, ?_⟩
      subst heqR
      rfl
    rw [MeasureTheory.Measure.map_id] at this
    exact this
  iintro %e₂ %σ₂ %e₂' %σ₂' %HR
  obtain ⟨n, hn0, hnz, heq1, heq2⟩ := HR
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq2
  imodintro
  iintro !>
  ihave HUpd := specProg_update (GF := GF)
    (e3 := K.fill (pl(#(.int (f n))))) $$ Hs Hj
  imod HUpd with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  isplitl [Hσ]; · iexact Hσ
  isplitl [Hs']; · iexact Hs'
  isplitl [Hε]; · iexact Hε
  iapply (wp_value_of_toVal (v := (.int n : Val rT)) rfl)
  ihave HαNat := show (α ↪ₐ ⟨z, ([] : List _)⟩) ⊢@{IProp GF} appNatTape α z [] by
    iintro Hb
    unfold appNatTape
    iexists ([] : List _)
    isplitr; · ipureintro; simp
    iexact Hb
  ihave HαNat' := HαNat $$ Hα_b
  ihave Hα'Nat := show (α' ↪ₛ ⟨z, ([] : List _)⟩) ⊢@{IProp GF} specNatTape α' z [] by
    iintro Hb
    unfold specNatTape
    iexists ([] : List _)
    isplitr; · ipureintro; simp
    iexact Hb
  ihave Hα'Nat' := Hα'Nat $$ Hα'_b
  iapply Hcnt
  isplitl [HαNat']; · iexact HαNat'
  isplitl [Hα'Nat']; · iexact Hα'Nat'
  isplitl [Hj']; · iexact Hj'
  ipureintro; exact ⟨hn0, hnz⟩

/-! ## Mixed tape-rand couplings -/

theorem wp_couple_tape_rand (z : Int) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (α : Loc) (Φ : Val rT → IProp GF) :
    iprop(▷ appNatTape α z [] ∗
        (⤇ K.fill (pl(rand(#(.int z), #(.unit))))) ∗
        (∀ (n : Int),
          appNatTape α z [] ∗
            (⤇ K.fill (pl(#(.int (f n))))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗
          Φ (.int n : Val rT)))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.lbl α)))) Φ := by
  iintro ⟨Hα, Hj, Hcnt⟩
  have Hv : (pl(rand(#(.int z), #(.lbl α))) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_prim_steps_coupl Hv)
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  iapply (later_timeless_fupd (P := appNatTape α z []))
  isplitl [Hα]; · iexact Hα
  iintro Hα
  ihave HαEx := show appNatTape α z [] ⊢@{IProp GF}
      iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < z },
        (⌜fs.map (fun x => x.val) = []⌝) ∗ α ↪ₐ ⟨z, fs⟩) from
    BI.BIBase.Entails.rfl $$ Hα
  icases HαEx with ⟨%fs, %hmap_fs, Hα_b⟩
  have hfs_nil : fs = [] := List.map_eq_nil_iff.mp hmap_fs
  subst hfs_nil
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  ihave %Hlk_α := app_state_lookup_tape (GF := GF) (σ := σ₁) $$ Hσ Hα_b
  have HheadL : 0 < headStep ⟨pl(rand(#(.int z), #(.lbl α))), σ₁⟩
        {⟨pl(#(.int 0)), σ₁⟩} :=
    HeadStepSupport.pos
      (.RandTapeEmptyS Hz Hlk_α rfl (_root_.le_refl _) Hz rfl)
  have HredL : Discrete.Reducible (pl(rand(#(.int z), #(.lbl α)))) σ₁ :=
    Reducible.toDiscrete (by no_urand) (reducible_of_headReducible (by is_lc) (fun hz => by rw [hz] at HheadL; simp at HheadL))
  have HheadR : 0 < headStep ⟨pl(rand(#(.int z), #(.unit))), σ₁'⟩
        {⟨pl(#(.int 0)), σ₁'⟩} :=
    HeadStepSupport.pos (.RandNoTapeS Hz (_root_.le_refl _) Hz)
  have HredR_rand : Discrete.Reducible (pl(rand(#(.int z), #(.unit)))) σ₁' :=
    Reducible.toDiscrete (by no_urand) (reducible_of_headReducible (by is_lc) (fun hz => by rw [hz] at HheadR; simp at HheadR))
  have HredR : Discrete.Reducible (K.fill (pl(rand(#(.int z), #(.unit))))) σ₁' :=
    Reducible.toDiscrete (by no_urand) (HredR_rand.toReducible.fill K)
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  let R : Cfg rT → Cfg rT → Prop := fun c₁ c₂ =>
    ∃ n : Int, 0 ≤ n ∧ n < z ∧
      c₁ = ⟨pl(#(.int n)), σ₁⟩ ∧ c₂ = ⟨K.fill (pl(#(.int (f n)))), σ₁'⟩
  iexists R, 0, ε
  isplitr; · ipureintro; rw [zero_add]
  isplitr; · ipureintro; exact HredL.toReducible
  isplitr; · ipureintro; exact HredR.toReducible
  isplitr
  · ipureintro
    rw [primStep_rand_lbl_empty Hz σ₁ α Hlk_α]
    have Hv_rand : ¬ (pl(rand(#(.int z), #(.unit))) : Exp rT).isValue := by
      intro ⟨w⟩; nomatch w
    rw [primStep_fill Hv_rand, primStep_rand_unit Hz]
    have Hbase := Cfg.uniform_addCoupl_bij Hz σ₁ σ₁' f hdom hbij
    have : AddCoupl 0
        {p : Cfg rT × Cfg rT | R p.1 p.2}
        ((Cfg.uniform z σ₁).map id)
        ((Cfg.uniform z σ₁').map (fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT))) := by
      refine AddCoupl.map (f := id) (g := K.fillCfg)
        measurable_id (Ectx.fillCfg.measurable K)
        (R := {p : Cfg rT × Cfg rT | R p.1 p.2})
        ?_
        Hbase
      intro a b hab
      obtain ⟨n, h0, hz, heqL, heqR⟩ := hab
      refine ⟨n, h0, hz, heqL, ?_⟩
      subst heqR
      rfl
    rw [MeasureTheory.Measure.map_id] at this
    exact this
  iintro %e₂ %σ₂ %e₂' %σ₂' %HR
  obtain ⟨n, hn0, hnz, heq1, heq2⟩ := HR
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq2
  imodintro
  iintro !>
  ihave HUpd := specProg_update (GF := GF)
    (e3 := K.fill (pl(#(.int (f n))))) $$ Hs Hj
  imod HUpd with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  isplitl [Hσ]; · iexact Hσ
  isplitl [Hs']; · iexact Hs'
  isplitl [Hε]; · iexact Hε
  iapply (wp_value_of_toVal (v := (.int n : Val rT)) rfl)
  ihave HαNat := show (α ↪ₐ ⟨z, ([] : List _)⟩) ⊢@{IProp GF} appNatTape α z [] by
    iintro Hb
    unfold appNatTape
    iexists ([] : List _)
    isplitr; · ipureintro; simp
    iexact Hb
  ihave HαNat' := HαNat $$ Hα_b
  iapply Hcnt
  isplitl [HαNat']; · iexact HαNat'
  isplitl [Hj']; · iexact Hj'
  ipureintro; exact ⟨hn0, hnz⟩

/-- Symmetric: couple LHS unit rand with RHS rand on empty tape. -/
theorem wp_couple_rand_tape (z : Int) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (α' : Loc) (Φ : Val rT → IProp GF) :
    iprop(▷ specNatTape α' z [] ∗
        (⤇ K.fill (pl(rand(#(.int z), #(.lbl α'))))) ∗
        (∀ (n : Int),
          specNatTape α' z [] ∗
            (⤇ K.fill (pl(#(.int (f n))))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗
          Φ (.int n : Val rT)))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.unit)))) Φ := by
  iintro ⟨Hα', Hj, Hcnt⟩
  have Hv : (pl(rand(#(.int z), #(.unit))) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_prim_steps_coupl Hv)
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  iapply (later_timeless_fupd (P := specNatTape α' z []))
  isplitl [Hα']; · iexact Hα'
  iintro Hα'
  ihave Hα'Ex := show specNatTape α' z [] ⊢@{IProp GF}
      iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < z },
        (⌜fs.map (fun x => x.val) = []⌝) ∗ α' ↪ₛ ⟨z, fs⟩) from
    BI.BIBase.Entails.rfl $$ Hα'
  icases Hα'Ex with ⟨%fs', %hmap_fs', Hα'_b⟩
  have hfs'_nil : fs' = [] := List.map_eq_nil_iff.mp hmap_fs'
  subst hfs'_nil
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  ihave %Hlk_α' := spec_auth_lookup_tape (GF := GF) (σ := σ₁') $$ Hs Hα'_b
  have HheadL : 0 < headStep ⟨pl(rand(#(.int z), #(.unit))), σ₁⟩
        {⟨pl(#(.int 0)), σ₁⟩} :=
    HeadStepSupport.pos (.RandNoTapeS Hz (_root_.le_refl _) Hz)
  have HredL : Discrete.Reducible (pl(rand(#(.int z), #(.unit)))) σ₁ :=
    Reducible.toDiscrete (by no_urand) (reducible_of_headReducible (by is_lc) (fun hz => by rw [hz] at HheadL; simp at HheadL))
  have HheadR : 0 < headStep ⟨pl(rand(#(.int z), #(.lbl α'))), σ₁'⟩
        {⟨pl(#(.int 0)), σ₁'⟩} :=
    HeadStepSupport.pos
      (.RandTapeEmptyS Hz Hlk_α' rfl (_root_.le_refl _) Hz rfl)
  have HredR_rand : Discrete.Reducible (pl(rand(#(.int z), #(.lbl α')))) σ₁' :=
    Reducible.toDiscrete (by no_urand) (reducible_of_headReducible (by is_lc) (fun hz => by rw [hz] at HheadR; simp at HheadR))
  have HredR : Discrete.Reducible (K.fill (pl(rand(#(.int z), #(.lbl α'))))) σ₁' :=
    Reducible.toDiscrete (by no_urand) (HredR_rand.toReducible.fill K)
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  let R : Cfg rT → Cfg rT → Prop := fun c₁ c₂ =>
    ∃ n : Int, 0 ≤ n ∧ n < z ∧
      c₁ = ⟨pl(#(.int n)), σ₁⟩ ∧ c₂ = ⟨K.fill (pl(#(.int (f n)))), σ₁'⟩
  iexists R, 0, ε
  isplitr; · ipureintro; rw [zero_add]
  isplitr; · ipureintro; exact HredL.toReducible
  isplitr; · ipureintro; exact HredR.toReducible
  isplitr
  · ipureintro
    rw [primStep_rand_unit Hz]
    have Hv_rand : ¬ (pl(rand(#(.int z), #(.lbl α'))) : Exp rT).isValue := by
      intro ⟨w⟩; nomatch w
    rw [primStep_fill Hv_rand, primStep_rand_lbl_empty Hz σ₁' α' Hlk_α']
    have Hbase := Cfg.uniform_addCoupl_bij Hz σ₁ σ₁' f hdom hbij
    have : AddCoupl 0
        {p : Cfg rT × Cfg rT | R p.1 p.2}
        ((Cfg.uniform z σ₁).map id)
        ((Cfg.uniform z σ₁').map (fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT))) := by
      refine AddCoupl.map (f := id) (g := K.fillCfg)
        measurable_id (Ectx.fillCfg.measurable K)
        (R := {p : Cfg rT × Cfg rT | R p.1 p.2})
        ?_
        Hbase
      intro a b hab
      obtain ⟨n, h0, hz, heqL, heqR⟩ := hab
      refine ⟨n, h0, hz, heqL, ?_⟩
      subst heqR
      rfl
    rw [MeasureTheory.Measure.map_id] at this
    exact this
  iintro %e₂ %σ₂ %e₂' %σ₂' %HR
  obtain ⟨n, hn0, hnz, heq1, heq2⟩ := HR
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq2
  imodintro
  iintro !>
  ihave HUpd := specProg_update (GF := GF)
    (e3 := K.fill (pl(#(.int (f n))))) $$ Hs Hj
  imod HUpd with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  isplitl [Hσ]; · iexact Hσ
  isplitl [Hs']; · iexact Hs'
  isplitl [Hε]; · iexact Hε
  iapply (wp_value_of_toVal (v := (.int n : Val rT)) rfl)
  ihave Hα'Nat := show (α' ↪ₛ ⟨z, ([] : List _)⟩) ⊢@{IProp GF} specNatTape α' z [] by
    iintro Hb
    unfold specNatTape
    iexists ([] : List _)
    isplitr; · ipureintro; simp
    iexact Hb
  ihave Hα'Nat' := Hα'Nat $$ Hα'_b
  iapply Hcnt
  isplitl [Hα'Nat']; · iexact Hα'Nat'
  isplitl [Hj']; · iexact Hj'
  ipureintro; exact ⟨hn0, hnz⟩

end CouplingRules

end ProbLang
