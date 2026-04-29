module

public import Metrology.Approxis.Lifting
public import Metrology.Approxis.PrimitiveLaws

@[expose] public section

/-!
# Coupling Rules

Coupling rules used by Compatibility/Fundamental/Soundness.
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS
open scoped AppGS

namespace ProbLang

/-! ## Timeless instances for tape predicates -/

section TimelessTapes
open scoped AppGS

variable {GF : BundledGFunctors}

instance heapView_tape_frag_discreteE (l : Loc) (t : Tape) :
    OFE.DiscreteE (HeapView.Frag (F := ℕ+) (H := LocHeap) l (.own 1) (toAgree t)) := by
  unfold HeapView.Frag
  exact View.frag_discrete ⟨fun H => OFE.Discrete.discrete_0 H⟩

instance appTapesFrag_timeless [IApp : AppGS GF] (l : Loc) (t : Tape) :
    BI.Timeless (iprop(l ↪ₐ t) : IProp GF) := by
  unfold appTapesFrag
  exact iOwn_timeless

instance specTapesFrag_timeless [ISpec : SpecGS GF] (l : Loc) (t : Tape) :
    BI.Timeless (iprop(l ↪ₛ t) : IProp GF) := by
  unfold specTapesFrag
  exact iOwn_timeless

instance heapView_heap_frag_discreteE (l : Loc) (v : Val) :
    OFE.DiscreteE (HeapView.Frag (F := ℕ+) (H := LocHeap) l (.own 1) (toAgree v)) := by
  unfold HeapView.Frag
  exact View.frag_discrete ⟨fun H => OFE.Discrete.discrete_0 H⟩

instance appHeapFrag_timeless [IApp : AppGS GF] (l : Loc) (v : Val) :
    BI.Timeless (iprop(l ↦ v) : IProp GF) := by
  unfold appHeapFrag
  exact iOwn_timeless

instance specHeapFrag_timeless [ISpec : SpecGS GF] (l : Loc) (v : Val) :
    BI.Timeless (iprop(l ↦ₛ v) : IProp GF) := by
  unfold specHeapFrag
  exact iOwn_timeless

instance appNatTape_timeless [IApp : AppGS GF] (l : Loc) (z : Int) (ns : List Int) :
    BI.Timeless (appNatTape l z ns : IProp GF) := by
  unfold appNatTape
  infer_instance

instance specNatTape_timeless [ISpec : SpecGS GF] (l : Loc) (z : Int) (ns : List Int) :
    BI.Timeless (specNatTape l z ns : IProp GF) := by
  unfold specNatTape
  infer_instance

/-- Strip `▷` from a Timeless hypothesis when the continuation is in `fupd`
position. Mirrors Rocq's `iMod ">Hα"` automation. -/
theorem later_timeless_fupd {PROP : Type _} [BI PROP] [BIUpdate PROP] [BIFUpdate PROP]
    {P : PROP} [BI.Timeless P] {E₁ E₂ : CoPset} {Q : PROP} :
    (iprop(▷ P) ∗ (P -∗ |={E₁, E₂}=> Q)) ⊢ (iprop(|={E₁, E₂}=> Q) : PROP) := by
  refine BIBase.Entails.trans ?_ IsExcept0.is_except0
  refine BI.sep_mono_l BI.Timeless.timeless |>.trans ?_
  refine BIBase.Entails.trans ?_ (BI.except0_mono (BI.wand_elim_r (P := P) (Q := iprop(|={E₁,E₂}=> Q))))
  refine BIBase.Entails.trans ?_ BI.except0_sep.2
  exact BI.sep_mono_r BI.except0_intro

end TimelessTapes

/-! ## Core probability fact: uniform coupling under bijection -/

theorem Cfg.lintegral_uniform {z : Int} (Hz : 0 < z) (σ : State) (φ : Cfg → ENNReal) :
    ∫⁻ c, φ c ∂(Cfg.uniform z σ) =
      ((z.toNat : ENNReal)⁻¹) * ∑ n ∈ Finset.Ico (0 : Int) z,
        φ (⟨.lit (.int n), σ⟩ : Cfg) := by
  classical
  have Huniform : Cfg.uniform z σ =
      ((PMF.uniformOfFinset (Finset.Ico (0 : Int) z)
          (Finset.nonempty_Ico.mpr Hz)).toMeasure).map
        (fun n : Int => (⟨.lit (.int n), σ⟩ : Cfg)) := by
    unfold Cfg.uniform Int.isPos
    simp only [Hz, dite_true]
  rw [Huniform,
      MeasureTheory.lintegral_map (Measurable.of_discrete) Measurable.of_discrete]
  rw [MeasureTheory.lintegral_countable']
  have hcard : (Finset.Ico (0 : Int) z).card = z.toNat := by
    rw [Int.card_Ico]
    omega
  have hpmf_mem : ∀ n ∈ Finset.Ico (0 : Int) z,
      ((PMF.uniformOfFinset (Finset.Ico (0 : Int) z) (Finset.nonempty_Ico.mpr Hz)).toMeasure)
        {n} = ((z.toNat : ENNReal)⁻¹) := by
    intro n hn
    rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
        PMF.uniformOfFinset_apply_of_mem _ hn, hcard]
  have hpmf_notmem : ∀ n ∉ Finset.Ico (0 : Int) z,
      ((PMF.uniformOfFinset (Finset.Ico (0 : Int) z) (Finset.nonempty_Ico.mpr Hz)).toMeasure)
        {n} = 0 := by
    intro n hn
    rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
        PMF.uniformOfFinset_apply_of_notMem _ hn]
  have htsum : ∑' n : Int, φ (⟨.lit (.int n), σ⟩ : Cfg) *
      ((PMF.uniformOfFinset (Finset.Ico (0 : Int) z) (Finset.nonempty_Ico.mpr Hz)).toMeasure)
        {n}
      = ∑ n ∈ Finset.Ico (0 : Int) z,
          φ (⟨.lit (.int n), σ⟩ : Cfg) * ((z.toNat : ENNReal)⁻¹) := by
    rw [tsum_eq_sum (s := Finset.Ico (0 : Int) z) ?_]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [hpmf_mem n hn]
    · intro n hn
      rw [hpmf_notmem n hn, mul_zero]
  rw [htsum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- Uniform-measure coupling under a bijection on the support: for `f` that
restricts to a bijection on `Ico 0 z`, `Cfg.uniform z σ` and `Cfg.uniform z σ'`
are exactly coupled along `{(⟨#n, σ⟩, ⟨#(f n), σ'⟩) | n ∈ Ico 0 z}`. -/
theorem Cfg.uniform_addCoupl_bij {z : Int} (Hz : 0 < z) (σ σ' : State)
    (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m) :
    AddCoupl 0
      {p : Cfg × Cfg | ∃ n : Int, 0 ≤ n ∧ n < z ∧
        p.1 = ⟨.lit (.int n), σ⟩ ∧ p.2 = ⟨.lit (.int (f n)), σ'⟩}
      (Cfg.uniform z σ) (Cfg.uniform z σ') := by
  classical
  rintro ⟨φ, Hφm, Hφb⟩ ⟨ψ, Hψm, Hψb⟩ Hle
  simp only [add_zero]
  show ∫⁻ c, φ c ∂(Cfg.uniform z σ) ≤ ∫⁻ c, ψ c ∂(Cfg.uniform z σ')
  rw [Cfg.lintegral_uniform Hz σ φ, Cfg.lintegral_uniform Hz σ' ψ]
  refine mul_le_mul_right ?_ _
  have hreindex : ∑ m ∈ Finset.Ico (0 : Int) z, ψ (⟨.lit (.int m), σ'⟩ : Cfg)
      = ∑ n ∈ Finset.Ico (0 : Int) z, ψ (⟨.lit (.int (f n)), σ'⟩ : Cfg) := by
    symm
    refine Finset.sum_bij (fun n _ => f n) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_Ico] at hn ⊢
      exact hdom n hn.1 hn.2
    · intro n₁ hn₁ n₂ hn₂ h
      simp only [Finset.mem_Ico] at hn₁ hn₂
      obtain ⟨n₀, ⟨⟨_, _⟩, _⟩, huniq⟩ := hbij (f n₁)
        (hdom n₁ hn₁.1 hn₁.2).1 (hdom n₁ hn₁.1 hn₁.2).2
      have h1 : n₁ = n₀ := huniq n₁ ⟨hn₁, rfl⟩
      have h2 : n₂ = n₀ := huniq n₂ ⟨hn₂, h.symm⟩
      exact h1.trans h2.symm
    · intro m hm
      simp only [Finset.mem_Ico] at hm
      obtain ⟨n₀, ⟨hn₀, hfn₀⟩, _⟩ := hbij m hm.1 hm.2
      exact ⟨n₀, by simp only [Finset.mem_Ico]; exact hn₀, hfn₀⟩
    · intro n _; rfl
  rw [hreindex]
  refine Finset.sum_le_sum fun n hn => ?_
  simp only [Finset.mem_Ico] at hn
  exact Hle ⟨n, hn.1, hn.2, rfl, rfl⟩

/-- `primStep` of `rand #z ()` (unlabeled) equals `Cfg.uniform z σ`. -/
theorem primStep_rand_unit {z : Int} (Hz : 0 < z) (σ : State) :
    primStep (⟨Exp.rand (.lit (.int z)) (.lit .unit), σ⟩ : Cfg) = Cfg.uniform z σ := by
  have Hhead : 0 < headStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ⟩
        {⟨.lit (.int 0), σ⟩} :=
    (headStep_support_iff _ _ _ _).mpr (.RandNoTapeS Hz (_root_.le_refl _) Hz)
  rw [primStep_eq_headStep ⟨_, Hhead⟩]
  rfl

/-- `primStep` of `rand #z (lbl α)` when the tape has the wrong bound. -/
theorem primStep_rand_lbl_wrong {z M : Int} (Hz : 0 < z) (HneM : z ≠ M)
    (σ : State) (l : Loc) (fs : List { z' : Int // 0 ≤ z' ∧ z' < M })
    (Hlk : σ.tapes[l]? = some ⟨M, fs⟩) :
    primStep (⟨Exp.rand (.lit (.int z)) (.lit (.lbl l)), σ⟩ : Cfg) = Cfg.uniform z σ := by
  have Hhead : 0 < headStep ⟨Exp.rand (.lit (.int z)) (.lit (.lbl l)), σ⟩
        {⟨.lit (.int 0), σ⟩} :=
    (headStep_support_iff _ _ _ _).mpr
      (.RandTapeOtherS Hz Hlk HneM (_root_.le_refl _) Hz rfl)
  rw [primStep_eq_headStep ⟨_, Hhead⟩]
  show (match σ.tapes[l]? with
        | none => (0 : MeasureTheory.Measure Cfg)
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
theorem primStep_rand_lbl_empty {z : Int} (Hz : 0 < z) (σ : State) (l : Loc)
    (Hlk : σ.tapes[l]? = some ⟨z, []⟩) :
    primStep (⟨Exp.rand (.lit (.int z)) (.lit (.lbl l)), σ⟩ : Cfg) = Cfg.uniform z σ := by
  have Hhead : 0 < headStep ⟨Exp.rand (.lit (.int z)) (.lit (.lbl l)), σ⟩
        {⟨.lit (.int 0), σ⟩} :=
    (headStep_support_iff _ _ _ _).mpr
      (.RandTapeEmptyS Hz Hlk rfl (_root_.le_refl _) Hz rfl)
  rw [primStep_eq_headStep ⟨_, Hhead⟩]
  show (match σ.tapes[l]? with
        | none => (0 : MeasureTheory.Measure Cfg)
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
theorem AddCoupl_steps_ctx_bind_r {α} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    {μ : Measure α} {e : Exp} {σ : State} {R : Set (α × Cfg)} {ε : ENNReal}
    {K : Ectx} (hv : ¬ e.isValue)
    (Hcpl : AddCoupl ε R μ (primStep ⟨e, σ⟩)) :
    AddCoupl ε
      {p : α × Cfg | ∃ e'', p.2.expr = K.fill e'' ∧ R (p.1, ⟨e'', p.2.state⟩)}
      μ (primStep ⟨K.fill e, σ⟩) := by
  rw [primStep_fill (K := K) hv]
  rw [show μ = μ.map id from (MeasureTheory.Measure.map_id).symm]
  refine AddCoupl.map (f := id) (g := fun ρ : Cfg => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg))
    Measurable.of_discrete Measurable.of_discrete
    (R := {p : α × Cfg | ∃ e'', p.2.expr = K.fill e'' ∧ R (p.1, ⟨e'', p.2.state⟩)}) ?_ Hcpl
  intro a ⟨e', σ'⟩ HR
  refine ⟨e', rfl, ?_⟩
  exact HR

open MeasureTheory in
/-- Variant of `AddCoupl_steps_ctx_bind_r` where the relation only depends on
the expression of the second component. -/
theorem AddCoupl_steps_ctx_bind_r_no_state
    {μ : Measure Cfg} {e : Exp} {σ : State} {R : Exp → Exp → Prop} {ε : ENNReal}
    {K : Ectx} (hv : ¬ e.isValue)
    (Hcpl : AddCoupl ε {p : Cfg × Cfg | R p.1.expr p.2.expr} μ (primStep ⟨e, σ⟩)) :
    AddCoupl ε
      {p : Cfg × Cfg | ∃ e'', p.2.expr = K.fill e'' ∧ R p.1.expr e''}
      μ (primStep ⟨K.fill e, σ⟩) := by
  rw [primStep_fill (K := K) hv]
  rw [show μ = μ.map id from (MeasureTheory.Measure.map_id).symm]
  refine AddCoupl.map (f := id) (g := fun ρ : Cfg => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg))
    Measurable.of_discrete Measurable.of_discrete
    (R := {p : Cfg × Cfg | ∃ e'', p.2.expr = K.fill e'' ∧ R p.1.expr e''}) ?_ Hcpl
  intro a b HR
  refine ⟨b.expr, rfl, ?_⟩
  exact HR

section CouplingRules

variable {hlc : Bool} {GF : BundledGFunctors} [ApproxisGS hlc GF]

/-- Same-bound bijective coupling: `f : Int → Int` restricts to a bijection on
`[0, z)`. -/
theorem wp_couple_rand_rand (z : Int) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx) (E : CoPset) (Φ : Val → IProp GF) :
    iprop((⤇ K.fill (.rand (.lit (.int z)) (.lit .unit))) ∗
        (∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗
          (⤇ K.fill (.lit (.int (f n)))) -∗
          Φ (⟨.lit (.int n), IsVal.lit⟩ : Val)))
      ⊢@{IProp GF} wp E (.rand (.lit (.int z)) (.lit .unit)) Φ := by
  iintro ⟨Hj, Hcnt⟩
  have Hv : (Exp.rand (Exp.lit (.int z)) (Exp.lit .unit)).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_prim_steps_coupl Hv)
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  have HheadL : 0 < headStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁⟩
        {⟨.lit (.int 0), σ₁⟩} :=
    (headStep_support_iff _ _ _ _).mpr (.RandNoTapeS Hz (_root_.le_refl _) Hz)
  have HredL : Reducible (Exp.rand (.lit (.int z)) (.lit .unit)) σ₁ :=
    Reducible.of_head ⟨_, HheadL⟩
  have HheadR : 0 < headStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁'⟩
        {⟨.lit (.int 0), σ₁'⟩} :=
    (headStep_support_iff _ _ _ _).mpr (.RandNoTapeS Hz (_root_.le_refl _) Hz)
  have HredR_rand : Reducible (Exp.rand (.lit (.int z)) (.lit .unit)) σ₁' :=
    Reducible.of_head ⟨_, HheadR⟩
  have HredR : Reducible (K.fill (.rand (.lit (.int z)) (.lit .unit))) σ₁' :=
    HredR_rand.fill K
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  let R : Cfg → Cfg → Prop := fun c₁ c₂ =>
    ∃ n : Int, 0 ≤ n ∧ n < z ∧
      c₁ = ⟨.lit (.int n), σ₁⟩ ∧ c₂ = ⟨K.fill (.lit (.int (f n))), σ₁'⟩
  iexists R, 0, ε
  isplitr; · ipure_intro; rw [zero_add]
  isplitr; · ipure_intro; exact HredL
  isplitr; · ipure_intro; exact HredR
  isplitr
  · ipure_intro
    rw [primStep_rand_unit Hz]
    have Hv_rand : ¬ (Exp.rand (Exp.lit (.int z)) (Exp.lit .unit)).isValue := by
      intro ⟨w⟩; nomatch w
    rw [primStep_fill Hv_rand, primStep_rand_unit Hz]
    have Hbase := Cfg.uniform_addCoupl_bij Hz σ₁ σ₁' f hdom hbij
    have : AddCoupl 0
        {p : Cfg × Cfg | R p.1 p.2}
        ((Cfg.uniform z σ₁).map id)
        ((Cfg.uniform z σ₁').map (fun ρ : Cfg => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg))) := by
      refine AddCoupl.map (f := id) (g := fun ρ : Cfg => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg))
        Measurable.of_discrete Measurable.of_discrete
        (R := {p : Cfg × Cfg | R p.1 p.2})
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
    (e3 := K.fill (.lit (.int (f n)))) $$ Hs Hj
  imod HUpd with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  isplitl [Hσ]; · iexact Hσ
  isplitl [Hs']; · iexact Hs'
  isplitl [Hε]; · iexact Hε
  iapply (wp_value_of_toVal (v := ⟨.lit (.int n), IsVal.lit⟩) rfl)
  iapply Hcnt
  · ipure_intro; exact ⟨hn0, hnz⟩
  · iexact Hj'

/-- Labeled-rand coupling where both tapes have the wrong bound `M ≠ z`.
Both tapes are unchanged; the draw is uniform and `f` links the values. -/
theorem wp_couple_rand_lbl_rand_lbl_wrong (z M : Int) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (HneM : z ≠ M) (K : Ectx) (E : CoPset) (α α' : Loc)
    (xs ys : List Int) (Φ : Val → IProp GF) :
    iprop(▷ appNatTape α M xs ∗ ▷ specNatTape α' M ys ∗
        (⤇ K.fill (.rand (.lit (.int z)) (.lit (.lbl α')))) ∗
        (∀ (n : Int),
          appNatTape α M xs ∗ specNatTape α' M ys ∗
            (⤇ K.fill (.lit (.int (f n)))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗
          Φ (⟨.lit (.int n), IsVal.lit⟩ : Val)))
      ⊢@{IProp GF} wp E (.rand (.lit (.int z)) (.lit (.lbl α))) Φ := by
  iintro ⟨Hα, Hα', Hj, Hcnt⟩
  have Hv : (Exp.rand (Exp.lit (.int z)) (Exp.lit (.lbl α))).toVal? = none :=
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
  have HheadL : 0 < headStep ⟨Exp.rand (.lit (.int z)) (.lit (.lbl α)), σ₁⟩
        {⟨.lit (.int 0), σ₁⟩} :=
    (headStep_support_iff _ _ _ _).mpr
      (.RandTapeOtherS Hz Hlk_α HneM (_root_.le_refl _) Hz rfl)
  have HredL : Reducible (Exp.rand (.lit (.int z)) (.lit (.lbl α))) σ₁ :=
    Reducible.of_head ⟨_, HheadL⟩
  have HheadR : 0 < headStep ⟨Exp.rand (.lit (.int z)) (.lit (.lbl α')), σ₁'⟩
        {⟨.lit (.int 0), σ₁'⟩} :=
    (headStep_support_iff _ _ _ _).mpr
      (.RandTapeOtherS Hz Hlk_α' HneM (_root_.le_refl _) Hz rfl)
  have HredR_rand : Reducible (Exp.rand (.lit (.int z)) (.lit (.lbl α'))) σ₁' :=
    Reducible.of_head ⟨_, HheadR⟩
  have HredR : Reducible (K.fill (.rand (.lit (.int z)) (.lit (.lbl α')))) σ₁' :=
    HredR_rand.fill K
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  let R : Cfg → Cfg → Prop := fun c₁ c₂ =>
    ∃ n : Int, 0 ≤ n ∧ n < z ∧
      c₁ = ⟨.lit (.int n), σ₁⟩ ∧ c₂ = ⟨K.fill (.lit (.int (f n))), σ₁'⟩
  iexists R, 0, ε
  isplitr; · ipure_intro; rw [zero_add]
  isplitr; · ipure_intro; exact HredL
  isplitr; · ipure_intro; exact HredR
  isplitr
  · ipure_intro
    rw [primStep_rand_lbl_wrong Hz HneM σ₁ α fs Hlk_α]
    have Hv_rand : ¬ (Exp.rand (Exp.lit (.int z)) (Exp.lit (.lbl α'))).isValue := by
      intro ⟨w⟩; nomatch w
    rw [primStep_fill Hv_rand, primStep_rand_lbl_wrong Hz HneM σ₁' α' fs' Hlk_α']
    have Hbase := Cfg.uniform_addCoupl_bij Hz σ₁ σ₁' f hdom hbij
    have : AddCoupl 0
        {p : Cfg × Cfg | R p.1 p.2}
        ((Cfg.uniform z σ₁).map id)
        ((Cfg.uniform z σ₁').map (fun ρ : Cfg => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg))) := by
      refine AddCoupl.map (f := id) (g := fun ρ : Cfg => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg))
        Measurable.of_discrete Measurable.of_discrete
        (R := {p : Cfg × Cfg | R p.1 p.2})
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
    (e3 := K.fill (.lit (.int (f n)))) $$ Hs Hj
  imod HUpd with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  isplitl [Hσ]; · iexact Hσ
  isplitl [Hs']; · iexact Hs'
  isplitl [Hε]; · iexact Hε
  iapply (wp_value_of_toVal (v := ⟨.lit (.int n), IsVal.lit⟩) rfl)
  ihave HαNat := show (α ↪ₐ ⟨M, fs⟩) ⊢@{IProp GF} appNatTape α M xs by
    iintro Hb
    unfold appNatTape
    iexists fs
    isplitr; · ipure_intro; exact hmap_fs
    iexact Hb
  ihave HαNat' := HαNat $$ Hα_b
  ihave Hα'Nat := show (α' ↪ₛ ⟨M, fs'⟩) ⊢@{IProp GF} specNatTape α' M ys by
    iintro Hb
    unfold specNatTape
    iexists fs'
    isplitr; · ipure_intro; exact hmap_fs'
    iexact Hb
  ihave Hα'Nat' := Hα'Nat $$ Hα'_b
  iapply Hcnt
  isplitl [HαNat']; · iexact HαNat'
  isplitl [Hα'Nat']; · iexact Hα'Nat'
  isplitl [Hj']; · iexact Hj'
  ipure_intro; exact ⟨hn0, hnz⟩

/-- Fully labeled two-sided coupling via a bijection `f`, both tapes empty. -/
theorem wp_couple_rand_lbl_rand_lbl (z : Int) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx) (E : CoPset) (α α' : Loc) (Φ : Val → IProp GF) :
    iprop(▷ appNatTape α z [] ∗ ▷ specNatTape α' z [] ∗
        (⤇ K.fill (.rand (.lit (.int z)) (.lit (.lbl α')))) ∗
        (∀ (n : Int),
          appNatTape α z [] ∗ specNatTape α' z [] ∗
            (⤇ K.fill (.lit (.int (f n)))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗
          Φ (⟨.lit (.int n), IsVal.lit⟩ : Val)))
      ⊢@{IProp GF} wp E (.rand (.lit (.int z)) (.lit (.lbl α))) Φ := by
  iintro ⟨Hα, Hα', Hj, Hcnt⟩
  have Hv : (Exp.rand (Exp.lit (.int z)) (Exp.lit (.lbl α))).toVal? = none :=
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
  have HheadL : 0 < headStep ⟨Exp.rand (.lit (.int z)) (.lit (.lbl α)), σ₁⟩
        {⟨.lit (.int 0), σ₁⟩} :=
    (headStep_support_iff _ _ _ _).mpr
      (.RandTapeEmptyS Hz Hlk_α rfl (_root_.le_refl _) Hz rfl)
  have HredL : Reducible (Exp.rand (.lit (.int z)) (.lit (.lbl α))) σ₁ :=
    Reducible.of_head ⟨_, HheadL⟩
  have HheadR : 0 < headStep ⟨Exp.rand (.lit (.int z)) (.lit (.lbl α')), σ₁'⟩
        {⟨.lit (.int 0), σ₁'⟩} :=
    (headStep_support_iff _ _ _ _).mpr
      (.RandTapeEmptyS Hz Hlk_α' rfl (_root_.le_refl _) Hz rfl)
  have HredR_rand : Reducible (Exp.rand (.lit (.int z)) (.lit (.lbl α'))) σ₁' :=
    Reducible.of_head ⟨_, HheadR⟩
  have HredR : Reducible (K.fill (.rand (.lit (.int z)) (.lit (.lbl α')))) σ₁' :=
    HredR_rand.fill K
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  let R : Cfg → Cfg → Prop := fun c₁ c₂ =>
    ∃ n : Int, 0 ≤ n ∧ n < z ∧
      c₁ = ⟨.lit (.int n), σ₁⟩ ∧ c₂ = ⟨K.fill (.lit (.int (f n))), σ₁'⟩
  iexists R, 0, ε
  isplitr; · ipure_intro; rw [zero_add]
  isplitr; · ipure_intro; exact HredL
  isplitr; · ipure_intro; exact HredR
  isplitr
  · ipure_intro
    rw [primStep_rand_lbl_empty Hz σ₁ α Hlk_α]
    have Hv_rand : ¬ (Exp.rand (Exp.lit (.int z)) (Exp.lit (.lbl α'))).isValue := by
      intro ⟨w⟩; nomatch w
    rw [primStep_fill Hv_rand, primStep_rand_lbl_empty Hz σ₁' α' Hlk_α']
    have Hbase := Cfg.uniform_addCoupl_bij Hz σ₁ σ₁' f hdom hbij
    have : AddCoupl 0
        {p : Cfg × Cfg | R p.1 p.2}
        ((Cfg.uniform z σ₁).map id)
        ((Cfg.uniform z σ₁').map (fun ρ : Cfg => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg))) := by
      refine AddCoupl.map (f := id) (g := fun ρ : Cfg => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg))
        Measurable.of_discrete Measurable.of_discrete
        (R := {p : Cfg × Cfg | R p.1 p.2})
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
    (e3 := K.fill (.lit (.int (f n)))) $$ Hs Hj
  imod HUpd with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  isplitl [Hσ]; · iexact Hσ
  isplitl [Hs']; · iexact Hs'
  isplitl [Hε]; · iexact Hε
  iapply (wp_value_of_toVal (v := ⟨.lit (.int n), IsVal.lit⟩) rfl)
  ihave HαNat := show (α ↪ₐ ⟨z, ([] : List _)⟩) ⊢@{IProp GF} appNatTape α z [] by
    iintro Hb
    unfold appNatTape
    iexists ([] : List _)
    isplitr; · ipure_intro; simp
    iexact Hb
  ihave HαNat' := HαNat $$ Hα_b
  ihave Hα'Nat := show (α' ↪ₛ ⟨z, ([] : List _)⟩) ⊢@{IProp GF} specNatTape α' z [] by
    iintro Hb
    unfold specNatTape
    iexists ([] : List _)
    isplitr; · ipure_intro; simp
    iexact Hb
  ihave Hα'Nat' := Hα'Nat $$ Hα'_b
  iapply Hcnt
  isplitl [HαNat']; · iexact HαNat'
  isplitl [Hα'Nat']; · iexact Hα'Nat'
  isplitl [Hj']; · iexact Hj'
  ipure_intro; exact ⟨hn0, hnz⟩

/-! ## Mixed tape-rand couplings -/

theorem wp_couple_tape_rand (z : Int) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx) (E : CoPset) (α : Loc) (Φ : Val → IProp GF) :
    iprop(▷ appNatTape α z [] ∗
        (⤇ K.fill (.rand (.lit (.int z)) (.lit .unit))) ∗
        (∀ (n : Int),
          appNatTape α z [] ∗
            (⤇ K.fill (.lit (.int (f n)))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗
          Φ (⟨.lit (.int n), IsVal.lit⟩ : Val)))
      ⊢@{IProp GF} wp E (.rand (.lit (.int z)) (.lit (.lbl α))) Φ := by
  iintro ⟨Hα, Hj, Hcnt⟩
  have Hv : (Exp.rand (Exp.lit (.int z)) (Exp.lit (.lbl α))).toVal? = none :=
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
  have HheadL : 0 < headStep ⟨Exp.rand (.lit (.int z)) (.lit (.lbl α)), σ₁⟩
        {⟨.lit (.int 0), σ₁⟩} :=
    (headStep_support_iff _ _ _ _).mpr
      (.RandTapeEmptyS Hz Hlk_α rfl (_root_.le_refl _) Hz rfl)
  have HredL : Reducible (Exp.rand (.lit (.int z)) (.lit (.lbl α))) σ₁ :=
    Reducible.of_head ⟨_, HheadL⟩
  have HheadR : 0 < headStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁'⟩
        {⟨.lit (.int 0), σ₁'⟩} :=
    (headStep_support_iff _ _ _ _).mpr (.RandNoTapeS Hz (_root_.le_refl _) Hz)
  have HredR_rand : Reducible (Exp.rand (.lit (.int z)) (.lit .unit)) σ₁' :=
    Reducible.of_head ⟨_, HheadR⟩
  have HredR : Reducible (K.fill (.rand (.lit (.int z)) (.lit .unit))) σ₁' :=
    HredR_rand.fill K
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  let R : Cfg → Cfg → Prop := fun c₁ c₂ =>
    ∃ n : Int, 0 ≤ n ∧ n < z ∧
      c₁ = ⟨.lit (.int n), σ₁⟩ ∧ c₂ = ⟨K.fill (.lit (.int (f n))), σ₁'⟩
  iexists R, 0, ε
  isplitr; · ipure_intro; rw [zero_add]
  isplitr; · ipure_intro; exact HredL
  isplitr; · ipure_intro; exact HredR
  isplitr
  · ipure_intro
    rw [primStep_rand_lbl_empty Hz σ₁ α Hlk_α]
    have Hv_rand : ¬ (Exp.rand (Exp.lit (.int z)) (Exp.lit .unit)).isValue := by
      intro ⟨w⟩; nomatch w
    rw [primStep_fill Hv_rand, primStep_rand_unit Hz]
    have Hbase := Cfg.uniform_addCoupl_bij Hz σ₁ σ₁' f hdom hbij
    have : AddCoupl 0
        {p : Cfg × Cfg | R p.1 p.2}
        ((Cfg.uniform z σ₁).map id)
        ((Cfg.uniform z σ₁').map (fun ρ : Cfg => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg))) := by
      refine AddCoupl.map (f := id) (g := fun ρ : Cfg => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg))
        Measurable.of_discrete Measurable.of_discrete
        (R := {p : Cfg × Cfg | R p.1 p.2})
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
    (e3 := K.fill (.lit (.int (f n)))) $$ Hs Hj
  imod HUpd with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  isplitl [Hσ]; · iexact Hσ
  isplitl [Hs']; · iexact Hs'
  isplitl [Hε]; · iexact Hε
  iapply (wp_value_of_toVal (v := ⟨.lit (.int n), IsVal.lit⟩) rfl)
  ihave HαNat := show (α ↪ₐ ⟨z, ([] : List _)⟩) ⊢@{IProp GF} appNatTape α z [] by
    iintro Hb
    unfold appNatTape
    iexists ([] : List _)
    isplitr; · ipure_intro; simp
    iexact Hb
  ihave HαNat' := HαNat $$ Hα_b
  iapply Hcnt
  isplitl [HαNat']; · iexact HαNat'
  isplitl [Hj']; · iexact Hj'
  ipure_intro; exact ⟨hn0, hnz⟩

/-- Symmetric: couple LHS unit rand with RHS rand on empty tape. -/
theorem wp_couple_rand_tape (z : Int) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx) (E : CoPset) (α' : Loc) (Φ : Val → IProp GF) :
    iprop(▷ specNatTape α' z [] ∗
        (⤇ K.fill (.rand (.lit (.int z)) (.lit (.lbl α')))) ∗
        (∀ (n : Int),
          specNatTape α' z [] ∗
            (⤇ K.fill (.lit (.int (f n)))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗
          Φ (⟨.lit (.int n), IsVal.lit⟩ : Val)))
      ⊢@{IProp GF} wp E (.rand (.lit (.int z)) (.lit .unit)) Φ := by
  iintro ⟨Hα', Hj, Hcnt⟩
  have Hv : (Exp.rand (Exp.lit (.int z)) (Exp.lit .unit)).toVal? = none :=
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
  have HheadL : 0 < headStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁⟩
        {⟨.lit (.int 0), σ₁⟩} :=
    (headStep_support_iff _ _ _ _).mpr (.RandNoTapeS Hz (_root_.le_refl _) Hz)
  have HredL : Reducible (Exp.rand (.lit (.int z)) (.lit .unit)) σ₁ :=
    Reducible.of_head ⟨_, HheadL⟩
  have HheadR : 0 < headStep ⟨Exp.rand (.lit (.int z)) (.lit (.lbl α')), σ₁'⟩
        {⟨.lit (.int 0), σ₁'⟩} :=
    (headStep_support_iff _ _ _ _).mpr
      (.RandTapeEmptyS Hz Hlk_α' rfl (_root_.le_refl _) Hz rfl)
  have HredR_rand : Reducible (Exp.rand (.lit (.int z)) (.lit (.lbl α'))) σ₁' :=
    Reducible.of_head ⟨_, HheadR⟩
  have HredR : Reducible (K.fill (.rand (.lit (.int z)) (.lit (.lbl α')))) σ₁' :=
    HredR_rand.fill K
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  let R : Cfg → Cfg → Prop := fun c₁ c₂ =>
    ∃ n : Int, 0 ≤ n ∧ n < z ∧
      c₁ = ⟨.lit (.int n), σ₁⟩ ∧ c₂ = ⟨K.fill (.lit (.int (f n))), σ₁'⟩
  iexists R, 0, ε
  isplitr; · ipure_intro; rw [zero_add]
  isplitr; · ipure_intro; exact HredL
  isplitr; · ipure_intro; exact HredR
  isplitr
  · ipure_intro
    rw [primStep_rand_unit Hz]
    have Hv_rand : ¬ (Exp.rand (Exp.lit (.int z)) (Exp.lit (.lbl α'))).isValue := by
      intro ⟨w⟩; nomatch w
    rw [primStep_fill Hv_rand, primStep_rand_lbl_empty Hz σ₁' α' Hlk_α']
    have Hbase := Cfg.uniform_addCoupl_bij Hz σ₁ σ₁' f hdom hbij
    have : AddCoupl 0
        {p : Cfg × Cfg | R p.1 p.2}
        ((Cfg.uniform z σ₁).map id)
        ((Cfg.uniform z σ₁').map (fun ρ : Cfg => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg))) := by
      refine AddCoupl.map (f := id) (g := fun ρ : Cfg => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg))
        Measurable.of_discrete Measurable.of_discrete
        (R := {p : Cfg × Cfg | R p.1 p.2})
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
    (e3 := K.fill (.lit (.int (f n)))) $$ Hs Hj
  imod HUpd with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  isplitl [Hσ]; · iexact Hσ
  isplitl [Hs']; · iexact Hs'
  isplitl [Hε]; · iexact Hε
  iapply (wp_value_of_toVal (v := ⟨.lit (.int n), IsVal.lit⟩) rfl)
  ihave Hα'Nat := show (α' ↪ₛ ⟨z, ([] : List _)⟩) ⊢@{IProp GF} specNatTape α' z [] by
    iintro Hb
    unfold specNatTape
    iexists ([] : List _)
    isplitr; · ipure_intro; simp
    iexact Hb
  ihave Hα'Nat' := Hα'Nat $$ Hα'_b
  iapply Hcnt
  isplitl [Hα'Nat']; · iexact Hα'Nat'
  isplitl [Hj']; · iexact Hj'
  ipure_intro; exact ⟨hn0, hnz⟩

end CouplingRules

end ProbLang
