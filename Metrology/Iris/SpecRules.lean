module

public import Metrology.Iris.SpecUpdate
public import Metrology.ProbLang.DetStep

@[expose] public section

/-! # Spec-side stepping rules -/

open Std Iris Iris.Std Iris.BI COFE ProbLang



namespace ProbLang


variable {rT : Type _} [ProbLangℝ rT]

/-! ## Bridge: `DetStep_discrete` ⇒ `pexecN 1 ρ = MeasureTheory.Measure.dirac ρ'` -/

-- TODO: Move me to Measure.lean
/-- A sub-probability measure on a countable discrete space with singleton mass
1 at `a` is the Dirac at `a`. -/
theorem Measure.eq_dirac_of_singleton_mass_one {α : Type _}
    [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    {μ : MeasureTheory.Measure α} {a : α} (hmass : μ {a} = 1) (htot : μ .univ ≤ 1) :
    μ = MeasureTheory.Measure.dirac a := by
  refine MeasureTheory.Measure.ext fun s hs => ?_
  -- μ.univ = 1 (sandwich) and μ {a}ᶜ = 0 (mass conservation), so μ s = μ (s ∩ {a}).
  have hsingle : μ {a} ≤ μ .univ := MeasureTheory.measure_mono (Set.subset_univ _)
  have huniv : μ .univ = 1 := _root_.le_antisymm htot (hmass ▸ hsingle)
  have hcompl : μ ({a}ᶜ) = 0 := by
    have hAdd : μ {a} + μ ({a}ᶜ) = μ .univ :=
      MeasureTheory.measure_add_measure_compl (measurableSet_singleton a)
    have hbnd : μ {a} + μ ({a}ᶜ) ≤ μ {a} + 0 := by
      rw [hAdd, huniv, add_zero]; exact hmass.symm.le
    refine _root_.le_antisymm ?_ (zero_le)
    exact ENNReal.le_of_add_le_add_left (hmass ▸ ENNReal.one_ne_top) hbnd
  by_cases ha : a ∈ s
  · rw [MeasureTheory.Measure.dirac_apply_of_mem ha]
    have hsplit : μ s = μ (s ∩ {a}) + μ (s ∩ {a}ᶜ) := by
      rw [← MeasureTheory.measure_inter_add_diff s (measurableSet_singleton _)]; rfl
    have hzero : μ (s ∩ {a}ᶜ) = 0 :=
      MeasureTheory.measure_mono_null Set.inter_subset_right hcompl
    have hinter : s ∩ {a} = {a} :=
      Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr ha)
    rw [hsplit, hinter, hzero, hmass, add_zero]
  · rw [MeasureTheory.Measure.dirac_apply' _ hs, Set.indicator_of_notMem ha]
    refine MeasureTheory.measure_mono_null ?_ hcompl
    intro x hx hxa
    exact ha (by simpa using hxa ▸ hx)


/-- One-step deterministic advance: `DetStep_discrete ρ ρ'` gives `pexecN 1 ρ = dirac ρ'`. -/
@[discrete] -- pexecN_1_of_DetStep_cts
theorem pexecN_1_of_DetStep [Countable rT] [MeasurableSingletonClass rT]
    {ρ ρ' : Cfg rT} (h : DetStep_discrete ρ ρ') :
    pexecN 1 ρ = MeasureTheory.Measure.dirac ρ' := by
  rw [pexecN_one]
  have hnv : ¬ ρ.expr.isValue := by
    obtain ⟨_, hpos⟩ := h.safe
    obtain ⟨_, _⟩ := ρ
    exact Discrete.val_stuck hpos
  rw [stepOrFinal_not_isValue hnv]
  exact Measure.eq_dirac_of_singleton_mass_one h.det (primStep_univ_le_one ρ)

/-- One-step deterministic advance: `DetStep_discrete ρ ρ'` gives `pexecN 1 ρ = dirac ρ'`. -/
theorem pexecN_1_of_DetStep_cts {ρ ρ' : Cfg rT} (h : DetStep ρ ρ') :
    pexecN 1 ρ = MeasureTheory.Measure.dirac ρ' := by
  rw [pexecN_one]
  rcases h with ⟨h1, h2⟩
  have hnv : ¬ ρ.expr.isValue := by
    refine val_stuck (σ := ρ.2) ?_
    simp [h2]
  rw [stepOrFinal_not_isValue hnv]
  exact h2

/-- `n`-step version: `DetExec_discrete n ρ ρ'` gives `pexecN n ρ = dirac ρ'`. -/
theorem pexecN_of_DetExec [Countable rT] [MeasurableSingletonClass rT]
    {n : ℕ} {ρ ρ' : Cfg rT} (h : DetExec_discrete n ρ ρ') :
    pexecN n ρ = MeasureTheory.Measure.dirac ρ' := by
  induction n generalizing ρ with
  | zero =>
    obtain ⟨⟨rfl⟩⟩ := h.det_exec; rfl
  | succ k ih =>
    obtain ⟨ρmid, hstep, hrest⟩ := h.det_exec
    rw [show k + 1 = 1 + k from Nat.add_comm _ _, pexecN_plus,
        pexecN_1_of_DetStep hstep,
        MeasureTheory.Measure.dirac_bind Measurable.of_discrete,
        ih ⟨hrest⟩]


/-- `nsteps PureStep_discrete n e1 e2` at a fixed state gives `DetExec_discrete n ⟨e1,σ⟩ ⟨e2,σ⟩`. -/
theorem DetExec_discrete.of_nsteps_PureStep {n : ℕ} {e1 e2 : Exp rT} (σ : State rT)
    (h : nsteps PureStep_discrete n e1 e2) :
    DetExec_discrete n ⟨e1, σ⟩ ⟨e2, σ⟩ := by
  induction n generalizing e1 with
  | zero => simp [nsteps] at h; subst h; exact ⟨rfl⟩
  | succ k ih =>
    obtain ⟨c, hstep, hrest⟩ := h
    exact (ih hrest).succ ⟨hstep.safe σ, hstep.det σ⟩

/-- `PureExec_discrete φ n e1 e2 + φ` gives `pexecN n ⟨e1,σ⟩ = dirac ⟨e2,σ⟩`. -/
theorem pexecN_of_PureExec [Countable rT] [MeasurableSingletonClass rT] {φ : Prop} {n : ℕ} {e1 e2 : Exp rT}
    [h : PureExec_discrete φ n e1 e2] (σ : State rT) (hφ : φ) :
    pexecN n ⟨e1, σ⟩ = MeasureTheory.Measure.dirac ⟨e2, σ⟩ :=
  pexecN_of_DetExec (DetExec_discrete.of_nsteps_PureStep σ (h.pure_exec hφ))

/-- Bridge: `ExtTreeMap.insert` and `PartialMap.insert` agree extensionally. -/
theorem ExtTreeMap.insert_eq_PartialMap_insert {V : Type _}
    (h : LocHeap V) (l : Loc) (v : V) :
    h.insert l v = PartialMap.insert h l v :=
  ExtTreeMap.ext_getElem? fun k => by
    show (h.insert l v)[k]? = (h.alter l (fun _ => some v))[k]?
    simp [ExtTreeMap.getElem?_insert, ExtTreeMap.getElem?_alter]

/-! ## Per-redex `DetHeadStep_discrete` lemmas (tape-flavored)

The heap variants `DetHeadStep_discrete.alloc`/`load`/`store` already live in `DetStep_discrete.lean`.
The two below are tape-specific and used by `step_alloctape` / `step_rand`. -/

/-- Tape allocation: `tape #z` deterministically allocates a fresh empty tape of
bound `z`. -/
theorem DetHeadStep_discrete.tape {z : Int} (σ : State rT) :
    DetHeadStep_discrete ⟨.tape (.lit (.int z)), σ⟩
      ⟨.lit (.lbl σ.tapes.fresh),
       σ.update_tapes (·.insert σ.tapes.fresh (Tape.empty z))⟩ :=
  .of_det_discrete _ _ (by simp [headStep])

/-- Tape rand: with `σ.tapes[α] = some ⟨z, n :: ns⟩`, the random sample
`rand z α` deterministically returns `n` and pops the head. -/
theorem DetHeadStep_discrete.rand_tape {z : Int} (l : Loc)
    (n : { k : Int // 0 ≤ k ∧ k < z }) (ns : List { k : Int // 0 ≤ k ∧ k < z })
    {σ : State rT} (htape : σ.tapes[l]? = some ⟨z, n :: ns⟩) :
    DetHeadStep_discrete ⟨.rand (.lit (.int z)) (.lit (.lbl l)), σ⟩
      ⟨.lit (.int n), σ.update_tapes (·.insert l ⟨z, ns⟩)⟩ :=
  .of_det_discrete _ _ (by simp [headStep, htape])

/-! ## Stepping rules over the `Cfg.specAuth` interpretation. -/

section Rules

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] [SpecGS rT GF]
variable [Countable rT] [MeasurableSingletonClass rT]

/-- Pure reduction under an evaluation context. -/
theorem step_pure {E : CoPset} (K : Ectx rT) {e e' : Exp rT} {φ : Prop} {n : ℕ}
    (Hφ : φ) [Hex : PureExec_discrete φ n e e'] :
    ⤇ (K.fill e) ⊢@{IProp GF} specUpdate rT E (⤇ (K.fill e')) := by
  have HexK : PureExec_discrete φ n (K.fill e) (K.fill e') := PureExec_discrete.fill K
  iintro HK
  unfold specUpdate
  iintro %ρ Hρ
  obtain ⟨_, σ⟩ := ρ
  ihave %Heq := specAuth_specFrag_agree (GF := GF) $$ Hρ HK
  subst Heq
  imod specProg_update $$ Hρ HK with ⟨HρNew, HKNew⟩
  imodintro
  iexists ⟨K.fill e', σ⟩, n
  isplitr
  · ipureintro; exact pexecN_of_PureExec (h := HexK) σ Hφ
  isplitl [HρNew] <;> iassumption

/-- Allocation under an evaluation context. -/
theorem step_alloc {E : CoPset} (K : Ectx rT) {v : Exp rT} (hv : IsVal v) :
    ⤇ (K.fill (.alloc v)) ⊢@{IProp GF}
      specUpdate rT E iprop(∃ (l : Loc), (⤇ (K.fill (.lit (.loc l)))) ∗ (l ↦ₛ ⟨v, hv⟩)) := by
  iintro HK
  unfold specUpdate
  iintro %ρ Hρ
  obtain ⟨_, σ⟩ := ρ
  ihave %Heq := specAuth_specFrag_agree (GF := GF) $$ Hρ HK
  subst Heq
  set l := σ.heap.fresh with hl
  set σ' := σ.update_heap (fun h : LocHeap (Val rT) => PartialMap.insert h l ⟨v, hv⟩)
    with hσ'
  imod specProg_update (e3 := K.fill (.lit (.loc l))) $$ Hρ HK with ⟨HρNew, HKNew⟩
  ihave HAlloc := spec_auth_heap_alloc (v := ⟨v, hv⟩) (GF := GF)
    (e := K.fill (.lit (.loc l))) $$ HρNew
  imod HAlloc with ⟨HρFinal, Hl⟩
  imodintro
  iexists ⟨K.fill (.lit (.loc l)), σ'⟩, 1
  isplitr
  · ipureintro
    refine pexecN_1_of_DetStep ?_
    have hstate_eq :
        σ.update_heap (·.insert σ.heap.fresh ⟨v, hv⟩) = σ' := by
      simp [hσ', State.update_heap, ExtTreeMap.insert_eq_PartialMap_insert, hl]
    rw [← hstate_eq]
    exact ((DetHeadStep_discrete.alloc hv σ).toDetStep).fill K
  isplitl [HρFinal]
  · iassumption
  iexists σ.heap.fresh
  isplitl [HKNew] <;> iassumption

/-- Heap load under an evaluation context. -/
theorem step_load {E : CoPset} (K : Ectx rT) {l : Loc} {v : Val rT} :
    iprop((⤇ (K.fill (.load (.lit (.loc l))))) ∗ (l ↦ₛ v)) ⊢@{IProp GF}
      specUpdate rT E iprop((⤇ (K.fill (Exp.ofVal v))) ∗ (l ↦ₛ v)) := by
  iintro ⟨HK, Hl⟩
  unfold specUpdate
  iintro %ρ Hρ
  obtain ⟨_, σ⟩ := ρ
  ihave %Heq := specAuth_specFrag_agree (GF := GF) $$ Hρ HK
  subst Heq
  ihave %Hlk := spec_auth_lookup_heap (GF := GF) $$ Hρ Hl
  imod specProg_update (e3 := K.fill (Exp.ofVal v)) $$ Hρ HK with ⟨HρNew, HKNew⟩
  imodintro
  iexists ⟨K.fill (Exp.ofVal v), σ⟩, 1
  isplitr
  · ipureintro
    exact pexecN_1_of_DetStep (((DetHeadStep_discrete.load σ Hlk).toDetStep).fill K)
  isplitl [HρNew]
  · iassumption
  isplitl [HKNew] <;> iassumption

/-- Heap store under an evaluation context. -/
theorem step_store {E : CoPset} (K : Ectx rT) {l : Loc} {e : Exp rT} {v_old v_new : Val rT}
    (hv : IsVal e) (hnew : e.toVal? = some v_new) :
    iprop((⤇ (K.fill (.store (.lit (.loc l)) e))) ∗ (l ↦ₛ v_old)) ⊢@{IProp GF}
      specUpdate rT E iprop((⤇ (K.fill (.lit .unit))) ∗ (l ↦ₛ v_new)) := by
  iintro ⟨HK, Hl⟩
  unfold specUpdate
  iintro %ρ Hρ
  obtain ⟨_, σ⟩ := ρ
  ihave %Heq := specAuth_specFrag_agree (GF := GF) $$ Hρ HK
  subst Heq
  ihave %Hlk := spec_auth_lookup_heap (GF := GF) $$ Hρ Hl
  set σ' := σ.update_heap (fun h : LocHeap (Val rT) => PartialMap.insert h l v_new)
    with hσ'
  imod specProg_update (e3 := K.fill (.lit .unit)) $$ Hρ HK with ⟨HρNew, HKNew⟩
  ihave HUpd := spec_auth_update_heap (GF := GF) (e := K.fill (.lit .unit))
    (l := l) (v := v_old) (w := v_new) $$ HρNew Hl
  imod HUpd with ⟨HρFinal, _Hl⟩
  imodintro
  iexists ⟨K.fill (.lit .unit), σ'⟩, 1
  isplitr
  · ipureintro
    refine pexecN_1_of_DetStep ?_
    have hstate_eq : σ.update_heap (·.insert l v_new) = σ' := by
      simp [hσ', State.update_heap, ExtTreeMap.insert_eq_PartialMap_insert]
    rw [← hstate_eq]
    exact ((DetHeadStep_discrete.store hv σ Hlk hnew).toDetStep).fill K
  isplitl [HρFinal]
  · iassumption
  isplitl [HKNew] <;> iassumption

/-- Allocate a tape under an evaluation context. -/
theorem step_alloctape {E : CoPset} (K : Ectx rT) (z : Int) :
    ⤇ (K.fill (.tape (.lit (.int z)))) ⊢@{IProp GF}
      specUpdate rT E iprop(∃ (l : Loc),
        (⤇ (K.fill (.lit (.lbl l)))) ∗ (l ↪ₛ Tape.empty z)) := by
  iintro HK
  unfold specUpdate
  iintro %ρ Hρ
  obtain ⟨_, σ⟩ := ρ
  ihave %Heq := specAuth_specFrag_agree (GF := GF) $$ Hρ HK
  subst Heq
  set l := σ.tapes.fresh with hl
  set σ' := σ.update_tapes (fun h : LocHeap Tape => PartialMap.insert h l (Tape.empty z))
    with hσ'
  imod specProg_update (e3 := K.fill (.lit (.lbl l))) $$ Hρ HK with ⟨HρNew, HKNew⟩
  ihave HAlloc := spec_auth_tape_alloc (t := Tape.empty z) (GF := GF)
    (e := K.fill (.lit (.lbl l))) $$ HρNew
  imod HAlloc with ⟨HρFinal, Hl⟩
  imodintro
  iexists ⟨K.fill (.lit (.lbl l)), σ'⟩, 1
  isplitr
  · ipureintro
    refine pexecN_1_of_DetStep ?_
    have hstate_eq :
        σ.update_tapes (·.insert σ.tapes.fresh (Tape.empty z)) = σ' := by
      simp [hσ', State.update_tapes, ExtTreeMap.insert_eq_PartialMap_insert, hl]
    rw [← hstate_eq]
    exact ((DetHeadStep_discrete.tape σ).toDetStep).fill K
  isplitl [HρFinal]
  · iassumption
  iexists σ.tapes.fresh
  isplitl [HKNew] <;> iassumption

/-- Read from a non-empty tape under an evaluation context. -/
theorem step_rand {E : CoPset} (K : Ectx rT) {z : Int} (l : Loc)
    (n : { k : Int // 0 ≤ k ∧ k < z }) (ns : List { k : Int // 0 ≤ k ∧ k < z }) :
    iprop((⤇ (K.fill (.rand (.lit (.int z)) (.lit (.lbl l))))) ∗ (l ↪ₛ ⟨z, n :: ns⟩))
        ⊢@{IProp GF}
      specUpdate rT E iprop((⤇ (K.fill (.lit (.int n)))) ∗ (l ↪ₛ ⟨z, ns⟩)) := by
  iintro ⟨HK, Hl⟩
  unfold specUpdate
  iintro %ρ Hρ
  obtain ⟨_, σ⟩ := ρ
  ihave %Heq := specAuth_specFrag_agree (GF := GF) $$ Hρ HK
  subst Heq
  ihave %Hlk := spec_auth_lookup_tape (GF := GF) $$ Hρ Hl
  set σ' := σ.update_tapes (fun h : LocHeap Tape => PartialMap.insert h l ⟨z, ns⟩)
    with hσ'
  imod specProg_update (e3 := K.fill (.lit (.int n))) $$ Hρ HK with ⟨HρNew, HKNew⟩
  ihave HUpd := spec_auth_update_tape (GF := GF) (e := K.fill (.lit (.int n)))
    (l := l) (t := ⟨z, n :: ns⟩) (s := ⟨z, ns⟩) $$ HρNew Hl
  imod HUpd with ⟨HρFinal, _Hl⟩
  imodintro
  iexists ⟨K.fill (.lit (.int n)), σ'⟩, 1
  isplitr
  · ipureintro
    refine pexecN_1_of_DetStep ?_
    have hstate_eq : σ.update_tapes (·.insert l ⟨z, ns⟩) = σ' := by
      simp [hσ', State.update_tapes, ExtTreeMap.insert_eq_PartialMap_insert]
    rw [← hstate_eq]
    exact ((DetHeadStep_discrete.rand_tape l n ns Hlk).toDetStep).fill K
  isplitl [HρFinal]
  · iassumption
  isplitl [HKNew] <;> iassumption

end Rules

end ProbLang
