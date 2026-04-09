import Metrology.ProbLang.Syntax.Syntax
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Distributions.Uniform

noncomputable section

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace ProbLang

def Option.unwrapM {α : Type _} [MeasurableSpace β] (f : α → Measure β) : Option α → Measure β
| some v => f v
| none => 0

@[simp]
def Exp.asValM [MeasurableSpace T] (e : Exp) (f : Val → Measure T) : Measure T :=
  match e.toVal? with | none => 0 | some v => f v

def Exp.isValM [MeasurableSpace T] (e : Exp) (m : Measure T) : Measure T :=
  if e.isValue then m else 0

@[simp] theorem Exp.isValM_some [MeasurableSpace T] {e : Exp} {m : Measure T} (He : e.isValue) :
    e.isValM m = m := if_pos He

theorem Exp.isValM_some' [MeasurableSpace T] {e : Exp} {m : Measure T} (w : IsVal e) :
    e.isValM m = m := isValM_some w.toIsValue

@[simp] theorem Exp.isValM_none [MeasurableSpace T] {e : Exp} {m : Measure T} (He : ¬ e.isValue) :
    e.isValM m = 0 := if_neg He

def Int.isPos (z : Int) : Option { z : Int // 0 < z } :=
  if H : 0 < z then some ⟨z, H⟩ else none

instance : MeasurableSpace Exp := ⊤
instance : MeasurableSpace State := ⊤
instance : MeasurableSpace Val := ⊤
instance : MeasurableSpace Cfg := ⊤

def Cfg.uniform (z : Int) (σ : State) : Measure Cfg :=
  z.isPos.unwrapM fun ⟨z, Hz⟩ =>
  PMF.uniformOfFinset (.Icc 0 z) (Finset.nonempty_Icc.mpr <| Int.le_of_lt Hz)
    |>.toMeasure.map (⟨.lit <| .int ·, σ⟩)

-- TODO: What if we change Cfg to Option (Exp × State)?
-- NB. Rand is currently off-by-one from Eris. I'm going to see if sticking `by grind`
-- as a default term everywhere will solve all the positvity side conditions.
-- TODO: Do we need these value checks? Finding the redex, and enforcing evalutation
-- order, should be governed by the reduction context.
def headStep : Cfg → Measure Cfg
| ⟨.app (.letrec f x e1) e2, σ⟩ =>
  e2.isValM <|
  dirac ⟨Exp.subst x e2 (Exp.subst f (.letrec f x e1) e1), σ⟩
| ⟨.unop op e, σ⟩ =>
  e.isValM <|
  (op.eval e).unwrapM <|
  (dirac ⟨·, σ⟩)
| ⟨.binop op e1 e2, σ⟩ =>
  e1.isValM <|
  e2.isValM <|
  (op.eval e1 e2).unwrapM <|
  (dirac ⟨·, σ⟩)
| ⟨.cond (.lit (.bool true)) et _, σ⟩ => dirac ⟨et, σ⟩
| ⟨.cond (.lit (.bool false)) _ ef, σ⟩ => dirac ⟨ef, σ⟩
| ⟨.fst (.pair e1 e2), σ⟩ => e1.isValM <| e2.isValM <| (dirac ⟨e1, σ⟩)
| ⟨.snd (.pair e1 e2), σ⟩ => e1.isValM <| e2.isValM <| (dirac ⟨e2, σ⟩)
| ⟨.case (.inl e) el _, σ⟩ => e.isValM <| (dirac ⟨el.app e, σ⟩)
| ⟨.case (.inr e) _ er, σ⟩ => e.isValM <| (dirac ⟨er.app e, σ⟩)
| ⟨.alloc ed, σ⟩ =>
  ed.asValM fun vd =>
  let ℓ := σ.heap.fresh
  dirac ⟨.lit <| .loc ℓ, σ.update_heap fun t => t.insert ℓ vd⟩
| ⟨.load (.lit (.loc ℓ)), σ⟩ =>
  match σ.heap[ℓ]? with | none => 0 | some v => (dirac ⟨.ofVal v, σ⟩)
| ⟨.store (.lit (.loc ℓ)) e, σ⟩ =>
  e.asValM fun v =>
  match σ.heap[ℓ]? with | none => 0 | some _ => dirac ⟨.lit .unit, σ.update_heap fun t => t.insert ℓ v⟩
| ⟨.rand (.lit (.int z)) (.lit .unit), σ⟩ => Cfg.uniform z σ
| ⟨.tape (.lit (.int z)), σ⟩ =>
  let α := σ.tapes.fresh
  dirac ⟨.lit <| .lbl α, σ.update_tapes fun t => t.insert α (.empty z)⟩
| ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩ =>
  match σ.tapes[α]? with
  | none => 0
  | some ⟨M, ns⟩ =>
    if M = z
      then
        match ns with
        | [] => Cfg.uniform z σ
        | n :: ns => dirac ⟨.lit <| .int n, σ.update_tapes fun t => t.insert α ⟨M, ns⟩⟩
      else Cfg.uniform z σ
| ⟨.scrut e p, σ⟩ =>
  e.isValM <|
  match Pat.tryMatch p e with
  | some bindings => dirac ⟨.inl bindings, σ⟩
  | none => dirac ⟨.inr (.lit .unit), σ⟩
| ⟨.annot _ e, σ⟩ =>
  e.isValM <|
  dirac ⟨e, σ⟩
| _ => 0

elab "rename_goal" name:ident : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.setUserName name.getId

/-- Split the headStep cases, but with informative goal names. -/
macro "head_case_names" : tactic =>
  `(tactic| (
    unfold headStep
    split
    on_goal 1  => rename_goal beta
    on_goal 2  => rename_goal unop
    on_goal 3  => rename_goal binop
    on_goal 4  => rename_goal cond.true
    on_goal 5  => rename_goal cond.false
    on_goal 6  => rename_goal fst
    on_goal 7  => rename_goal snd
    on_goal 8  => rename_goal case.left
    on_goal 9  => rename_goal case.right
    on_goal 10 => rename_goal alloc
    on_goal 11 => rename_goal load
    on_goal 12 => rename_goal store
    on_goal 13 => rename_goal rand.plain
    on_goal 14 => rename_goal tape
    on_goal 15 => rename_goal rand.tape
    on_goal 16 => rename_goal scrut
    on_goal 17 => rename_goal annot
    on_goal 18 => rename_goal default
  ))

/-- Decompose the Cfg equality hypothesis left by `split` on `headStep`, then substitute. -/
macro "head_subst" : tactic =>
  `(tactic| (rename_i h_eq
             have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
             subst_eqs))

/-- Unfold `isValM`, split into redex/no_redex, and name goals.
    Goal order after `split` on `if`: goal 1 = true (redex), goal 2 = false (no_redex). -/
macro "head_split_isValM" redex:ident no_redex:ident : tactic =>
  `(tactic| (unfold Exp.isValM; split
             on_goal 2 => rename_goal $no_redex
             on_goal 1 => rename_goal $redex))

/-- Unfold `asValM`, split into no_redex/redex, and name goals.
    Goal order after `split` on `match toVal?`: goal 1 = none (no_redex), goal 2 = some (redex). -/
macro "head_split_asValM" no_redex:ident redex:ident : tactic =>
  `(tactic| (unfold Exp.asValM; split
             on_goal 1 => rename_goal $no_redex
             on_goal 2 => rename_goal $redex))

/-- Split a binary match (e.g. heap lookup) and name the two goals. -/
macro "head_split2" goal1:ident goal2:ident : tactic =>
  `(tactic| (split
             on_goal 1 => rename_goal $goal1
             on_goal 2 => rename_goal $goal2))

macro "head_case" : tactic =>
  `(tactic| (
    head_case_names
    case' rand.tape =>
      head_subst
      head_split2 rand.tape.unalloc rand_tape_alloc
      case' rand_tape_alloc =>
        split
        on_goal 2 => rename_goal rand.tape.mismatch
        on_goal 1 =>
          subst_eqs
          head_split2 rand.tape.empty rand.tape.deterministic
    case' tape       => head_subst
    case' rand.plain => head_subst
    case' store =>
      head_subst
      unfold Exp.asValM; split
      on_goal 1 => rename_goal store.no_redex
      on_goal 2 => head_split2 store.segfault store.redex
    case' load =>
      head_subst
      head_split2 load.segfault load.redex
    case' alloc =>
      head_subst
      head_split_asValM alloc.no_redex alloc.redex
    case' case.right =>
      head_subst
      head_split_isValM case.right.redex case.right.no_redex
    case' case.left =>
      head_subst
      head_split_isValM case.left.redex case.left.no_redex
    case' snd =>
      head_subst
      unfold Exp.isValM; split
      on_goal 2 => rename_goal snd.no_redex_1
      on_goal 1 => head_split2 snd.redex snd.no_redex_2
    case' fst =>
      head_subst
      unfold Exp.isValM; split
      on_goal 2 => rename_goal fst.no_redex_1
      on_goal 1 => head_split2 fst.redex fst.no_redex_2
    case' cond.false => head_subst
    case' cond.true  => head_subst
    case' binop =>
      head_subst
      unfold Exp.isValM; split
      on_goal 2 => rename_goal binop.no_redex_1
      on_goal 1 => head_split2 binop.redex binop.no_redex_2
    case' unop =>
      head_subst
      head_split_isValM unop.redex unop.no_redex
    case' annot =>
      head_subst
      head_split_isValM annot.redex annot.no_redex
    case' scrut =>
      head_subst
      unfold Exp.isValM; split
      on_goal 2 => rename_goal scrut_no_redex
      on_goal 1 =>
        head_split2 scrut_success scrut_failure
    case' beta =>
      head_subst
      head_split_isValM beta.redex beta.no_redex
  ))

def headStepKernel : Kernel Cfg Cfg where
  measurable' := .of_discrete
  toFun := headStep

theorem val_head_stuck : 0 < headStep ⟨e, σ⟩ {ρ} → ¬e.isValue := by
  head_case <;> simp [Exp.isValue_iff_isValueR]

theorem Exp.toVal?_isValue {e : Exp} : e.toVal? = some v → e.isValue := by
  intro h; by_contra hne; rw [Exp.toVal?_eq_none.mpr hne] at h; exact absurd h (by simp)

theorem head_ctx_step_val {Ki : EctxItem} :
    0 < headStep ⟨Ki.fillItem e, σ⟩ {ρ} → e.isValue := by
  have Hzero : 0 < (0 : Measure Cfg) {ρ} → False := by simp
  head_case
  all_goals try (exact fun H => (Hzero H).elim)
  all_goals cases Ki <;> (intro _; simp_all [EctxItem.fillItem, Exp.isValue_iff_isValueR])
  all_goals exact (Exp.isValue_iff_isValueR.mp (Exp.toVal?_isValue ‹_›))

inductive HeadStepSupport : Cfg → Cfg → Prop
| BetaS :
  e2.isValue →
  e' = Exp.subst x e2 (Exp.subst f (.letrec f x e1) e1) →
  HeadStepSupport ⟨.app (.letrec f x e1) e2, σ⟩ ⟨e', σ⟩
| UnOpS :
  e.isValue →
  some e' = op.eval e →
  HeadStepSupport ⟨.unop op e, σ⟩ ⟨e', σ⟩
| BinOpS :
  e1.isValue →
  e2.isValue →
  some e' = op.eval e1 e2 →
  HeadStepSupport ⟨.binop op e1 e2, σ⟩ ⟨e', σ⟩
| IfTrueS :
  HeadStepSupport ⟨.cond (.lit (.bool true)) et _, σ⟩ ⟨et, σ⟩
| IfFalseS :
  HeadStepSupport ⟨.cond (.lit (.bool false)) _ ef, σ⟩ ⟨ef, σ⟩
| FstS :
  e1.isValue →
  e2.isValue →
  HeadStepSupport ⟨.fst (.pair e1 e2), σ⟩ ⟨e1, σ⟩
| SndS :
  e1.isValue →
  e2.isValue →
  HeadStepSupport ⟨.snd (.pair e1 e2), σ⟩ ⟨e2, σ⟩
| CaseLS :
  e.isValue →
  HeadStepSupport ⟨.case (.inl e) el er, σ⟩ ⟨el.app e, σ⟩
| CaseRS :
  e.isValue →
  HeadStepSupport ⟨.case (.inr e) el er, σ⟩ ⟨er.app e, σ⟩
| AllocS :
  ed.toVal? = some vd →
  ℓ = σ.heap.fresh →
  σ' = σ.update_heap (·.insert ℓ vd) →
  HeadStepSupport ⟨.alloc ed, σ⟩ ⟨.lit (.loc ℓ), σ'⟩
| LoadS :
  σ.heap[ℓ]? = some v →
  e' = Exp.ofVal v →
  HeadStepSupport ⟨.load (.lit (.loc ℓ)), σ⟩ ⟨e', σ⟩
| StoreS :
  e.toVal? = some v →
  σ.heap[ℓ]?.isSome →
  σ' = σ.update_heap (·.insert ℓ v) →
  HeadStepSupport ⟨.store (.lit (.loc ℓ)) e, σ⟩ ⟨.lit .unit, σ'⟩
| RandNoTapeS :
  0 < z →
  0 ≤ v →
  v ≤ z →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit .unit), σ⟩ ⟨.lit (.int v), σ⟩
| TapeS :
  ℓ = σ.tapes.fresh →
  σ' = σ.update_tapes (·.insert ℓ (.empty z)) →
  HeadStepSupport ⟨.tape (.lit (.int z)), σ⟩ ⟨.lit (.lbl ℓ), σ'⟩
| RandTapeS :
  0 < z →
  σ.tapes[α]? = some ⟨N, nn :: ns⟩ →
  z = N →
  v = nn.1 →
  σ' = σ.update_tapes (·.insert α ⟨N, ns⟩) →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩ ⟨.lit (.int v), σ'⟩
| RandTapeEmptyS :
  0 < z →
  σ.tapes[α]? = some ⟨N, []⟩ →
  z = N →
  0 ≤ v →
  v ≤ z →
  σ' = σ →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩ ⟨.lit (.int v), σ'⟩
| RandTapeOtherS :
  0 < z →
  σ.tapes[α]? = some ⟨N, L⟩ →
  z ≠ N →
  0 ≤ v →
  v ≤ z →
  σ' = σ →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩ ⟨.lit (.int v), σ'⟩
| ScrutSuccessS :
  e.isValue →
  Pat.tryMatch p e = some bindings →
  HeadStepSupport ⟨.scrut e p, σ⟩ ⟨.inl bindings, σ⟩
| ScrutFailureS :
  e.isValue →
  Pat.tryMatch p e = none →
  HeadStepSupport ⟨.scrut e p, σ⟩ ⟨.inr (.lit .unit), σ⟩
| AnnotS :
  e.isValue →
  HeadStepSupport ⟨.annot a e, σ⟩ ⟨e, σ⟩

@[simp]
theorem dirac_singleton_pos {a b : Cfg} :
    0 < (dirac a) {b} ↔ a = b := by
  constructor
  · rw [dirac_apply' a .of_discrete, Set.indicator_singleton, Pi.single, Function.update]
    split <;> simp; trivial
  · simp_all [dirac_apply_of_mem (Set.mem_singleton _)]

@[simp]
theorem isValM_singleton_pos [MeasurableSpace T] {e : Exp} {m : Measure T} {s : Set T} :
    0 < (e.isValM m) s ↔ e.isValue ∧ 0 < m s := by
  simp only [Exp.isValM]
  by_cases He : e.isValue
  · rw [if_pos He]; exact ⟨fun h => ⟨He, h⟩, And.right⟩
  · rw [if_neg He]; exact ⟨fun h => absurd h (by simp), fun ⟨hv, _⟩ => absurd hv He⟩

@[simp]
theorem unwrapM_singleton_pos {α β : Type _} [MeasurableSpace β]
    {f : α → Measure β} {opt : Option α} {s : Set β} :
    0 < (opt.unwrapM f) s ↔ ∃ a, opt = some a ∧ 0 < (f a) s := by
  cases opt <;> simp [Option.unwrapM]

@[simp]
theorem asValM_singleton_pos [MeasurableSpace T] {e : Exp} {f : Val → Measure T} :
    0 < (e.asValM f) s ↔ ∃ v, e.toVal? = some v ∧ 0 < (f v) s := by
  unfold Exp.asValM; cases e.toVal? <;> simp

theorem Cfg.uniform_singleton_pos_inv {z : Int} {σ : State} {ρ : Cfg}
    (h : 0 < Cfg.uniform z σ {ρ}) :
    0 < z ∧ ρ.state = σ ∧
    ∃ v : Int, ρ.expr = .lit (.int v) ∧ 0 ≤ v ∧ v ≤ z := by
  unfold Cfg.uniform Int.isPos Option.unwrapM at h
  by_cases Hz : 0 < z
  case neg => simp_all
  case pos =>
    simp [Hz, Measure.map_apply .of_discrete .of_discrete] at h
    obtain ⟨_, _, _, rfl⟩ := h
    simp_all

theorem Cfg.uniform_singleton_pos_of_mem {z v : Int} {σ : State}
    (Hz : 0 < z) (Hv0 : 0 ≤ v) (Hvz : v ≤ z) :
    0 < Cfg.uniform z σ {⟨.lit (.int v), σ⟩} := by
  unfold Cfg.uniform Int.isPos Option.unwrapM
  simp only [Hz, dite_true]
  rw [Measure.map_apply (f := fun x => (⟨.lit (.int x), σ⟩ : Cfg)) Measurable.of_discrete MeasurableSet.of_discrete]
  rw [PMF.toMeasure_uniformOfFinset_apply _ _ MeasurableSet.of_discrete]
  rw [ENNReal.div_pos_iff]
  refine ⟨?_, ?_⟩
  · rw [ne_eq, Nat.cast_eq_zero]
    exact Finset.card_ne_zero.mpr ⟨v, by simp [Finset.mem_filter, Finset.mem_Icc, Hv0, Hvz, Set.mem_preimage]⟩
  · exact ENNReal.natCast_ne_top _

/-- Decompose `0 < (dirac a) {b}` into Cfg component equalities, then substitute. -/
macro "cfg_dirac" h:ident : tactic =>
  `(tactic| (rw [dirac_singleton_pos] at $h:ident
             have ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp $h:ident))

theorem headStep_support_iff (e1 e2 : Exp) (σ1 σ2 : State) :
    0 < headStep ⟨e1, σ1⟩ {⟨e2, σ2⟩} ↔ HeadStepSupport ⟨e1, σ1⟩ ⟨e2, σ2⟩ := by
  constructor
  · head_case
    all_goals try (· simp)
    case cond.true | cond.false => intro h; cfg_dirac h; constructor
    case beta.redex => intro h; cfg_dirac h; exact .BetaS ‹_› rfl
    case fst.redex => intro h; cfg_dirac h; exact .FstS ‹_› ‹_›
    case snd.redex => intro h; cfg_dirac h; exact .SndS ‹_› ‹_›
    case case.left.redex => intro h; cfg_dirac h; exact .CaseLS ‹_›
    case case.right.redex => intro h; cfg_dirac h; exact .CaseRS ‹_›
    case tape => intro h; cfg_dirac h; exact .TapeS rfl rfl
    case load.redex => intro h; cfg_dirac h; exact .LoadS ‹_› rfl
    case alloc.redex => intro h; cfg_dirac h; exact .AllocS ‹_› rfl rfl
    case store.redex =>
      intro h; cfg_dirac h
      exact .StoreS ‹_› (by rw [Option.isSome_iff_exists]; exact ⟨_, ‹_›⟩) rfl
    case rand.tape.deterministic =>
      intro h; cfg_dirac h; exact .RandTapeS (by omega) ‹_› rfl rfl rfl
    case unop.redex =>
      intro h; rw [unwrapM_singleton_pos] at h
      obtain ⟨r, hr, h⟩ := h; cfg_dirac h; exact .UnOpS ‹_› hr.symm
    case binop.redex =>
      intro h; rw [unwrapM_singleton_pos] at h
      obtain ⟨r, hr, h⟩ := h; cfg_dirac h; exact .BinOpS ‹_› ‹_› hr.symm
    case rand.plain =>
      intro h
      obtain ⟨Hz, hσ, v, hv, Hv0, Hvz⟩ := Cfg.uniform_singleton_pos_inv h
      simp at hv hσ; subst hv; subst hσ
      exact .RandNoTapeS Hz Hv0 Hvz
    case rand.tape =>
      intro h
      obtain ⟨Hz, hσ, v, hv, Hv0, Hvz⟩ := Cfg.uniform_singleton_pos_inv h
      simp at hv hσ; subst hv; subst hσ
      exact .RandTapeEmptyS Hz ‹_› rfl Hv0 Hvz rfl
    case rand.tape.mismatch =>
      intro h
      obtain ⟨Hz, hσ, v, hv, Hv0, Hvz⟩ := Cfg.uniform_singleton_pos_inv h
      simp at hv hσ; subst hv; subst hσ
      exact .RandTapeOtherS Hz ‹_› (Ne.symm ‹_›) Hv0 Hvz rfl
    case annot.redex => intro h; cfg_dirac h; exact .AnnotS ‹_›
    case scrut_success => intro h; cfg_dirac h; exact .ScrutSuccessS ‹_› ‹_›
    case scrut_failure => intro h; cfg_dirac h; exact .ScrutFailureS ‹_› ‹_›
  · intro hsupp
    cases hsupp with
    | BetaS | IfTrueS | IfFalseS | FstS |SndS | CaseLS | CaseRS | LoadS
    | TapeS | RandTapeS | AllocS | StoreS
    | ScrutSuccessS | ScrutFailureS | AnnotS =>
      simp_all [headStep]
    | RandNoTapeS | RandTapeEmptyS =>
      simp_all [headStep, Cfg.uniform_singleton_pos_of_mem]
    | UnOpS _ heval | BinOpS _ _ heval =>
      simp_all [headStep]
      exact ⟨_, heval.symm, by simp⟩
    | RandTapeOtherS Hz htape hzN Hv0 Hvz hσ =>
      subst hσ
      simp only [headStep, htape]
      split
      · next hM => rw [hM] at hzN; exact absurd rfl hzN
      · exact Cfg.uniform_singleton_pos_of_mem Hz Hv0 Hvz

theorem isValM_isProbabilityMeasure [MeasurableSpace T] {e : Exp} {m : Measure T}
    (he : e.isValue) [IsProbabilityMeasure m] : IsProbabilityMeasure (e.isValM m) := by
  rw [Exp.isValM, if_pos he]; infer_instance

theorem asValM_isProbabilityMeasure [MeasurableSpace T] {e : Exp} {f : Val → Measure T}
    {v : Val} (hv : e.toVal? = some v) [IsProbabilityMeasure (f v)] :
    IsProbabilityMeasure (e.asValM f) := by
  simp [Exp.asValM, hv]; infer_instance

theorem Cfg.uniform_isProbabilityMeasure {z : Int} {σ : State} (Hz : 0 < z) :
    IsProbabilityMeasure (Cfg.uniform z σ) := by
  unfold Cfg.uniform Int.isPos Option.unwrapM
  simp only [Hz, dite_true]
  exact Measure.isProbabilityMeasure_map (μ := (PMF.uniformOfFinset _ _).toMeasure)
    AEMeasurable.of_discrete

theorem head_step_mass (e : Exp) (σ : State) :
    (∃ ρ : Cfg, 0 < headStep ⟨e, σ⟩ {ρ}) → IsProbabilityMeasure (headStep ⟨e, σ⟩) := by
  head_case
  all_goals try (· simp)
  case beta.redex | cond.true | cond.false
     | fst.redex | snd.redex | case.left.redex | case.right.redex
     | alloc.redex | load.redex | store.redex | tape
     | rand.tape.deterministic
     | scrut_success | scrut_failure | annot.redex => intro _; infer_instance
  case unop.redex | binop.redex =>
    intro ⟨_, hρ⟩; rw [unwrapM_singleton_pos] at hρ
    obtain ⟨_, he, _⟩ := hρ; simp [Option.unwrapM, he]; infer_instance
  case rand.plain | rand.tape | rand.tape.mismatch =>
    intro ⟨_, hρ⟩
    exact Cfg.uniform_isProbabilityMeasure (Cfg.uniform_singleton_pos_inv hρ).1

end ProbLang
