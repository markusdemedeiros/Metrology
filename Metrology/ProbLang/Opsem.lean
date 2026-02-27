import Metrology.ProbLang.Syntax
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Distributions.Uniform

noncomputable section HeadStep
open Classical MeasureTheory ProbabilityTheory Measure

def Option.unwrapM {α : Type _} [MeasurableSpace β] (f : α → Measure β) : Option α → Measure β
| some v => f v
| none => 0

def Expr.asValM [MeasurableSpace T] (e : Expr) (f : Val → Measure T) : Measure T :=
  match e.toVal? with | none => 0 | some v => f v

def Expr.isValM [MeasurableSpace T] (e : Expr) (m : Measure T) : Measure T :=
  match e.toVal? with | none => 0 | some _ => m

@[simp] theorem Expr.isValM_some [MeasurableSpace T] {e : Expr} {m : Measure T} (He : e.isValue) :
    e.isValM m = m := by simp [Expr.isValM, Expr.toVal?, He]

@[simp] theorem Expr.isValM_none [MeasurableSpace T] {e : Expr} {m : Measure T} (He : ¬ e.isValue) :
    e.isValM m = 0 := by simp [Expr.isValM, Expr.toVal?, He]

def Int.isPos (z : Int) : Option { z : Int // 0 < z } :=
  if H : 0 < z then some ⟨z, H⟩ else none

local instance : MeasurableSpace Expr := ⊤
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Val := ⊤
local instance : MeasurableSpace Cfg := ⊤

def Cfg.Uniform (z : Int) (σ : State) : Measure Cfg :=
  z.isPos.unwrapM fun ⟨z, Hz⟩ =>
  PMF.uniformOfFinset (.Icc 0 z) (Finset.nonempty_Icc.mpr <| Int.le_of_lt Hz)
    |>.toMeasure.map (⟨.lit <| .int ·, σ⟩)

-- TODO: What if we change Cfg to Option (Expr × State)?
-- NB. Rand is currently off-by-one from Eris. I'm going to see if sticking `by grind`
-- as a default term everywhere will solve all the positvity side conditions.
-- TODO: Do we need these value checks? Finding the redex, and enforcing evalutation
-- order, should be governed by the reduction context.
def HeadStep : Cfg → Measure Cfg
| ⟨.app (.letrec f x e1) e2, σ⟩ =>
  e2.isValM <|
  dirac ⟨e1.subst' f (.letrec f x e1) |>.subst' x e2, σ⟩
| ⟨.unop op e, σ⟩ =>
  e.isValM <|
  (op.eval e).unwrapM <|
  (dirac ⟨·, σ⟩)
| ⟨.binop op e1 e2, σ⟩ =>
  e1.isValM <|
  e2.isValM <|
  (op.eval e1 e2).unwrapM <|
  (dirac ⟨·, σ⟩)
| ⟨.bif (.lit (.bool true)) et _, σ⟩ => dirac ⟨et, σ⟩
| ⟨.bif (.lit (.bool false)) _ ef, σ⟩ => dirac ⟨ef, σ⟩
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
| ⟨.rand (.lit (.int z)) (.lit .unit), σ⟩ => Cfg.Uniform z σ
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
        | [] => Cfg.Uniform z σ
        | n :: ns => dirac ⟨.lit <| .int n, σ.update_tapes fun t => t.insert α ⟨M, ns⟩⟩
      else Cfg.Uniform z σ
| _ => 0


-- head_case
-- case beta.redex => sorry
-- case beta.no_redex => sorry
-- case unop.redex => sorry
-- case unop.no_redex => sorry
-- case binop.no_redex_1 => sorry
-- case binop.no_redex_2 => sorry
-- case binop.redex => sorry
-- case cond.true => sorry
-- case cond.false => sorry
-- case fst.no_redex_1 => sorry
-- case fst.no_redex_2 => sorry
-- case fst.redex => sorry
-- case snd.no_redex_1 => sorry
-- case snd.no_redex_2 => sorry
-- case snd.redex => sorry
-- case case.left.no_redex => sorry
-- case case.left.redex => sorry
-- case case.right.no_redex => sorry
-- case case.right.redex => sorry
-- case alloc.no_redex => sorry
-- case alloc.redex => sorry
-- case load.segfault => sorry
-- case load.redex => sorry
-- case store.no_redex => sorry
-- case store.segfault => sorry
-- case store.redex => sorry
-- case rand.plain => sorry
-- case tape => sorry
-- case rand.tape.unalloc => sorry
-- case rand.tape.mismatch => sorry
-- case rand.tape.empty => sorry
-- case rand.tape.deterministic => sorry
-- case default => sorry

elab "rename_goal" name:ident : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.setUserName name.getId

/-- Split the HeadStep cases, but with informative goal names. -/
macro "head_case_names" : tactic =>
  `(tactic| (
    unfold HeadStep
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
    on_goal 16 => rename_goal default
  ))

macro "head_case_intro" : tactic =>
  `(tactic| (
    rename_i h_eq
    have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
    subst_eqs
  ))

-- TODO: Refactor
macro "head_case" : tactic =>
  `(tactic| (
    head_case_names
    case' rand.tape =>
      rename_i h_eq
      have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
      subst_eqs
      split
      on_goal 1 => rename_goal rand.tape.unalloc
      on_goal 2 =>
        split
        on_goal 2 =>
          rename_goal rand.tape.mismatch
        on_goal 1 =>
          subst_eqs
          split
          on_goal 1 => rename_goal rand.tape.empty
          on_goal 2 => rename_goal rand.tape.deterministic
    case' tape =>
      rename_i h_eq
      have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
      subst_eqs
    case' rand.plain =>
      rename_i h_eq
      have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
      subst_eqs
    case' store =>
      rename_i h_eq
      have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
      subst_eqs
      unfold Expr.asValM
      split
      on_goal 1 => rename_goal store.no_redex
      on_goal 2 =>
        split
        on_goal 1 => rename_goal store.segfault
        on_goal 2 => rename_goal store.redex
    case' load =>
      rename_i h_eq
      have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
      subst_eqs
      split
      on_goal 1 => rename_goal load.segfault
      on_goal 2 => rename_goal load.redex
    case' alloc =>
      rename_i h_eq
      have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
      subst_eqs
      unfold Expr.asValM
      split
      on_goal 1 => rename_goal alloc.no_redex
      on_goal 2 => rename_goal alloc.redex
    case' case.right =>
      rename_i h_eq
      have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
      subst_eqs
      unfold Expr.isValM
      split
      on_goal 1 => rename_goal case.right.no_redex
      on_goal 2 => rename_goal case.right.redex
    case' case.left =>
      rename_i h_eq
      have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
      subst_eqs
      unfold Expr.isValM
      split
      on_goal 1 => rename_goal case.left.no_redex
      on_goal 2 => rename_goal case.left.redex
    case' snd =>
      rename_i h_eq
      have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
      subst_eqs
      unfold Expr.isValM
      split
      on_goal 1 => rename_goal snd.no_redex_1
      on_goal 2 =>
        split
        on_goal 1 => rename_goal snd.no_redex_2
        on_goal 2 => rename_goal snd.redex
    case' fst =>
      rename_i h_eq
      have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
      subst_eqs
      unfold Expr.isValM
      split
      on_goal 1 => rename_goal fst.no_redex_1
      on_goal 2 =>
        split
        on_goal 1 => rename_goal fst.no_redex_2
        on_goal 2 => rename_goal fst.redex
    case' cond.false =>
      rename_i h_eq
      have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
      subst_eqs
    case' cond.true =>
      rename_i h_eq
      have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
      subst_eqs
    case' binop =>
      rename_i h_eq
      have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
      subst_eqs
      unfold Expr.isValM
      split
      on_goal 1 => rename_goal binop.no_redex_1
      on_goal 2 =>
        split
        on_goal 1 => rename_goal binop.no_redex_2
        on_goal 2 => rename_goal binop.redex
    case' unop =>
      rename_i h_eq
      have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
      subst_eqs
      unfold Expr.isValM
      split
      on_goal 1 => rename_goal unop.no_redex
      on_goal 2 => rename_goal unop.redex
    case' beta =>
      rename_i h_eq
      have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
      subst_eqs
      unfold Expr.isValM
      split
      on_goal 1 => rename_goal beta.no_redex
      on_goal 2 => rename_goal beta.redex
  ))

def HeadStepKernel : Kernel Cfg Cfg where
  measurable' := .of_discrete
  toFun := HeadStep

theorem val_head_stuck : HeadStep ⟨e, σ⟩ {ρ} > 0 → e.toVal? = none := by
  head_case <;> simp [Expr.toVal?]

theorem Expr.toVal?_isValue {e : Expr} : e.toVal? = some v → e.isValue := by
  simp [Expr.toVal?]; grind

-- FIXME: Long proof, needs some automation
theorem haed_ctx_step_val {Ki : EctxItem} :
    HeadStep ⟨Ki.FillItem e, σ⟩ {ρ} > 0 → e.isValue := by
  have Hzero : (0 : Measure Cfg) {ρ} > 0 → False := by simp
  have Hdirac : ∀ {ρ' : Cfg}, dirac ρ' {ρ} > 0 → ρ = ρ' := by
    simp [dirac, Pi.single, Function.update]; grind
  head_case
  all_goals try (exact fun H => (Hzero H).elim) -- Deal with all stuck cases
  -- Now: the redexes remain
  all_goals cases Ki
  all_goals (rename_i Hk _; simp [EctxItem.FillItem] at Hk)
  all_goals try (obtain ⟨rfl, rfl⟩ := Hk)
  all_goals try (obtain ⟨rfl, rfl, rfl⟩ := Hk)
  all_goals try (· simp [Expr.isValue])
  all_goals try (rename_i Hk _; intro _; exact Expr.toVal?_isValue Hk)
  all_goals simp [Expr.isValue]
  all_goals intro _
  all_goals try (· apply Expr.toVal?_isValue; trivial)
  all_goals try (· apply And.intro <;> apply Expr.toVal?_isValue <;> trivial)
  all_goals try (obtain ⟨H1, _⟩ := Hk; rw [H1]; simp [Expr.isValue])

inductive HeadStepSupport : Cfg → Cfg → Prop
| BetaS :
  e2.isValue →
  e' = (e1.subst' f (.letrec f x e1)).subst' x e2 →
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
  HeadStepSupport ⟨.bif (.lit (.bool true)) et _, σ⟩ ⟨et, σ⟩
| IfFalseS :
  HeadStepSupport ⟨.bif (.lit (.bool false)) _ ef, σ⟩ ⟨ef, σ⟩
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
  e' = Expr.ofVal v →
  HeadStepSupport ⟨.load (.lit (.loc ℓ)), σ⟩ ⟨e', σ⟩
| StoreS :
  e.toVal? = some v →
  σ.heap[ℓ]?.isSome →
  σ' = σ.update_heap (·.insert ℓ v) →
  HeadStepSupport ⟨.store (.lit (.loc ℓ)) e, σ⟩ ⟨.lit .unit, σ'⟩
| RandNoTapeS :
  0 < z →
  0 ≤ v →
  v < z →
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
  v < z →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩ ⟨.lit (.int v), σ'⟩
| RandTapeOtherS :
  0 < z →
  σ.tapes[α]? = some ⟨N, L⟩ →
  z ≠ N →
  0 ≤ v →
  v < z →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩ ⟨.lit (.int v), σ'⟩

-- Lemma head_step_support_equiv_rel e1 e2 σ1 σ2 :
--   head_step e1 σ1 (e2, σ2) > 0 ↔ head_step_rel e1 σ1 e2 σ2.
-- Proof.
--   split.
--   - intros ?. destruct e1; inv_head_step ; eauto with head_step.
--   - inversion 1; simplify_map_eq/= ; try case_bool_decide ; try case_decide ; simplify_eq; solve_distr; try done.
-- Qed.

-- Lemma head_step_mass e σ :
--   (∃ ρ, head_step e σ ρ > 0) → SeriesC (head_step e σ) = 1.
-- Proof.
--   intros [[] Hs%head_step_support_equiv_rel].
--   inversion Hs;
--     repeat (simplify_map_eq/=; solve_distr_mass || (case_match ; try done) ;
--             try (case_bool_decide; done)).
-- Qed.

