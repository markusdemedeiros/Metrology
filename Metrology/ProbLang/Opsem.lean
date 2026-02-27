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

-- def Expr.asValM [MeasurableSpace T] (e : Expr) (f : Val → Measure T) : Measure T :=
--   match e.toVal? with | none => 0 | some v => f v

-- def Expr.isValM [MeasurableSpace T] (e : Expr) (m : Measure T) : Measure T :=
--   match e.toVal? with | none => 0 | some _ => m

-- @[simp] theorem Expr.isValM_some [MeasurableSpace T] {e : Expr} {m : Measure T} (He : e.isValue) :
--     e.isValM m = m := by
--   simp [Expr.isValM, Expr.toVal?] -- He]
--   sorry

-- @[simp] theorem Expr.isValM_none [MeasurableSpace T] {e : Expr} {m : Measure T} (He : ¬ e.isValue) :
--     e.isValM m = 0 := by
--   simp [Expr.isValM, Expr.toVal?] -- He]
--   sorry

def Int.isPos (z : Int) : Option { z : Int // 0 < z } :=
  if H : 0 < z then some ⟨z, H⟩ else none

local instance : MeasurableSpace Expr := ⊤
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Val := ⊤
local instance : MeasurableSpace Cfg := ⊤

def Cfg.Uniform (z : Int) (σ : State) : Measure Cfg :=
  z.isPos.unwrapM fun ⟨z, Hz⟩ =>
  PMF.uniformOfFinset (.Icc 0 z) (Finset.nonempty_Icc.mpr <| Int.le_of_lt Hz)
    |>.toMeasure.map (⟨.val <| .lit <| .int ·, σ⟩)

-- TODO: What if we change Cfg to Option (Expr × State)?
-- NB. Rand is currently off-by-one from Eris. I'm going to see if sticking `by grind`
-- as a default term everywhere will solve all the positvity side conditions.
-- TODO: Do we need these value checks? Finding the redex, and enforcing evalutation
-- order, should be governed by the reduction context.
def HeadStep : Cfg → Measure Cfg
| ⟨.letrec f x e, σ⟩ => dirac ⟨.val (.letrec f x e), σ⟩
| ⟨.pair (.val v1) (.val v2), σ⟩ => dirac ⟨.val (.pair (.val v1) (.val v2)), σ⟩
| ⟨.inl (.val v), σ⟩ => dirac ⟨.val (.inl (.val v)), σ⟩
| ⟨.inr (.val v), σ⟩ => dirac ⟨.val (.inr (.val v)), σ⟩
| ⟨.app (.val (.letrec f x e1)) (.val v2), σ⟩ =>
  dirac ⟨e1.subst' f (.letrec f x e1) |>.subst' x v2, σ⟩
| ⟨.unop op (.val v), σ⟩ => (op.eval v).unwrapM (dirac ⟨·, σ⟩)
| ⟨.binop op (.val v1) (.val v2), σ⟩ => (op.eval v1 v2).unwrapM (dirac ⟨·, σ⟩)
| ⟨.cond (.val (.lit (.bool true))) et _, σ⟩ => dirac ⟨et, σ⟩
| ⟨.cond (.val (.lit (.bool false))) _ ef, σ⟩ => dirac ⟨ef, σ⟩
| ⟨.fst (.pair (.val v1) (.val _)), σ⟩ => (dirac ⟨.val v1, σ⟩)
| ⟨.snd (.pair (.val _) (.val v2)), σ⟩ => (dirac ⟨.val v2, σ⟩)
| ⟨.case (.val (.inl e)) el _, σ⟩ => (dirac ⟨el.app e, σ⟩)
| ⟨.case (.val (.inr e)) _ er, σ⟩ => (dirac ⟨er.app e, σ⟩)
| ⟨.alloc (.val vd), σ⟩ =>
  let ℓ := σ.heap.fresh
  dirac ⟨.val (.lit (.loc ℓ)), σ.update_heap fun t => t.insert ℓ (.val vd)⟩
| ⟨.load (.val (.lit (.loc ℓ))), σ⟩ => σ.heap[ℓ]?.casesOn 0 (dirac ⟨·, σ⟩)
| ⟨.store (.lit (.loc ℓ)) (.val v), σ⟩ =>
  σ.heap[ℓ]?.casesOn 0 fun _ => dirac ⟨.lit .unit, σ.update_heap fun t => t.insert ℓ v⟩
| ⟨.rand (.val (.lit (.int z))) (.val (.lit .unit)), σ⟩ => Cfg.Uniform z σ
| ⟨.tape (.val (.lit (.int z))), σ⟩ =>
  let α := σ.tapes.fresh
  dirac ⟨.lit <| .lbl α, σ.update_tapes fun t => t.insert α (.empty z)⟩
| ⟨.rand (.val (.lit (.int z))) (.val (.lit (.lbl α))), σ⟩ =>
  σ.tapes[α]?.unwrapM fun ⟨M, ns⟩ =>
  if M = z
    then
      match ns with
      | [] => Cfg.Uniform z σ
      | n :: ns => dirac ⟨.val (.lit (.int n)), σ.update_tapes fun t => t.insert α ⟨M, ns⟩⟩
    else Cfg.Uniform z σ
| _ => 0

def HeadStepKernel : Kernel Cfg Cfg where
  measurable' := .of_discrete
  toFun := HeadStep

theorem dirac_singleton_gt_0 {ρ1 ρ2 : Cfg} : dirac ρ1 {ρ2} > 0 ↔ ρ1 = ρ2 := by
  simp [Pi.single, Function.update]
  split <;> rename_i h
  · exact ⟨fun _ => h, fun _ => zero_lt_one' _⟩
  · simpa

theorem val_head_stuck : HeadStep ⟨e, σ⟩ {ρ} > 0 → e.toVal? = none := by
  obtain ⟨ρe, ρσ⟩ := ρ
  simp only [HeadStep]
  split <;> try rw [dirac_singleton_gt_0]
  all_goals rename_i h
  all_goals try obtain ⟨rfl, rfl⟩ := h
  all_goals try rintro ⟨rfl, rfl⟩
  all_goals try simp [Expr.toVal?]
  exfalso
  rename_i Hcontra
  exact (lt_self_iff_false 0).mp Hcontra

theorem haed_ctx_step_val {Ki : EctxItem} :
    HeadStep ⟨Ki.FillItem e, σ⟩ {ρ} > 0 → e.isValue := by
  obtain ⟨ρe, ρσ⟩ := ρ
  cases Ki
  all_goals simp only [EctxItem.FillItem]
  all_goals cases e
  all_goals simp [HeadStep]
  · rename_i e1 e2

    sorry
  · sorry
  · sorry


inductive HeadStepSupport : Cfg → Cfg → Prop
| BetaS :
  e' = (e1.subst' f (.letrec f x e1)).subst' x v2 →
  HeadStepSupport ⟨.app (.letrec f x e1) (.val v2), σ⟩ ⟨e', σ⟩
| UnOpS :
  some e' = op.eval v →
  HeadStepSupport ⟨.unop op (.val v), σ⟩ ⟨e', σ⟩
| BinOpS :
  some e' = op.eval v1 v2 →
  HeadStepSupport ⟨.binop op (.val v1) (.val v2), σ⟩ ⟨e', σ⟩
| IfTrueS :
  HeadStepSupport ⟨.cond (.val (.lit (.bool true))) et _, σ⟩ ⟨et, σ⟩
| IfFalseS :
  HeadStepSupport ⟨.cond (.val (.lit (.bool false))) _ ef, σ⟩ ⟨ef, σ⟩
| FstS :
  HeadStepSupport ⟨.fst (.pair (.val e1) (.val e2)), σ⟩ ⟨e1, σ⟩
| SndS :
  HeadStepSupport ⟨.snd (.pair (.val e1) (.val e2)), σ⟩ ⟨e2, σ⟩
| CaseLS :
  HeadStepSupport ⟨.case (.val (.inl e)) el er, σ⟩ ⟨el.app e, σ⟩
| CaseRS :
  HeadStepSupport ⟨.case (.val (.inr e)) el er, σ⟩ ⟨er.app e, σ⟩
| AllocS :
  ℓ = σ.heap.fresh →
  σ' = σ.update_heap (·.insert ℓ vd) →
  HeadStepSupport ⟨.alloc (.val vd), σ⟩ ⟨.val (.lit (.loc ℓ)), σ'⟩
| LoadS :
  σ.heap[ℓ]? = some v →
  HeadStepSupport ⟨.load (.val (.lit (.loc ℓ))), σ⟩ ⟨v, σ⟩
| StoreS :
  σ.heap[ℓ]?.isSome →
  σ' = σ.update_heap (·.insert ℓ v) →
  HeadStepSupport ⟨.store (.val (.lit (.loc ℓ))) (.val v), σ⟩ ⟨.val (.lit .unit), σ'⟩
| RandNoTapeS :
  0 < z →
  0 ≤ v →
  v < z →
  HeadStepSupport ⟨.rand (.val (.lit (.int z))) (.val (.lit .unit)), σ⟩ ⟨.val (.lit (.int v)), σ⟩
| AllocTapeS :
  ℓ = σ.tapes.fresh →
  σ' = σ.update_tapes (·.insert ℓ (.empty z)) →
  HeadStepSupport ⟨.tape (.val (.lit (.int z))), σ⟩ ⟨.val (.lit (.lbl ℓ)), σ'⟩
| RandTapeS :
  0 < z →
  σ.tapes[α]? = some ⟨N, nn :: ns⟩ →
  z = N →
  v = nn.1 →
  σ' = σ.update_tapes (·.insert α ⟨N, ns⟩) →
  HeadStepSupport ⟨.rand (.val (.lit (.int z))) (.val (.lit (.lbl α))), σ⟩ ⟨.val (.lit (.int v)), σ'⟩
| RandTapeEmptyS :
  0 < z →
  σ.tapes[α]? = some ⟨N, []⟩ →
  z = N →
  0 ≤ v →
  v < z →
  HeadStepSupport ⟨.rand (.val (.lit (.int z))) (.val (.lit (.lbl α))), σ⟩ ⟨.val (.lit (.int v)), σ'⟩
| RandTapeOtherS :
  0 < z →
  σ.tapes[α]? = some ⟨N, L⟩ →
  z ≠ N →
  0 ≤ v →
  v < z →
  HeadStepSupport ⟨.rand (.val (.lit (.int z))) (.val (.lit (.lbl α))), σ⟩ ⟨.val (.lit (.int v)), σ'⟩

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

