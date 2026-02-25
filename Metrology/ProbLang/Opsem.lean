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
| ⟨.load (.lit (.loc ℓ)), σ⟩ => σ.heap[ℓ]?.casesOn 0 (dirac ⟨.ofVal ·, σ⟩)
| ⟨.store (.lit (.loc ℓ)) e, σ⟩ =>
  e.asValM fun v =>
  σ.heap[ℓ]?.casesOn 0 fun _ => dirac ⟨.lit .unit, σ.update_heap fun t => t.insert ℓ v⟩
| ⟨.rand (.lit (.int z)) (.lit .unit), σ⟩ => Cfg.Uniform z σ
| ⟨.allocTape (.lit (.int z)), σ⟩ =>
  let α := σ.tapes.fresh
  dirac ⟨.lit <| .lbl α, σ.update_tapes fun t => t.insert α (.empty z)⟩
| ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩ =>
  σ.tapes[α]?.unwrapM fun ⟨M, ns⟩ =>
  if M = z
    then
      match ns with
      | [] => Cfg.Uniform z σ
      | n :: ns => dirac ⟨.lit <| .int n, σ.update_tapes fun t => t.insert α ⟨M, ns⟩⟩
    else Cfg.Uniform z σ
| _ => 0

def HeadStepKernel : Kernel Cfg Cfg where
  measurable' := .of_discrete
  toFun := HeadStep

theorem val_head_stuck : HeadStep ⟨e, σ⟩ {ρ} > 0 → e.toVal? = none := by
  sorry
-- Lemma val_head_stuck e σ ρ :
--   head_step e σ ρ > 0 → to_val e = None.
-- Proof. destruct ρ, e; [|done..]. rewrite /pmf /=. lra. Qed.

theorem haed_ctx_step_val {Ki : EctxItem} :
    HeadStep ⟨Ki.FillItem e, σ⟩ {ρ} > 0 → e.isValue := by
  sorry
-- Lemma head_ctx_step_val Ki e σ ρ :
--   head_step (fill_item Ki e) σ ρ > 0 → is_Some (to_val e).
-- Proof.
--   destruct ρ, Ki ;
--     rewrite /pmf/= ;
--     repeat case_match; clear -H ; inversion H; intros ; (lra || done).
-- Qed.


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
| AllocTapeS :
  ℓ = σ.tapes.fresh →
  σ' = σ.update_tapes (·.insert ℓ (.empty z)) →
  HeadStepSupport ⟨.allocTape (.lit (.int z)), σ⟩ ⟨.lit (.lbl ℓ), σ'⟩
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

