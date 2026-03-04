import Metrology.ProbLang.Syntax
import Std.Data.ExtTreeMap.Lemmas

open Std

/-! An interpreter for testing ProbLang programs. -/

namespace ProbLang
namespace Eval

/-- Interpreter error type. -/
inductive Error
  | fail   : Error
  | stuck  : String → Exp → Error
  | unsupported  : String → Error
  | segfault : Loc → Error

instance : ToString Error where
  toString
    | .fail        => "fail"
    | .stuck msg e => s!"stuck ({msg}): {repr e}"
    | .segfault ℓ  => s!"segfault at location {ℓ}"
    | .unsupported msg  => s!"unsupported: {msg}"

private def throw' (err : Error) : IO α :=
  throw (IO.userError (toString err))

private theorem UnOp.eval_isValue {op : UnOp} {v r : Exp} (h : op.eval v = some r) :
    r.isValue := by
  cases op <;> cases v <;> simp_all [UnOp.eval] <;>
    rename_i b <;> cases b <;> simp_all <;> subst_vars <;> simp

private theorem BinOp.eval_isValue {op : BinOp} {v1 v2 r : Exp} (h : op.eval v1 v2 = some r) :
    r.isValue := by
  cases op <;> cases v1 <;> cases v2 <;> simp_all [BinOp.eval] <;>
    rename_i b1 b2 <;> cases b1 <;> cases b2 <;> simp_all <;>
    subst_vars <;> simp

/-- Sample uniformly from [0, z).  Returns an error if z ≤ 0. -/
def sampleUniform (z : Int) : IO Int := do
  if 0 < z then
    return ← IO.rand 0 z.toNat
  else
    throw' (.stuck "rand: bound must be positive" (.lit (.int z)))

/-- An interpreter for ProbLang expressions.

Follows call-by-value, right-to-left evaluation order matching the
operational semantics in `Opsem.lean`.  The heap is an `IO.Ref` holding
an `ExtTreeMap Loc Val`.  `tape e` evaluates its argument and returns the
result (no tape state is maintained).  `rand` always samples uniformly.

NB: Per the semantics, substitution is not capture-avoiding. -/
partial def eval (σ : IO.Ref (ExtTreeMap Loc Val)) (e : Exp) : IO Val := do
  match e with
  -- Values: return immediately
  | .lit b           => return ⟨.lit b, by simp [Exp.isValue]⟩
  | .letrec f x body => return ⟨.letrec f x body, by simp [Exp.isValue]⟩

  -- Variables: stuck (should have been substituted away)
  | .var x => throw' (.stuck s!"unbound variable '{x}'" (.var x))

  -- Application: evaluate argument first (right-to-left), then function,
  -- then beta-reduce.
  | .app e1 e2 => do
    let v2 ← eval σ e2
    let v1 ← eval σ e1
    match v1.1 with
    | .letrec f x body =>
        -- Match HeadStep: substitute f first (recursive name), then x (argument).
        -- When f = x the order matters: f's substitution shadows x in the letrec value.
        eval σ (Exp.subst' x v2.1 (Exp.subst' f v1.1 body))
    | _ => throw' (.stuck "application of non-function" v1.1)

  -- Unary operators
  | .unop op e => do
    let v ← eval σ e
    match h : op.eval v.1 with
    | some r => return ⟨r, UnOp.eval_isValue h⟩
    | none   => throw' (Error.stuck s!"unop: type error" v.1)

  -- Binary operators: right-to-left
  | .binop op e1 e2 => do
    let v2 ← eval σ e2
    let v1 ← eval σ e1
    match h : op.eval v1.1 v2.1 with
    | some r => return ⟨r, BinOp.eval_isValue h⟩
    | none   => throw' (Error.stuck "binop: type error" v1.1)

  -- Conditionals
  | .cond ec et ef => do
    let vc ← eval σ ec
    match vc.1 with
    | .lit (.bool true)  => eval σ et
    | .lit (.bool false) => eval σ ef
    | _ => throw' (.stuck "cond: non-boolean condition" vc.1)

  -- Pairs
  | .pair e1 e2 => do
    let v2 ← eval σ e2
    let v1 ← eval σ e1
    return ⟨.pair v1.1 v2.1, by simp [Exp.isValue, v1.2, v2.2]⟩

  | .fst e => do
    let v ← eval σ e
    match v.1 with
    | .pair e1 _ => eval σ e1
    | _ => throw' (.stuck "fst: not a pair" v.1)

  | .snd e => do
    let v ← eval σ e
    match v.1 with
    | .pair _ e2 => eval σ e2
    | _ => throw' (.stuck "snd: not a pair" v.1)

  -- Sums
  | .inl e => do
    let v ← eval σ e
    return ⟨.inl v.1, by simp [Exp.isValue, v.2]⟩

  | .inr e => do
    let v ← eval σ e
    return ⟨.inr v.1, by simp [Exp.isValue, v.2]⟩

  | .case ec el er => do
    let vc ← eval σ ec
    match vc.1 with
    | .inl payload => eval σ (.app el payload)
    | .inr payload => eval σ (.app er payload)
    | _ => throw' (.stuck "case: not a sum" vc.1)

  -- Heap
  | .alloc ed => do
    let vd ← eval σ ed
    let heap ← σ.get
    let ℓ := heap.fresh
    σ.modify (·.insert ℓ vd)
    return ⟨.lit (.loc ℓ), by simp [Exp.isValue]⟩

  | .load e => do
    let v ← eval σ e
    match v.1 with
    | .lit (.loc ℓ) =>
      let heap ← σ.get
      match heap[ℓ]? with
      | none   => throw' (.segfault ℓ)
      | some w => return w
    | _ => throw' (.stuck "load: not a location" v.1)

  | .store e1 e2 => do
    let v2 ← eval σ e2
    let v1 ← eval σ e1
    match v1.1 with
    | .lit (.loc ℓ) =>
      let heap ← σ.get
      match heap[ℓ]? with
      | none   => throw' (.segfault ℓ)
      | some _ =>
        σ.modify (·.insert ℓ v2)
        return ⟨.lit .unit, by simp [Exp.isValue]⟩
    | _ => throw' (.stuck "store: not a location" v1.1)

  -- Probabilistic
  | .tape e => throw' (.unsupported "tape allocation")
  | .rand e1 e2 => do
    let v2 ← eval σ e2
    let v1 ← eval σ e1
    match v1.1 with
    | .lit (.int z) =>
      let n ← sampleUniform z
      match v2.1 with
      | (.lit .unit) =>
        return ⟨.lit (.int n), by simp [Exp.isValue]⟩
      | (.lit (.lbl ℓ)) => throw' (.unsupported "tape random samples")
      | _ => throw' (.stuck "rand: tape is not unit or a location" v2.1)
    | _ => throw' (.stuck "rand: not an integer bound" v1.1)

  -- Failure
  | .fail => throw' .fail

/-- Run an expression from an empty initial heap. -/
def run (e : Exp) : IO Val := do
  let σ ← IO.mkRef (∅ : ExtTreeMap Loc Val)
  eval σ e

end Eval
end ProbLang
