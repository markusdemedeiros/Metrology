module

public import Metrology.ProbLang.Syntax.Syntax
public import Std.Data.ExtTreeMap.Lemmas

@[expose] public section

open Std

/-! ## A context-decomposing interpreter for ProbLang

This interpreter is structured to mirror the operational semantics as closely
as possible:

* `headStep` corresponds to `headStep : Cfg → Measure Cfg` — it handles
  exactly the head-reduction cases, operating on a redex expression together
  with a mutable heap.  Tape operations are unsupported and raise an error.

* `primStep` corresponds to `primStep` — it calls `Exp.decomp` to find the
  unique evaluation context `K` and redex `e'`, runs `headStep` on the redex
  to get a new expression `e_new`, then reassembles via `K.fill e_new`.

* `run` iterates `primStep` until the expression is a value or we get stuck/fail.
-/

namespace ProbLang
namespace EvalPrim

set_option linter.unusedSectionVars false
variable {rT : Type _} [ProbLangℝ rT]

/-- Interpreter error type. -/
inductive Error (rT : Type _)
  | fail      : Error rT
  | stuck     : String → Exp rT → Error rT
  | unsupported : String → Error rT
  | segfault  : Loc → Error rT

instance : ToString (Error rT) where
  toString
    | .fail           => "fail"
    | .stuck msg _    => s!"stuck ({msg})"
    | .segfault ℓ     => s!"segfault at location {ℓ}"
    | .unsupported msg => s!"unsupported: {msg}"

def throw' (err : Error rT) : IO α :=
  throw (IO.userError (toString err))

/-- Sample uniformly from [0, z).  Returns an error if z ≤ 0. -/
def sampleUniform (rT : Type _) [ProbLangℝ rT] (z : Int) : IO Int := do
  if 0 < z then
    return ← IO.rand 0 z.toNat
  else
    throw' (Error.stuck (rT := rT) "rand: bound must be positive" (.lit (.int z)))

/-!
### Head step

`headStep` takes a head-redex expression `e` (guaranteed by the caller to be
the innermost non-value sub-expression identified by `Exp.decomp`) together
with the current mutable heap `σ`, and returns the reduct expression.
It corresponds 1-to-1 with the cases of `headStep`.
-/

/-- The result of a single head-reduction step: a new expression and (possibly
    updated) heap.  The expression is *not* necessarily a value — it is the
    reduct of the redex, which will be spliced back into the context by
    `primStep`. -/
def headStep (σ : IO.Ref (ExtTreeMap Loc (Val rT) compare)) (e : Exp rT) : IO (Exp rT) := do
  match e with
  -- Beta reduction: app (lam e) v ↦ e[0 := v]
  | .app (.lam body) e2 =>
    return Exp.open' body e2
  -- Fix unfolding: app (fix e) v ↦ app (e[0 := fix e]) v
  | .app (.fix body) e2 =>
    return Exp.app (Exp.open' body (.fix body)) e2

  -- Unary operator: headStep (unop op e) = op.eval e
  | .unop op v =>
    match op.eval v with
    | some r => return r
    | none   => throw' (.stuck s!"unop: type error" e)

  -- Binary operator: headStep (binop op e1 e2) = op.eval e1 e2
  | .binop op v1 v2 =>
    match op.eval v1 v2 with
    | some r => return r
    | none   => throw' (.stuck s!"binop: type error" e)

  -- Conditional: headStep (cond true  et _) = et
  --              headStep (cond false _  ef) = ef
  | .cond (.lit (.bool true))  et _  => return et
  | .cond (.lit (.bool false)) _  ef => return ef

  -- Pair projections: headStep (fst (pair e1 e2)) = e1
  --                   headStep (snd (pair e1 e2)) = e2
  | .fst (.pair e1 _)  => return e1
  | .snd (.pair _ e2)  => return e2

  -- Sum elimination:
  --   headStep (case (inl e) el _)  = el.app e
  --   headStep (case (inr e) _  er) = er.app e
  | .case (.inl v) el _  => return .app el v
  | .case (.inr v) _  er => return .app er v

  -- Heap: alloc, load, store
  | .alloc vd =>
    let heap ← σ.get
    let ℓ := heap.fresh
    match vd.toVal? with
    | none    => throw' (.stuck "alloc: argument is not a value" vd)
    | some vd' =>
      σ.modify (·.insert ℓ vd')
      return .lit (.loc ℓ)

  | .load (.lit (.loc ℓ)) =>
    let heap ← σ.get
    match heap[ℓ]? with
    | none   => throw' (Error.segfault (rT := rT) ℓ)
    | some v => return .ofVal v

  | .store (.lit (.loc ℓ)) v =>
    match v.toVal? with
    | none    => throw' (.stuck "store: value argument is not a value" v)
    | some v' =>
      let heap ← σ.get
      match heap[ℓ]? with
      | none   => throw' (Error.segfault (rT := rT) ℓ)
      | some _ =>
        σ.modify (·.insert ℓ v')
        return .lit .unit

  -- Tape operations: unsupported
  | .tape _   => throw' (Error.unsupported (rT := rT) "tape allocation")
  | .rand _ (.lit (.lbl _)) => throw' (Error.unsupported (rT := rT) "rand with tape")

  -- Probabilistic sampling (no tape): headStep (rand z unit) = Uniform [0,z)
  | .rand (.lit (.int z)) (.lit .unit) =>
    let n ← sampleUniform rT z
    return .lit (.int n)

  -- Scrutinize: headStep (scrut v pat) = inl(bindings) | inr(unit)
  | .scrut v p =>
    match Pat.tryMatch p v with
    | some bindings => return .inl bindings
    | none          => return .inr (.lit .unit)

  -- Stuck / failure
  | .fail => throw' (Error.fail (rT := rT))

  | _ => throw' (.stuck "headStep: no reduction rule" e)

/-!
### Primitive step

`primStep` corresponds to `primStep`:

  primStep cfg = (headStep ⟨e', cfg.state⟩).map (fun ρ => ⟨K.fill ρ.expr, ρ.state⟩)

where `(K, e') = cfg.expr.decomp`.

Concretely:
1. Decompose `cfg.expr` into `(K, e')` using `Exp.decomp`.
2. Run `headStep` on the redex `e'`.
3. Return `K.fill e_new` as the new expression.
-/
def primStep (σ : IO.Ref (ExtTreeMap Loc (Val rT) compare)) (e : Exp rT) : IO (Exp rT) := do
  let (K, redex) := e.decomp
  let e_new ← headStep σ redex
  return K.fill e_new

/-!
### Iterated evaluation

`eval` repeatedly applies `primStep` until the expression is a value.
If `e` is already a value, return it immediately — the decomposition of a
value is `([], e)` and `headStep` would be stuck, so we check first.
-/
partial def eval (σ : IO.Ref (ExtTreeMap Loc (Val rT) compare)) (e : Exp rT) : IO (Val rT) := do
  match e.toVal? with
  | some v => return v
  | none   =>
    let e' ← primStep σ e
    eval σ e'

/-- Run an expression from an empty initial heap. -/
@[expose] def run (e : Exp rT) : IO (Val rT) := do
  let σ ← IO.mkRef (∅ : ExtTreeMap Loc (Val rT) compare)
  eval σ e

end EvalPrim
end ProbLang
