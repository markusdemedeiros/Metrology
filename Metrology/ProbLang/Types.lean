import Metrology.ProbLang.Syntax.Syntax

/-!
# Syntactic typing for ProbLang (System F_μ_ref with tapes)

Port of `theories/prob_lang/typing/types.v` from the Clutch development
(https://github.com/logsem/clutch).

The Clutch type system uses Autosubst-derived substitution on types. Lean
doesn't have Autosubst, so we hand-roll exactly the two pieces Clutch's
`types.v` / `contextual_refinement.v` actually use:

* single-variable substitution `τ.[τ'/]` (for `TApp`, `TFold`/`TUnfold`, `TPack`);
* shift-by-one renaming (for the context shift `⤉Γ` in `TLam`/`TUnpack` and
  for the result type in `TUnpack`).

No parallel-substitution lemmas (`subst_comp`, `id_subst`, …) are proved here
— `types.v` and `contextual_refinement.v` never rewrite with them. Those will
be added on demand when `interp.v`/`fundamental.v` are ported.

Typing contexts are represented as plain partial functions `String → Option Ty`
rather than as a `stringmap`; this matches `Γ !! x = Some τ` lookup directly
and avoids pulling in finite-map machinery that the inductive typing judgment
doesn't need.
-/

namespace ProbLang

/-! ## Type-level substitution infrastructure

Only `Ty.var`/`Ty.rec'`/`Ty.forall'`/`Ty.exists'` interact with de Bruijn type
variables. Every other constructor is just structural recursion. -/

/-- Lift a renaming `ξ` under one binder: the new bound variable (index 0)
stays at 0, and every other free variable is renamed by `ξ` and shifted. -/
@[simp] def upren (ξ : Nat → Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => ξ n + 1

/-- Renaming on types: apply `ξ` to every free type variable, lifting under
each type-level binder. -/
def Ty.rename (ξ : Nat → Nat) : Ty → Ty
  | .int        => .int
  | .nat        => .nat
  | .bool       => .bool
  | .unit       => .unit
  | .tape       => .tape
  | .prod τ1 τ2 => .prod (τ1.rename ξ) (τ2.rename ξ)
  | .sum  τ1 τ2 => .sum  (τ1.rename ξ) (τ2.rename ξ)
  | .arrow τ1 τ2 => .arrow (τ1.rename ξ) (τ2.rename ξ)
  | .ref τ      => .ref (τ.rename ξ)
  | .var n      => .var (ξ n)
  | .rec' τ     => .rec'    (τ.rename (upren ξ))
  | .forall' τ  => .forall' (τ.rename (upren ξ))
  | .exists' τ  => .exists' (τ.rename (upren ξ))

/-- Lift a substitution `σ` under one binder: the new bound variable becomes
`TVar 0`, and every other entry has its free variables shifted up by one. -/
def up (σ : Nat → Ty) : Nat → Ty
  | 0     => .var 0
  | n + 1 => (σ n).rename (· + 1)

/-- Parallel substitution on types. -/
def Ty.subst (σ : Nat → Ty) : Ty → Ty
  | .int        => .int
  | .nat        => .nat
  | .bool       => .bool
  | .unit       => .unit
  | .tape       => .tape
  | .prod τ1 τ2 => .prod (τ1.subst σ) (τ2.subst σ)
  | .sum  τ1 τ2 => .sum  (τ1.subst σ) (τ2.subst σ)
  | .arrow τ1 τ2 => .arrow (τ1.subst σ) (τ2.subst σ)
  | .ref τ      => .ref (τ.subst σ)
  | .var n      => σ n
  | .rec' τ     => .rec'    (τ.subst (up σ))
  | .forall' τ  => .forall' (τ.subst (up σ))
  | .exists' τ  => .exists' (τ.subst (up σ))

/-- Single-variable substitution `τ.[τ'/]`: substitute `τ'` for de Bruijn
index 0 and leave every other index alone. -/
def Ty.single (τ' τ : Ty) : Ty :=
  τ.subst (fun n => match n with | 0 => τ' | k + 1 => .var k)

/-- Shift every free type variable up by one. Used for the context shift
`⤉Γ` and for the result type in `TUnpack`. -/
def Ty.shift (τ : Ty) : Ty := τ.rename (· + 1)

/-! ## Unboxed and equality types

Auxiliary inductives from `types.v`. `UnboxedType` characterizes types that
may be held in a `ref` and compared by CAS; `EqType` characterizes types
supporting direct equality tests. -/

/-- Types which are "unboxed" (scalar or `ref`): we can CAS on references
holding values of an unboxed type. -/
inductive UnboxedType : Ty → Prop
  | unit                           : UnboxedType .unit
  | nat                            : UnboxedType .nat
  | int                            : UnboxedType .int
  | bool                           : UnboxedType .bool
  | ref (τ : Ty)                   : UnboxedType (.ref τ)

/-- Types supporting syntactic equality (for direct `eq` comparison). -/
inductive EqType : Ty → Prop
  | unit                           : EqType .unit
  | nat                            : EqType .nat
  | int                            : EqType .int
  | bool                           : EqType .bool
  | prod {τ τ'}                    : EqType τ → EqType τ' → EqType (.prod τ τ')
  | sum  {τ τ'}                    : EqType τ → EqType τ' → EqType (.sum τ τ')

theorem unboxed_type_ref_or_eqtype {τ : Ty} (h : UnboxedType τ) :
    EqType τ ∨ (∃ τ', τ = .ref τ') ∨ τ = .tape := by
  cases h with
  | unit  => exact .inl .unit
  | nat   => exact .inl .nat
  | int   => exact .inl .int
  | bool  => exact .inl .bool
  | ref τ => exact .inr (.inl ⟨τ, rfl⟩)

/-! ## Operator result types

The type system maps `BinOp`/`UnOp` codes to the result type of the
operator when applied to integer or boolean operands. Our `BinOp` is a
strict subset of Clutch's, so these are shorter than in `types.v`. -/

/-- Result type when both operands are integers (in the "int mode"). -/
def BinOp.intResTy : BinOp → Option Ty
  | .plus | .minus | .mult  => some .int
  | .and  | .or    | .xor   => none
  | .eq                     => some .bool

/-- Result type when both operands are booleans (in the "bool mode"). -/
def BinOp.boolResTy : BinOp → Option Ty
  | .plus | .minus | .mult  => none
  | .and  | .or    | .xor   => some .bool
  | .eq                     => some .bool

/-- Result type when the operand is an integer. -/
def UnOp.intResTy : UnOp → Option Ty
  | .neg   => none
  | .minus => some .int

/-- Result type when the operand is a boolean. -/
def UnOp.boolResTy : UnOp → Option Ty
  | .neg   => some .bool
  | .minus => none

/-! ## Typing contexts -/

/-- Typing context: partial map from variable names to their types. -/
abbrev Tctx := String → Option Ty

namespace Tctx

/-- Empty context. -/
def empty : Tctx := fun _ => none

/-- Extend a context: `Γ[x ↦ τ]`. A fresh name overrides any previous binding. -/
def insert (Γ : Tctx) (x : String) (τ : Ty) : Tctx :=
  fun y => if y = x then some τ else Γ y

/-- Extend a context with a `Binder`: `named`/`typed` insert, `anon` is a no-op.
This mirrors Clutch's `binder_insert`. -/
def insertB (Γ : Tctx) : Binder → Ty → Tctx
  | .anon,       _ => Γ
  | .named x,    τ => Γ.insert x τ
  | .typed x _,  τ => Γ.insert x τ

/-- Shift every type in the context by one (in the type-variable de Bruijn
namespace). Used by `TLam` and `TUnpack` when a fresh type variable is
introduced. -/
def shift (Γ : Tctx) : Tctx := fun x => (Γ x).map Ty.shift

end Tctx

/-! ## Type-level sugar as plain expressions

Clutch's `types.v` uses a few pieces of notational sugar:

* `Λ: e := λ: <>, e` — a thunk (our `letrec .anon .anon e`).
* `TApp e := App e #()` — our `app e (.lit .unit)`.
* `rec_unfold := λ x, x` — the identity-at-type-`μ`, used by `TUnfold` so
  that unfolding a recursive type takes a real computation step.
* `unpack: x := e1 in e2 := (λ x, e2) e1` — our
  `app (letrec .anon (.named x) e2) e1`.

`Λ:`, `TApp`, and `unpack` are inlined directly in the typing rules. We
materialize `rec_unfold` as a closed expression because (unlike the
notational-sugar cases) it is referenced by both the typing rule and the
contextual refinement fill semantics, so it is easier to name it once. -/

/-- The `rec_unfold` value: `λ x, x`. Used by `Typed.tunfold` so that
unfolding a recursive type is a real computation step rather than a
subsumption rule. -/
def recUnfold : Exp :=
  .letrec .anon (.named "x") (.var "x")


/-! ## Typing judgment

A direct port of Clutch's `Inductive typed`. Differences from `types.v`:

* We have no separate `val_typed` judgment: our values are carved out of `Exp`
  via `IsVal`, and Clutch's `Val_typed Γ v τ` just wraps `⊢ᵥ v : τ`. We fold
  that into the same `typed` relation and require a side condition `IsVal e`
  where needed. (For the first port we simply drop the val-only rules; the
  fundamental theorem will fold them back in later if necessary.)
* Type-level `Λ:` and `TApp` are notational sugar in Clutch (`λ <>, e`
  and `App e #()`). We inline the desugaring directly:
    * `Λ: e  ↝  letrec .anon .anon e` (a thunk)
    * `TApp e ↝ app e (lit .unit)`
* `unpack: x := e1 in e2` desugars to `app (λ x, e2) e1`, which on our
  syntax is `app (letrec .anon (.named x) e2) e1`.
* `BAllocTape` uses our `Exp.tape`, and `Rand` uses our `Exp.rand`. Our
  `rand` takes the bound and a tape expression; Clutch has both the tape
  and the "no-tape" variant — we encode the no-tape variant as `rand` with
  a unit argument in the `TRandU` rule below.
* Clutch's `Subsume_int_nat` rule is retained.
-/

/-- `Γ ⊢ₜ e : τ` — the expression `e` has type `τ` in context `Γ`. -/
inductive Typed : Tctx → Exp → Ty → Prop
  | var {Γ x τ} :
      Γ x = some τ →
      Typed Γ (.var x) τ
  | lit_int  {Γ z} : Typed Γ (.lit (.int z)) .int
  | lit_nat  {Γ : Tctx} {n : Nat} : Typed Γ (.lit (.int (n : Int))) .nat
  | lit_bool {Γ b} : Typed Γ (.lit (.bool b)) .bool
  | lit_unit {Γ}   : Typed Γ (.lit .unit)     .unit
  | binop_int {Γ op e1 e2 τ} :
      Typed Γ e1 .int → Typed Γ e2 .int →
      op.intResTy = some τ →
      Typed Γ (.binop op e1 e2) τ
  | binop_bool {Γ op e1 e2 τ} :
      Typed Γ e1 .bool → Typed Γ e2 .bool →
      op.boolResTy = some τ →
      Typed Γ (.binop op e1 e2) τ
  | unop_int {Γ op e τ} :
      Typed Γ e .int → op.intResTy = some τ →
      Typed Γ (.unop op e) τ
  | unop_bool {Γ op e τ} :
      Typed Γ e .bool → op.boolResTy = some τ →
      Typed Γ (.unop op e) τ
  | unboxed_eq {Γ e1 e2 τ} :
      UnboxedType τ →
      Typed Γ e1 τ → Typed Γ e2 τ →
      Typed Γ (.binop .eq e1 e2) .bool
  | pair {Γ e1 e2 τ1 τ2} :
      Typed Γ e1 τ1 → Typed Γ e2 τ2 →
      Typed Γ (.pair e1 e2) (.prod τ1 τ2)
  | fst {Γ e τ1 τ2} :
      Typed Γ e (.prod τ1 τ2) → Typed Γ (.fst e) τ1
  | snd {Γ e τ1 τ2} :
      Typed Γ e (.prod τ1 τ2) → Typed Γ (.snd e) τ2
  | inl {Γ e τ1 τ2} :
      Typed Γ e τ1 → Typed Γ (.inl e) (.sum τ1 τ2)
  | inr {Γ e τ1 τ2} :
      Typed Γ e τ2 → Typed Γ (.inr e) (.sum τ1 τ2)
  | case {Γ e0 e1 e2 τ1 τ2 τ3} :
      Typed Γ e0 (.sum τ1 τ2) →
      Typed Γ e1 (.arrow τ1 τ3) →
      Typed Γ e2 (.arrow τ2 τ3) →
      Typed Γ (.case e0 e1 e2) τ3
  | cond {Γ e0 e1 e2 τ} :
      Typed Γ e0 .bool →
      Typed Γ e1 τ → Typed Γ e2 τ →
      Typed Γ (.cond e0 e1 e2) τ
  | letrec {Γ f x e τ1 τ2} :
      Typed ((Γ.insertB f (.arrow τ1 τ2)).insertB x τ1) e τ2 →
      Typed Γ (.letrec f x e) (.arrow τ1 τ2)
  | app {Γ e1 e2 τ1 τ2} :
      Typed Γ e1 (.arrow τ1 τ2) →
      Typed Γ e2 τ1 →
      Typed Γ (.app e1 e2) τ2
  /-- `Λ: e` = `letrec anon anon e`, typed at `∀: τ` when `e` has type `τ`
  in the shifted context. -/
  | tlam {Γ e τ} :
      Typed Γ.shift e τ →
      Typed Γ (.letrec .anon .anon e) (.forall' τ)
  /-- `TApp e` = `app e ()`. Instantiates the body `τ` with `τ'`. -/
  | tapp {Γ e τ τ'} :
      Typed Γ e (.forall' τ) →
      Typed Γ (.app e (.lit .unit)) (τ.single τ')
  | tfold {Γ e τ} :
      Typed Γ e (τ.single (.rec' τ)) →
      Typed Γ e (.rec' τ)
  /-- Clutch asymmetry: `TFold` is a subsumption rule (no operational content),
  but `TUnfold` wraps `e` in `rec_unfold := λ x, x` so that unfolding takes a
  computation step. This matters for refinement: it prevents an `unfold` from
  being refined away past a diverging `fold`. We mirror it here by making
  unfold produce `app recUnfold e`. -/
  | tunfold {Γ e τ} :
      Typed Γ e (.rec' τ) →
      Typed Γ (.app recUnfold e) (τ.single (.rec' τ))
  | tpack {Γ e τ τ'} :
      Typed Γ e (τ.single τ') →
      Typed Γ e (.exists' τ)
  /-- `unpack: x := e1 in e2` desugared as `app (λ x, e2) e1`, which is
  `app (letrec .anon (.named x) e2) e1`. The result type `τ2` must not
  depend on the fresh type variable, hence the shift. -/
  | tunpack {Γ e1 x e2 τ τ2} :
      Typed Γ e1 (.exists' τ) →
      Typed ((Γ.shift).insert x τ) e2 τ2.shift →
      Typed Γ (.app (.letrec .anon (.named x) e2) e1) τ2
  | alloc {Γ e τ} :
      Typed Γ e τ → Typed Γ (.alloc e) (.ref τ)
  | load {Γ e τ} :
      Typed Γ e (.ref τ) → Typed Γ (.load e) τ
  | store {Γ e e' τ} :
      Typed Γ e (.ref τ) → Typed Γ e' τ →
      Typed Γ (.store e e') .unit
  | alloc_tape {Γ e} :
      Typed Γ e .nat → Typed Γ (.tape e) .tape
  | rand {Γ e1 e2} :
      Typed Γ e1 .nat → Typed Γ e2 .tape →
      Typed Γ (.rand e1 e2) .nat
  | rand_unit {Γ e1 e2} :
      Typed Γ e1 .nat → Typed Γ e2 .unit →
      Typed Γ (.rand e1 e2) .nat
  /-- Nat is a subtype of Int. -/
  | subsume_int_nat {Γ e} :
      Typed Γ e .nat → Typed Γ e .int

@[inherit_doc] scoped notation Γ " ⊢ₜ " e " : " τ => Typed Γ e τ

end ProbLang
