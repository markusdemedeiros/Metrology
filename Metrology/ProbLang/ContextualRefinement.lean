import Metrology.ProbLang.Syntax.Types
import Metrology.ProbLang.Exec

/-!
# Contextual refinement

Port of `theories/prob_lang/typing/contextual_refinement.v` from Clutch.

* `CtxItem` — single-frame evaluation-context holes for every expression
  constructor. Direct 1:1 port of Clutch's `ctx_item`.
* `CtxItem.fill` — plug an expression into a hole.
* `Ctx := List CtxItem`, `Ctx.fill` via `foldr` (matching Clutch).
* `TypedCtxItem` / `TypedCtx` — well-typed context frames and sequences.
* `CtxRefines Γ e e' τ` — contextual refinement: for every Bool-valued
  typed context `K`, `limExec (K[e], σ₀)` assigns no more mass to `#b`
  than `limExec (K[e'], σ₀)`. We phrase this in `ENNReal` (`limExec`
  returns an `ENNReal`-valued measure) rather than `Real` as in Clutch.

**Design note (tunfold asymmetry).** Clutch's `TFold` is a subsumption
rule (no operational content) while `TUnfold` wraps its body in
`rec_unfold := λ x, x`, so unfolding a recursive type is a real
computation step rather than a transparent rewrite. We mirror this in
`Types.lean` (`Typed.tunfold` produces `app recUnfold e`), and it
propagates here: `CTX_Fold` fills as the identity on its body, while
`CTX_Unfold` fills as `app recUnfold ·`.
-/

namespace ProbLang

open MeasureTheory

/-! ## Single-frame context items -/

/-- A single-frame evaluation-context hole. Every constructor corresponds
to a position in an `Exp` where a sub-expression could sit. -/
inductive CtxItem
  -- Base lambda calculus
  | letrec (f x : Binder)
  | appL (e2 : Exp)
  | appR (e1 : Exp)
  -- Base types and their operations
  | unop (op : UnOp)
  | binopL (op : BinOp) (e2 : Exp)
  | binopR (op : BinOp) (e1 : Exp)
  | ifL (e1 e2 : Exp)
  | ifM (e0 e2 : Exp)
  | ifR (e0 e1 : Exp)
  -- Products
  | pairL (e2 : Exp)
  | pairR (e1 : Exp)
  | fst
  | snd
  -- Sums
  | inl
  | inr
  | caseL (e1 e2 : Exp)
  | caseM (e0 e2 : Exp)
  | caseR (e0 e1 : Exp)
  -- Heap
  | alloc
  | load
  | storeL (e2 : Exp)
  | storeR (e1 : Exp)
  -- Recursive types (Fold is subsumption, Unfold wraps in `recUnfold`)
  | fold
  | unfold
  -- Polymorphic types (Λ: = letrec anon anon; TApp = app · unit)
  | tlam
  | tapp
  -- Existential types: unpack x := e in e' = app (λ x, e') e
  -- (we have no explicit PACK frame, matching Clutch)
  | unpackL (x : String) (e2 : Exp)
  | unpackR (x : String) (e1 : Exp)
  -- Tapes
  | allocTape
  | randL (e2 : Exp)
  | randR (e1 : Exp)

namespace CtxItem

/-- Fill the hole in a single context frame. -/
def fill : CtxItem → Exp → Exp
  | .letrec f x,     e => .letrec f x e
  | .appL e2,        e => .app e e2
  | .appR e1,        e => .app e1 e
  | .unop op,        e => .unop op e
  | .binopL op e2,   e => .binop op e e2
  | .binopR op e1,   e => .binop op e1 e
  | .ifL e1 e2,      e => .cond e e1 e2
  | .ifM e0 e2,      e => .cond e0 e e2
  | .ifR e0 e1,      e => .cond e0 e1 e
  | .pairL e2,       e => .pair e e2
  | .pairR e1,       e => .pair e1 e
  | .fst,            e => .fst e
  | .snd,            e => .snd e
  | .inl,            e => .inl e
  | .inr,            e => .inr e
  | .caseL e1 e2,    e => .case e e1 e2
  | .caseM e0 e2,    e => .case e0 e e2
  | .caseR e0 e1,    e => .case e0 e1 e
  | .alloc,          e => .alloc e
  | .load,           e => .load e
  | .storeL e2,      e => .store e e2
  | .storeR e1,      e => .store e1 e
  -- Fold is subsumption (Clutch: `| CTX_Fold => e`)
  | .fold,           e => e
  -- Unfold wraps in `recUnfold` (Clutch: `| CTX_Unfold => rec_unfold e`)
  | .unfold,         e => .app _root_.ProbLang.recUnfold e
  -- Λ: e = letrec anon anon e
  | .tlam,           e => .letrec .anon .anon e
  -- TApp e = app e ()
  | .tapp,           e => .app e (.lit .unit)
  -- unpack: x := e in e2 = app (λ x, e2) e
  | .unpackL x e2,   e => .app (.letrec .anon (.named x) e2) e
  | .unpackR x e1,   e => .app (.letrec .anon (.named x) e) e1
  | .allocTape,      e => .tape e
  | .randL e2,       e => .rand e e2
  | .randR e1,       e => .rand e1 e

end CtxItem

/-! ## Multi-frame contexts -/

/-- A context is a list of frames, innermost first (matching Clutch's
`foldr` convention). -/
abbrev Ctx := List CtxItem

namespace Ctx

/-- Fill the hole of a composite context. Using `foldr` matches Clutch's
`fill_ctx K e := foldr fill_ctx_item e K`: the head of the list is
applied *last*, so `[outer, ..., inner].fill e` is `outer[...[inner[e]]...]`. -/
def fill (K : Ctx) (e : Exp) : Exp := K.foldr CtxItem.fill e

@[simp] theorem fill_nil (e : Exp) : fill [] e = e := rfl

@[simp] theorem fill_cons (k : CtxItem) (K : Ctx) (e : Exp) :
    fill (k :: K) e = k.fill (K.fill e) := rfl

/-- Clutch's `fill_ctx_app`: filling by `K' ++ K` is the same as filling
by `K` and then by `K'`. Uses `foldr_append`. -/
theorem fill_append (K K' : Ctx) (e : Exp) :
    fill (K' ++ K) e = fill K' (fill K e) := by
  simp [fill, List.foldr_append]

end Ctx

/-! ## Well-typed single-frame contexts -/

/-- `TypedCtxItem k Γ τ Γ' τ'` says: plugging an expression of type `τ`
in context `Γ` into the frame `k` produces an expression of type `τ'`
in context `Γ'`. Direct 1:1 port of Clutch's `typed_ctx_item`. -/
inductive TypedCtxItem : CtxItem → Tctx → Ty → Tctx → Ty → Prop
  -- Base lambda calculus
  | letrec {Γ τ τ' f x} :
      TypedCtxItem (.letrec f x)
        ((Γ.insertB f (.arrow τ τ')).insertB x τ) τ'
        Γ (.arrow τ τ')
  | appL {Γ e2 τ τ'} :
      Typed Γ e2 τ →
      TypedCtxItem (.appL e2) Γ (.arrow τ τ') Γ τ'
  | appR {Γ e1 τ τ'} :
      Typed Γ e1 (.arrow τ τ') →
      TypedCtxItem (.appR e1) Γ τ Γ τ'
  -- Base types and operations
  | unop_int {Γ op τ} :
      op.intResTy = some τ →
      TypedCtxItem (.unop op) Γ .int Γ τ
  | unop_bool {Γ op τ} :
      op.boolResTy = some τ →
      TypedCtxItem (.unop op) Γ .bool Γ τ
  | binopL_int {Γ op e2 τ} :
      Typed Γ e2 .int → op.intResTy = some τ →
      TypedCtxItem (.binopL op e2) Γ .int Γ τ
  | binopR_int {Γ op e1 τ} :
      Typed Γ e1 .int → op.intResTy = some τ →
      TypedCtxItem (.binopR op e1) Γ .int Γ τ
  | binopL_bool {Γ op e2 τ} :
      Typed Γ e2 .bool → op.boolResTy = some τ →
      TypedCtxItem (.binopL op e2) Γ .bool Γ τ
  | binopR_bool {Γ op e1 τ} :
      Typed Γ e1 .bool → op.boolResTy = some τ →
      TypedCtxItem (.binopR op e1) Γ .bool Γ τ
  | binopL_unboxedEq {Γ e2 τ} :
      UnboxedType τ → Typed Γ e2 τ →
      TypedCtxItem (.binopL .eq e2) Γ τ Γ .bool
  | binopR_unboxedEq {Γ e1 τ} :
      UnboxedType τ → Typed Γ e1 τ →
      TypedCtxItem (.binopR .eq e1) Γ τ Γ .bool
  | ifL {Γ e1 e2 τ} :
      Typed Γ e1 τ → Typed Γ e2 τ →
      TypedCtxItem (.ifL e1 e2) Γ .bool Γ τ
  | ifM {Γ e0 e2 τ} :
      Typed Γ e0 .bool → Typed Γ e2 τ →
      TypedCtxItem (.ifM e0 e2) Γ τ Γ τ
  | ifR {Γ e0 e1 τ} :
      Typed Γ e0 .bool → Typed Γ e1 τ →
      TypedCtxItem (.ifR e0 e1) Γ τ Γ τ
  -- Products
  | pairL {Γ e2 τ τ'} :
      Typed Γ e2 τ' →
      TypedCtxItem (.pairL e2) Γ τ Γ (.prod τ τ')
  | pairR {Γ e1 τ τ'} :
      Typed Γ e1 τ →
      TypedCtxItem (.pairR e1) Γ τ' Γ (.prod τ τ')
  | fst {Γ τ τ'} :
      TypedCtxItem .fst Γ (.prod τ τ') Γ τ
  | snd {Γ τ τ'} :
      TypedCtxItem .snd Γ (.prod τ τ') Γ τ'
  -- Sums
  | inl {Γ τ τ'} :
      TypedCtxItem .inl Γ τ Γ (.sum τ τ')
  | inr {Γ τ τ'} :
      TypedCtxItem .inr Γ τ' Γ (.sum τ τ')
  | caseL {Γ e1 e2 τ1 τ2 τ'} :
      Typed Γ e1 (.arrow τ1 τ') → Typed Γ e2 (.arrow τ2 τ') →
      TypedCtxItem (.caseL e1 e2) Γ (.sum τ1 τ2) Γ τ'
  | caseM {Γ e0 e2 τ1 τ2 τ'} :
      Typed Γ e0 (.sum τ1 τ2) → Typed Γ e2 (.arrow τ2 τ') →
      TypedCtxItem (.caseM e0 e2) Γ (.arrow τ1 τ') Γ τ'
  | caseR {Γ e0 e1 τ1 τ2 τ'} :
      Typed Γ e0 (.sum τ1 τ2) → Typed Γ e1 (.arrow τ1 τ') →
      TypedCtxItem (.caseR e0 e1) Γ (.arrow τ2 τ') Γ τ'
  -- Heap
  | alloc {Γ τ} :
      TypedCtxItem .alloc Γ τ Γ (.ref τ)
  | load {Γ τ} :
      TypedCtxItem .load Γ (.ref τ) Γ τ
  | storeL {Γ e2 τ} :
      Typed Γ e2 τ → TypedCtxItem (.storeL e2) Γ (.ref τ) Γ .unit
  | storeR {Γ e1 τ} :
      Typed Γ e1 (.ref τ) → TypedCtxItem (.storeR e1) Γ τ Γ .unit
  -- Recursive & polymorphic types (fold is subsumption, unfold takes a step)
  | fold {Γ τ} :
      TypedCtxItem .fold Γ (τ.single (.rec' τ)) Γ (.rec' τ)
  | unfold {Γ τ} :
      TypedCtxItem .unfold Γ (.rec' τ) Γ (τ.single (.rec' τ))
  | tlam {Γ τ} :
      TypedCtxItem .tlam Γ.shift τ Γ (.forall' τ)
  | tapp {Γ τ τ'} :
      TypedCtxItem .tapp Γ (.forall' τ) Γ (τ.single τ')
  -- No explicit PACK frame, matching Clutch.
  | unpackL {x e2 Γ τ τ2} :
      Typed ((Γ.shift).insert x τ) e2 τ2.shift →
      TypedCtxItem (.unpackL x e2) Γ (.exists' τ) Γ τ2
  | unpackR {x e1 Γ τ τ2} :
      Typed Γ e1 (.exists' τ) →
      TypedCtxItem (.unpackR x e1)
        ((Γ.shift).insert x τ) τ2.shift Γ τ2
  -- Tapes
  | allocTape {Γ} :
      TypedCtxItem .allocTape Γ .int Γ .tape
  | randL_unit {Γ e2} :
      Typed Γ e2 .unit → TypedCtxItem (.randL e2) Γ .int Γ .int
  | randL_tape {Γ e2} :
      Typed Γ e2 .tape → TypedCtxItem (.randL e2) Γ .int Γ .int
  | randR_unit {Γ e1} :
      Typed Γ e1 .int → TypedCtxItem (.randR e1) Γ .unit Γ .int
  | randR_tape {Γ e1} :
      Typed Γ e1 .int → TypedCtxItem (.randR e1) Γ .tape Γ .int

/-! ## Well-typed multi-frame contexts -/

/-- `TypedCtx K Γ τ Γ' τ'`: the composite context `K` takes a hole of
type `τ` in `Γ` to a term of type `τ'` in `Γ'`. -/
inductive TypedCtx : Ctx → Tctx → Ty → Tctx → Ty → Prop
  | nil {Γ τ} : TypedCtx [] Γ τ Γ τ
  | cons {K k Γ1 τ1 Γ2 τ2 Γ3 τ3} :
      TypedCtxItem k Γ2 τ2 Γ3 τ3 →
      TypedCtx K Γ1 τ1 Γ2 τ2 →
      TypedCtx (k :: K) Γ1 τ1 Γ3 τ3

/-! ## Basic metatheory -/

/-- Plugging a well-typed term into a well-typed single frame produces a
well-typed term. (Clutch `typed_ctx_item_typed`.) -/
theorem TypedCtxItem.fill_typed {k : CtxItem} {Γ τ Γ' τ' e}
    (he : Typed Γ e τ) (hk : TypedCtxItem k Γ τ Γ' τ') :
    Typed Γ' (k.fill e) τ' := by
  induction hk with
  | letrec      => exact .letrec he
  | appL h2     => exact .app he h2
  | appR h1     => exact .app h1 he
  | unop_int hop       => exact .unop_int he hop
  | unop_bool hop      => exact .unop_bool he hop
  | binopL_int h2 hop  => exact .binop_int he h2 hop
  | binopR_int h1 hop  => exact .binop_int h1 he hop
  | binopL_bool h2 hop => exact .binop_bool he h2 hop
  | binopR_bool h1 hop => exact .binop_bool h1 he hop
  | binopL_unboxedEq hu h2 => exact .unboxed_eq hu he h2
  | binopR_unboxedEq hu h1 => exact .unboxed_eq hu h1 he
  | ifL h1 h2   => exact .cond he h1 h2
  | ifM h0 h2   => exact .cond h0 he h2
  | ifR h0 h1   => exact .cond h0 h1 he
  | pairL h2    => exact .pair he h2
  | pairR h1    => exact .pair h1 he
  | fst         => exact .fst he
  | snd         => exact .snd he
  | inl         => exact .inl he
  | inr         => exact .inr he
  | caseL h1 h2 => exact .case he h1 h2
  | caseM h0 h2 => exact .case h0 he h2
  | caseR h0 h1 => exact .case h0 h1 he
  | alloc       => exact .alloc he
  | load        => exact .load he
  | storeL h2   => exact .store he h2
  | storeR h1   => exact .store h1 he
  | fold        => exact .tfold he
  | unfold      => exact (.tunfold he : Typed _ (.app _root_.ProbLang.recUnfold _) _)
  | tlam        => exact .tlam he
  | tapp        => exact .tapp he
  | unpackL h2  => exact .tunpack he h2
  | unpackR h1  => exact .tunpack h1 he
  | allocTape   => exact .alloc_tape he
  | randL_unit h2 => exact .rand_unit he h2
  | randL_tape h2 => exact .rand he h2
  | randR_unit h1 => exact .rand_unit h1 he
  | randR_tape h1 => exact .rand h1 he

/-- Plugging a well-typed term into a well-typed multi-frame context
produces a well-typed term. (Clutch `typed_ctx_typed`.) -/
theorem TypedCtx.fill_typed {K : Ctx} {Γ τ Γ' τ' e}
    (he : Typed Γ e τ) (hK : TypedCtx K Γ τ Γ' τ') :
    Typed Γ' (K.fill e) τ' := by
  induction hK with
  | nil => exact he
  | cons hk _ ih => exact hk.fill_typed (ih he)

/-- Composing well-typed contexts. (Clutch `typed_ctx_compose`.) -/
theorem TypedCtx.compose {K K' : Ctx} {Γ1 Γ2 Γ3 τ1 τ2 τ3}
    (hK : TypedCtx K Γ1 τ1 Γ2 τ2) (hK' : TypedCtx K' Γ2 τ2 Γ3 τ3) :
    TypedCtx (K' ++ K) Γ1 τ1 Γ3 τ3 := by
  induction hK' with
  | nil => exact hK
  | cons hk _ ih => exact .cons hk (ih hK)

/-! ## Contextual refinement -/

/-- The set of final configurations whose expression component is the
Bool literal `b`. Used as the "observation" in `CtxRefines`. -/
def finalBool (b : Bool) : Set Cfg :=
  { ρ | ρ.expr = .lit (.bool b) }

/-- `Γ ⊨ e ≤ctx≤ e' : τ`. For every Bool-typed closing context `K` and
every initial state, the termination distribution of `K[e]` at each
Bool result is dominated by that of `K[e']`. -/
def CtxRefines (Γ : Tctx) (e e' : Exp) (τ : Ty) : Prop :=
  ∀ (K : Ctx) (σ₀ : State) (b : Bool),
    TypedCtx K Γ τ Tctx.empty .bool →
    limExec ⟨K.fill e,  σ₀⟩ (finalBool b) ≤
    limExec ⟨K.fill e', σ₀⟩ (finalBool b)

@[inherit_doc]
scoped notation Γ " ⊨ " e " ≤ctx≤ " e' " : " τ => CtxRefines Γ e e' τ

namespace CtxRefines

theorem refl {Γ τ} (e : Exp) : CtxRefines Γ e e τ := by
  intro _ _ _ _; exact le_refl _

theorem trans {Γ τ} {e1 e2 e3 : Exp}
    (h12 : CtxRefines Γ e1 e2 τ) (h23 : CtxRefines Γ e2 e3 τ) :
    CtxRefines Γ e1 e3 τ := by
  intro K σ₀ b hK
  exact (h12 K σ₀ b hK).trans (h23 K σ₀ b hK)

/-- Precongruence of contextual refinement: refinement is preserved under
any well-typed surrounding context. (Clutch `ctx_refines_congruence`.) -/
theorem congr {Γ Γ' τ τ'} {e1 e2 : Exp} {K : Ctx}
    (hK : TypedCtx K Γ τ Γ' τ')
    (href : CtxRefines Γ e1 e2 τ) :
    CtxRefines Γ' (K.fill e1) (K.fill e2) τ' := by
  intro K' σ₀ b hty
  rw [← Ctx.fill_append, ← Ctx.fill_append]
  exact href (K' ++ K) σ₀ b (hK.compose hty)

end CtxRefines

/-! ## Contextual equivalence -/

/-- Contextual equivalence: two-sided refinement. -/
def CtxEquiv (Γ : Tctx) (e1 e2 : Exp) (τ : Ty) : Prop :=
  CtxRefines Γ e1 e2 τ ∧ CtxRefines Γ e2 e1 τ

@[inherit_doc]
scoped notation Γ " ⊨ " e " =ctx= " e' " : " τ => CtxEquiv Γ e e' τ

namespace CtxEquiv

theorem refl {Γ τ} (e : Exp) : CtxEquiv Γ e e τ :=
  ⟨.refl e, .refl e⟩

theorem symm {Γ τ} {e1 e2 : Exp} (h : CtxEquiv Γ e1 e2 τ) : CtxEquiv Γ e2 e1 τ :=
  ⟨h.2, h.1⟩

theorem trans {Γ τ} {e1 e2 e3 : Exp}
    (h12 : CtxEquiv Γ e1 e2 τ) (h23 : CtxEquiv Γ e2 e3 τ) :
    CtxEquiv Γ e1 e3 τ :=
  ⟨h12.1.trans h23.1, h23.2.trans h12.2⟩

end CtxEquiv

end ProbLang
