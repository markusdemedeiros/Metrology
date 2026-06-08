module

public import Metrology.ProbLang.Syntax.Types
public import Metrology.ProbLang.Exec

@[expose] public section

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


variable {rT : Type _} [ProbLangℝ rT]

open MeasureTheory

/-! ## Single-frame context items -/

/-- A single-frame evaluation-context hole. Every constructor corresponds
to a position in an `Exp` where a sub-expression could sit.

Under locally-nameless, binder frames carry the atoms to close over. For
`lam x` the hole is the body (open at `x`); `fill` closes: `.lam (close hole x)`.
`fix f` is similar. The Clutch `letrec f x body` corresponds to `fix f .
lam x . body`, i.e. two nested `CtxItem` frames: `fix f :: lam x :: K`. -/
inductive CtxItem (rT : Type _) [ProbLangℝ rT]
  -- Base lambda calculus: `lam x` frame takes body open at atom `x`.
  | lam (x : Var)
  -- `fix f` frame: body is a `.lam …` open at recursive atom `f`.
  | fix (f : Var)
  -- `Λ` frame (anonymous lam for type abstraction).
  | tlam
  | appL (e2 : Exp rT)
  | appR (e1 : Exp rT)
  -- Base types and their operations
  | unop (op : UnOp)
  | binopL (op : BinOp) (e2 : Exp rT)
  | binopR (op : BinOp) (e1 : Exp rT)
  | ifL (e1 e2 : Exp rT)
  | ifM (e0 e2 : Exp rT)
  | ifR (e0 e1 : Exp rT)
  -- Products
  | pairL (e2 : Exp rT)
  | pairR (e1 : Exp rT)
  | fst
  | snd
  -- Sums
  | inl
  | inr
  | caseL (e1 e2 : Exp rT)
  | caseM (e0 e2 : Exp rT)
  | caseR (e0 e1 : Exp rT)
  -- Heap
  | alloc
  | load
  | storeL (e2 : Exp rT)
  | storeR (e1 : Exp rT)
  -- Recursive types (Fold is subsumption, Unfold wraps in `recUnfold`)
  | fold
  | unfold
  -- TApp = app · unit
  | tapp
  -- Existential types: unpack x := e in e2 = app (lam e2_closed_over_x) e.
  -- `unpackL x e2`: hole fills in for the `e` scrutinee; `x` atom says how
  -- to close `e2` into a lam. `unpackR x e1`: hole fills in for the body
  -- `e2` (which is open at `x`); `e1` is the scrutinee.
  | unpackL (x : Var) (e2 : Exp rT)
  | unpackR (x : Var) (e1 : Exp rT)
  -- Tapes
  | allocTape
  | randL (e2 : Exp rT)
  | randR (e1 : Exp rT)

namespace CtxItem

/-- Fill the hole in a single context frame. -/
def fill : CtxItem rT → Exp rT → Exp rT
  -- LN binders: close the hole over the stored atom.
  | .lam x,          e => .lam (Exp.close e x)
  | .fix f,          e => .fix (Exp.close e f)
  -- tlam is an anonymous `lam`: the hole body doesn't reference the binder.
  | .tlam,           e => .lam e
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
  -- TApp e = app e ()
  | .tapp,           e => .app e (.lit .unit)
  -- unpack: x := e in e2 = app (lam (close e2 x)) e
  -- unpackL: hole is the scrutinee `e`; `e2` already stored.
  | .unpackL x e2,   e => .app (.lam (Exp.close e2 x)) e
  -- unpackR: hole is the body `e2` (open at `x`); `e1` is the scrutinee.
  | .unpackR x e1,   e => .app (.lam (Exp.close e x)) e1
  | .allocTape,      e => .tape e
  | .randL e2,       e => .rand e e2
  | .randR e1,       e => .rand e1 e

end CtxItem

/-! ## Multi-frame contexts -/

/-- A context is a list of frames, innermost first (matching Clutch's
`foldr` convention). -/
abbrev Ctx (rT : Type _) [ProbLangℝ rT] := List (CtxItem rT)

namespace Ctx

/-- Fill the hole of a composite context. Using `foldr` matches Clutch's
`fill_ctx K e := foldr fill_ctx_item e K`: the head of the list is
applied *last*, so `[outer, ..., inner].fill e` is `outer[...[inner[e]]...]`. -/
def fill (K : Ctx rT) (e : Exp rT) : Exp rT := K.foldr CtxItem.fill e

@[simp] theorem fill_nil (e : Exp rT) : fill ([] : Ctx rT) e = e := rfl

@[simp] theorem fill_cons (k : CtxItem rT) (K : Ctx rT) (e : Exp rT) :
    fill (k :: K) e = k.fill (K.fill e) := rfl

/-- Clutch's `fill_ctx_app`: filling by `K' ++ K` is the same as filling
omit [Countable rT] [MeasurableSingletonClass rT] in
by `K` and then by `K'`. Uses `foldr_append`. -/
theorem fill_append (K K' : Ctx rT) (e : Exp rT) :
    fill (K' ++ K) e = fill K' (fill K e) := by
  simp [fill, List.foldr_append]

end Ctx

/-! ## Well-typed single-frame contexts -/

/-- `TypedCtxItem k Γ τ Γ' τ'` says: plugging an expression of type `τ`
in context `Γ` into the frame `k` produces an expression of type `τ'`
in context `Γ'`. Direct 1:1 port of Clutch's `typed_ctx_item`. -/
inductive TypedCtxItem : CtxItem rT → Tctx → Ty → Tctx → Ty → Prop
  -- Base lambda calculus: `lam x` (open at `x : τ1`) producing `τ1 → τ2`.
  -- The atom `x` must not appear free in the hole (a freshness invariant
  -- that callers must establish; trivially true for elaborator-built holes).
  | lam {Γ x τ τ'} :
      TypedCtxItem (.lam x) (Γ.insert x τ) τ' Γ (.arrow τ τ')
  -- `fix f`: body has type `τ → τ'` open at `f : τ → τ'`.
  | fix {Γ f τ τ'} :
      TypedCtxItem (.fix f) (Γ.insert f (.arrow τ τ')) (.arrow τ τ')
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
  -- No explicit PACK frame, matching Clutch. The freshness premise
  -- `x ∉ e2.fv` is required to discharge the cofinite premise of
  -- `Typed.tunpack` when `fill_typed` plugs an expression in.
  | unpackL {x : Var} {e2 Γ τ τ2} :
      x ∉ e2.fv →
      Typed ((Γ.shift).insert x τ) e2 τ2.shift →
      TypedCtxItem (.unpackL x e2) Γ (.exists' τ) Γ τ2
  | unpackR {x : Var} {e1 Γ τ τ2} :
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
inductive TypedCtx : Ctx rT → Tctx → Ty → Tctx → Ty → Prop
  | nil {Γ τ} : TypedCtx [] Γ τ Γ τ
  | cons {K k Γ1 τ1 Γ2 τ2 Γ3 τ3} :
      TypedCtxItem k Γ2 τ2 Γ3 τ3 →
      TypedCtx K Γ1 τ1 Γ2 τ2 →
      TypedCtx (k :: K) Γ1 τ1 Γ3 τ3

/-! ## Basic metatheory -/

/-- Atoms appearing as binder positions in a context frame. Used to state
    freshness preconditions on the hole expression. -/
def CtxItem.binderAtoms : CtxItem rT → Finset Var
  | .lam x => {x}
  | .fix f => {f}
  | .unpackL x _ => {x}
  | .unpackR x _ => {x}
  | _ => ∅

/-- Free variables of any expressions stored in the frame's payload. -/
def CtxItem.payloadFv : CtxItem rT → Finset Var
  | .appL e2 => e2.fv
  | .appR e1 => e1.fv
  | .binopL _ e2 => e2.fv
  | .binopR _ e1 => e1.fv
  | .ifL e1 e2 => e1.fv ∪ e2.fv
  | .ifM e0 e2 => e0.fv ∪ e2.fv
  | .ifR e0 e1 => e0.fv ∪ e1.fv
  | .pairL e2 => e2.fv
  | .pairR e1 => e1.fv
  | .caseL e1 e2 => e1.fv ∪ e2.fv
  | .caseM e0 e2 => e0.fv ∪ e2.fv
  | .caseR e0 e1 => e0.fv ∪ e1.fv
  | .storeL e2 => e2.fv
  | .storeR e1 => e1.fv
  | .unpackL _ e2 => e2.fv
  | .unpackR _ e1 => e1.fv
  | .randL e2 => e2.fv
  | .randR e1 => e1.fv
  | _ => ∅

/-- Closing a free variable can only remove atoms from the fv set. -/
theorem Exp.closeRec_fv_subset (e : Exp α) (x : Var) (k : Nat) (y : Var)
    (hy : y ∈ (Exp.closeRec k x e).fv) : y ∈ e.fv := by
  induction e generalizing k with
  | bvar _ => simp [Exp.closeRec, Exp.fv] at hy
  | fvar z =>
      simp [Exp.closeRec] at hy
      by_cases hxz : x = z
      · rw [if_pos hxz] at hy; simp [Exp.fv] at hy
      · rw [if_neg hxz] at hy; exact hy
  | lit _ | fail => simp [Exp.closeRec, Exp.fv] at hy
  | lam e ih | fix e ih =>
      simp only [Exp.closeRec, Exp.fv] at hy ⊢
      exact ih (k+1) hy
  | unop _ e ih | fst e ih | snd e ih
  | inl e ih | inr e ih | alloc e ih | load e ih | tape e ih | scrut e _ ih =>
      simp only [Exp.closeRec, Exp.fv] at hy ⊢
      exact ih k hy
  | app e1 e2 ih1 ih2 | binop _ e1 e2 ih1 ih2 | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2 | rand e1 e2 ih1 ih2 =>
      simp only [Exp.closeRec, Exp.fv, Finset.mem_union] at hy ⊢
      rcases hy with h | h
      · exact .inl (ih1 k h)
      · exact .inr (ih2 k h)
  | cond e0 e1 e2 ih0 ih1 ih2 | case e0 e1 e2 ih0 ih1 ih2 =>
      simp only [Exp.closeRec, Exp.fv, Finset.mem_union] at hy ⊢
      rcases hy with (h | h) | h
      · exact .inl (.inl (ih0 k h))
      · exact .inl (.inr (ih1 k h))
      · exact .inr (ih2 k h)

theorem Exp.close_fv_subset (e : Exp α) (x : Var) : (Exp.close e x).fv ⊆ e.fv :=
  fun y hy => Exp.closeRec_fv_subset e x 0 y hy

/-- The free variables of `k.fill body` are contained in the union of
    `k`'s payload fvs and the body's fvs (binder-induced removals only
    decrease the set). -/
theorem CtxItem.fv_fill_subset (k : CtxItem rT) (body : Exp rT) :
    (k.fill body).fv ⊆ k.payloadFv ∪ body.fv := by
  intro y hy
  cases k <;>
    simp only [CtxItem.fill, CtxItem.payloadFv, Exp.fv,
      Finset.mem_union, Finset.empty_union, ProbLang.recUnfold] at hy ⊢
  all_goals first
    | tauto
    | (rename_i x; exact Exp.close_fv_subset _ x hy)
    | (rename_i x e2; rcases hy with h | h
       · exact Or.inl (Exp.close_fv_subset _ x h)
       · exact Or.inr h)
    | (rename_i x e1; rcases hy with h | h
       · exact Or.inr (Exp.close_fv_subset _ x h)
       · exact Or.inl h)

/-- Plugging a well-typed term into a well-typed single frame produces a
well-typed term. (Clutch `typed_ctx_item_typed`.)

For the binder frames (`lam`/`fix`/`unpackL`/`unpackR`), this requires the
frame's binder atom to be fresh in the hole. Elaborator-built frames
satisfy this automatically since binder atoms come from the `freshAtom`
omit [Countable rT] [MeasurableSingletonClass rT] in
counter and never appear in user expressions. -/
theorem TypedCtxItem.fill_typed {k : CtxItem rT} {Γ τ Γ' τ'} {e : Exp rT}
    (he : Typed Γ e τ) (hk : TypedCtxItem k Γ τ Γ' τ')
    (hfresh : ∀ x ∈ k.binderAtoms, x ∉ e.fv) :
    Typed Γ' (k.fill e) τ' := by
  induction hk with
  | @lam Γ x τ τ' =>
      have hxfv : x ∉ e.fv := hfresh x (by simp [CtxItem.binderAtoms])
      exact Typed.lam (insert x e.fv) (Typed.rename_lam hxfv he)
  | @fix Γ f τ τ' =>
      have hffv : f ∉ e.fv := hfresh f (by simp [CtxItem.binderAtoms])
      exact Typed.fix (insert f e.fv) (Typed.rename_fix hffv he)
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
  | @unpackL x e2 Γ τ τ2 hxfv h2 =>
      -- The constructor now carries `hxfv : x ∉ e2.fv` directly.
      exact Typed.tunpack (insert x e2.fv) he (Typed.rename_unpack hxfv h2)
  | @unpackR x e1 Γ τ τ2 h1 =>
      have hxfv : x ∉ e.fv := hfresh x (by simp [CtxItem.binderAtoms])
      exact Typed.tunpack (insert x e.fv) h1 (Typed.rename_unpack hxfv he)
  | allocTape   => exact .alloc_tape he
  | randL_unit h2 => exact .rand_unit he h2
  | randL_tape h2 => exact .rand he h2
  | randR_unit h1 => exact .rand_unit h1 he
  | randR_tape h1 => exact .rand h1 he

/-- Atoms appearing as binders in any frame of a multi-frame context. -/
def Ctx.binderAtoms (K : Ctx rT) : Finset Var :=
  K.foldr (fun k acc => k.binderAtoms ∪ acc) ∅

/-- Free variables of payloads across all frames in a multi-frame context. -/
def Ctx.payloadFv (K : Ctx rT) : Finset Var :=
  K.foldr (fun k acc => k.payloadFv ∪ acc) ∅

/-- Multi-frame fv bound: fvs of `K.fill e` are bounded by payload fvs + fvs of `e`. -/
theorem Ctx.fv_fill_subset (K : Ctx rT) (e : Exp rT) :
    (K.fill e).fv ⊆ Ctx.payloadFv K ∪ e.fv := by
  induction K with
  | nil => intro y hy; exact Finset.mem_union_right _ hy
  | cons k K ih =>
      intro y hy
      simp only [Ctx.fill, List.foldr_cons] at hy
      have hk := CtxItem.fv_fill_subset k (K.foldr CtxItem.fill e) hy
      simp only [Ctx.payloadFv, List.foldr_cons, Finset.mem_union] at hk ⊢
      rcases hk with h | h
      · exact Or.inl (Or.inl h)
      · have := ih h
        simp only [Finset.mem_union] at this
        rcases this with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

/-- Plugging a well-typed term into a well-typed multi-frame context
produces a well-typed term. (Clutch `typed_ctx_typed`.)

Requires every binder atom in the context to be fresh in both the hole
and the surrounding frame payloads. -/
theorem TypedCtx.fill_typed {K : Ctx rT} {Γ τ Γ' τ'} {e : Exp rT}
    (he : Typed Γ e τ) (hK : TypedCtx K Γ τ Γ' τ')
    (hfresh : ∀ x ∈ Ctx.binderAtoms K, x ∉ e.fv ∧ x ∉ Ctx.payloadFv K) :
    Typed Γ' (K.fill e) τ' := by
  induction hK with
  | nil => exact he
  | @cons K k Γ1 τ1 Γ2 τ2 Γ3 τ3 hk hKrest ih =>
      have hfreshK : ∀ x ∈ Ctx.binderAtoms K, x ∉ e.fv ∧ x ∉ Ctx.payloadFv K := by
        intro x hx
        have hxmem : x ∈ Ctx.binderAtoms (k :: K) := by
          simp [Ctx.binderAtoms, List.foldr_cons, Finset.mem_union]; exact Or.inr hx
        obtain ⟨hxe, hxpay⟩ := hfresh x hxmem
        refine ⟨hxe, ?_⟩
        intro h
        apply hxpay
        simp [Ctx.payloadFv, List.foldr_cons, Finset.mem_union]; exact Or.inr h
      have hIH : Typed Γ2 (K.fill e) τ2 := ih he hfreshK
      have hfreshk : ∀ x ∈ k.binderAtoms, x ∉ (K.fill e).fv := by
        intro x hx
        have hxmem : x ∈ Ctx.binderAtoms (k :: K) := by
          simp [Ctx.binderAtoms, List.foldr_cons, Finset.mem_union]; exact Or.inl hx
        obtain ⟨hxe, hxpay⟩ := hfresh x hxmem
        intro hfv
        rcases Finset.mem_union.mp (Ctx.fv_fill_subset K e hfv) with h | h
        · apply hxpay
          simp [Ctx.payloadFv, List.foldr_cons, Finset.mem_union]; exact Or.inr h
        · exact hxe h
      show Typed Γ3 (k.fill (K.fill e)) τ3
      exact TypedCtxItem.fill_typed hIH hk hfreshk

/-- Composing well-typed contexts. (Clutch `typed_ctx_compose`.) -/
theorem TypedCtx.compose {K K' : Ctx rT} {Γ1 Γ2 Γ3 τ1 τ2 τ3}
    (hK : TypedCtx K Γ1 τ1 Γ2 τ2) (hK' : TypedCtx K' Γ2 τ2 Γ3 τ3) :
    TypedCtx (K' ++ K) Γ1 τ1 Γ3 τ3 := by
  induction hK' with
  | nil => exact hK
  | cons hk _ ih => exact .cons hk (ih hK)

/-! ## Contextual refinement -/

/-- The set of final configurations whose expression component is the
Bool literal `b`. Used as the "observation" in `CtxRefines`. -/
def finalBool (b : Bool) : Set (Cfg rT) :=
  { ρ | ρ.expr = .lit (.bool b) }

/-- `Γ ⊨ e ≤ctx≤ e' : τ`. For every Bool-typed closing context `K` and
every initial state, the termination distribution of `K[e]` at each
Bool result is dominated by that of `K[e']`. -/
def CtxRefines (Γ : Tctx) (e e' : Exp rT) (τ : Ty) : Prop :=
  ∀ (K : Ctx rT) (σ₀ : State rT) (b : Bool),
    TypedCtx K Γ τ Tctx.empty .bool →
    limExec ⟨K.fill e,  σ₀⟩ (finalBool b) ≤
    limExec ⟨K.fill e', σ₀⟩ (finalBool b)

@[inherit_doc]
scoped notation Γ " ⊨ " e " ≤ctx≤ " e' " : " τ => CtxRefines Γ e e' τ

namespace CtxRefines

theorem refl {Γ τ} (e : Exp rT) : CtxRefines Γ e e τ := by
  intro _ _ _ _; exact le_refl _

theorem trans {Γ τ} {e1 e2 e3 : Exp rT}
    (h12 : CtxRefines Γ e1 e2 τ) (h23 : CtxRefines Γ e2 e3 τ) :
    CtxRefines Γ e1 e3 τ := by
  intro K σ₀ b hK
  exact (h12 K σ₀ b hK).trans (h23 K σ₀ b hK)

/-- Precongruence of contextual refinement: refinement is preserved under
any well-typed surrounding context. (Clutch `ctx_refines_congruence`.) -/
theorem congr {Γ Γ' τ τ'} {e1 e2 : Exp rT} {K : Ctx rT}
    (hK : TypedCtx K Γ τ Γ' τ')
    (href : CtxRefines Γ e1 e2 τ) :
    CtxRefines Γ' (K.fill e1) (K.fill e2) τ' := by
  intro K' σ₀ b hty
  rw [← Ctx.fill_append, ← Ctx.fill_append]
  exact href (K' ++ K) σ₀ b (hK.compose hty)

end CtxRefines

/-! ## Contextual equivalence -/

/-- Contextual equivalence: two-sided refinement. -/
def CtxEquiv (Γ : Tctx) (e1 e2 : Exp rT) (τ : Ty) : Prop :=
  CtxRefines Γ e1 e2 τ ∧ CtxRefines Γ e2 e1 τ

@[inherit_doc]
scoped notation Γ " ⊨ " e " =ctx= " e' " : " τ => CtxEquiv Γ e e' τ

namespace CtxEquiv

theorem refl {Γ τ} (e : Exp rT) : CtxEquiv Γ e e τ :=
  ⟨.refl e, .refl e⟩

theorem symm {Γ τ} {e1 e2 : Exp rT} (h : CtxEquiv Γ e1 e2 τ) : CtxEquiv Γ e2 e1 τ :=
  ⟨h.2, h.1⟩

theorem trans {Γ τ} {e1 e2 e3 : Exp rT}
    (h12 : CtxEquiv Γ e1 e2 τ) (h23 : CtxEquiv Γ e2 e3 τ) :
    CtxEquiv Γ e1 e3 τ :=
  ⟨h12.1.trans h23.1, h23.2.trans h12.2⟩

end CtxEquiv

end ProbLang
