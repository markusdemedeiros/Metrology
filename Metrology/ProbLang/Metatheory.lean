import Metrology.ProbLang.DetStep
import Metrology.ProbLang.Exec

/-!
# Metatheory for ProbLang

Port of `theories/prob_lang/metatheory.v` from Clutch. We port three
self-contained groups of material:

* **Group A** — closed-ness and parallel substitution: `Exp.isClosed`,
  `Exp.substMap`, weakening/substitution lemmas. Purely syntactic, no
  probability content.
* **Group D** — deterministic / probabilistic head-step characterization:
  `DetHeadStepPred`, `ProbHeadStepPred`, `HeadStepPred`, a Boolean test
  `isDetHeadStep`, and the partitioning lemma
  `det_or_prob_or_zero`. We reuse our existing `HeadStepSupport`
  (from `HeadStep.lean`) as the Clutch `head_step_rel` / `det_head_step_rel`
  relation — no duplicate inductive.
* **Group E** — tape and fresh-location update lemmas:
  `upd_diff_tape_comm`, `fresh_loc_upd_some`, `fresh_loc_upd_swap`,
  `headStep_zero_upd_tapes`, `detHeadStep_upd_tapes`, and the
  empty-tape / no-tape interchange `primStep_empty_tape`.

**Omissions from Clutch:**
* Laplace-related material (`AllocTapeLaplace`, `Laplace`, `Tick` —
  not in our port).
* Value-reduction cases (`RecDS`, `PairDS`, `InjLDS`, `InjRDS`) — our
  `Exp` has no separate `Val` type and values live inside `Exp` via
  `IsVal`, so there is no "rec-to-recV" reduction step.
* Groups B/C (coupling-specific metatheory) — deferred until the
  coupling-rules layer lands.

**Representation choices:**
* Closed-ness sets and substitution maps are plain functions
  (`String → Bool`, `String → Option Exp`), matching the `Tctx` idiom
  in `Types.lean` and avoiding a dependency on `Std.HashMap`.
-/

namespace ProbLang

/-! ## Group A — Closed-ness and parallel substitution

`Exp.isClosed X e` holds iff every free variable of `e` lies in `X`,
where `X : String → Bool` is a predicate. We adapt Clutch's
`is_closed_expr`/`is_closed_val` into a single recursive function on
`Exp` because our values are already carved out of `Exp` via `IsVal`. -/

/-- A "closedness context" — a decidable predicate on free variable names. -/
abbrev ClosedCtx := String → Bool

namespace ClosedCtx

/-- The empty closedness context: no free variables permitted. -/
def empty : ClosedCtx := fun _ => false

/-- Add `x` to a closedness context. -/
def insert (X : ClosedCtx) (x : String) : ClosedCtx :=
  fun y => y == x || X y

/-- Insert a `Binder`: `named`/`typed` adds the name, `anon` is a no-op. -/
def insertB (X : ClosedCtx) : Binder → ClosedCtx
  | .anon       => X
  | .named s    => X.insert s
  | .typed s _  => X.insert s

/-- Pointwise inclusion of closedness contexts. -/
def subset (X Y : ClosedCtx) : Prop := ∀ x, X x = true → Y x = true

/-- Subset is preserved by `insert`. -/
theorem subset.insert {X Y : ClosedCtx} (h : X.subset Y) (x : String) :
    (X.insert x).subset (Y.insert x) := by
  intro z hz
  simp only [ClosedCtx.insert, Bool.or_eq_true, beq_iff_eq] at hz ⊢
  rcases hz with rfl | hz
  · exact .inl rfl
  · exact .inr (h _ hz)

/-- Subset is preserved by `insertB`. -/
theorem subset.insertB {X Y : ClosedCtx} (h : X.subset Y) (b : Binder) :
    (X.insertB b).subset (Y.insertB b) := by
  cases b with
  | anon       => exact h
  | named s    => exact h.insert s
  | typed s _  => exact h.insert s

end ClosedCtx

/-- `Exp.isClosed X e` — every free variable of `e` lies in `X`. -/
def Exp.isClosed (X : ClosedCtx) : Exp → Bool
  | .lit _             => true
  | .var x             => X x
  | .letrec f y e      => e.isClosed ((X.insertB f).insertB y)
  | .app e1 e2         => e1.isClosed X && e2.isClosed X
  | .unop _ e          => e.isClosed X
  | .binop _ e1 e2     => e1.isClosed X && e2.isClosed X
  | .cond e0 e1 e2     => e0.isClosed X && e1.isClosed X && e2.isClosed X
  | .pair e1 e2        => e1.isClosed X && e2.isClosed X
  | .fst e             => e.isClosed X
  | .snd e             => e.isClosed X
  | .inl e             => e.isClosed X
  | .inr e             => e.isClosed X
  | .case e0 e1 e2     => e0.isClosed X && e1.isClosed X && e2.isClosed X
  | .alloc e           => e.isClosed X
  | .load e            => e.isClosed X
  | .store e1 e2       => e1.isClosed X && e2.isClosed X
  | .rand e1 e2        => e1.isClosed X && e2.isClosed X
  | .tape e            => e.isClosed X
  | .fail              => true
  | .annot _ e         => e.isClosed X
  | .scrut e _         => e.isClosed X

/-- If `e` is closed w.r.t. `X` and `X ⊆ Y`, then `e` is closed w.r.t. `Y`. -/
theorem Exp.isClosed_weaken {X Y : ClosedCtx} (hXY : X.subset Y) :
    ∀ {e : Exp}, e.isClosed X = true → e.isClosed Y = true := by
  intro e
  induction e generalizing X Y with
  | lit _ => intro _; rfl
  | var x => intro h; exact hXY _ h
  | letrec f y e ih =>
    intro h
    simp only [isClosed] at h ⊢
    exact ih ((hXY.insertB f).insertB y) h
  | app e1 e2 ih1 ih2
  | binop _ e1 e2 ih1 ih2
  | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2
  | rand e1 e2 ih1 ih2 =>
    intro h
    simp only [isClosed, Bool.and_eq_true] at h ⊢
    exact ⟨ih1 hXY h.1, ih2 hXY h.2⟩
  | cond e0 e1 e2 ih0 ih1 ih2
  | case e0 e1 e2 ih0 ih1 ih2 =>
    intro h
    simp only [isClosed, Bool.and_eq_true] at h ⊢
    exact ⟨⟨ih0 hXY h.1.1, ih1 hXY h.1.2⟩, ih2 hXY h.2⟩
  | unop _ e ih
  | fst e ih
  | snd e ih
  | inl e ih
  | inr e ih
  | alloc e ih
  | load e ih
  | tape e ih
  | annot _ e ih
  | scrut e _ ih =>
    intro h
    simp only [isClosed] at h ⊢
    exact ih hXY h
  | fail => intro _; rfl

/-- If `e` is closed with no free variables, it is closed in any context. -/
theorem Exp.isClosed_weaken_empty {X : ClosedCtx} {e : Exp}
    (h : e.isClosed .empty = true) : e.isClosed X = true :=
  isClosed_weaken (fun _ h => by simp [ClosedCtx.empty] at h) h

/-- `insertB` on a `Binder` reduces to either the identity (for `anon`)
or `insert` on a string. This helper lets subsequent proofs avoid case
analysis on `Binder` for each individual step. -/
@[simp] theorem ClosedCtx.insertB_anon (X : ClosedCtx) :
    X.insertB .anon = X := rfl

@[simp] theorem ClosedCtx.insertB_named (X : ClosedCtx) (s : String) :
    X.insertB (.named s) = X.insert s := rfl

@[simp] theorem ClosedCtx.insertB_typed (X : ClosedCtx) (s : String) (τ : Ty) :
    X.insertB (.typed s τ) = X.insert s := rfl

/-- `insertB b` commutes with `insert x` when `x` isn't bound by `b`.

The `b = anon` case is definitional; the `named s` / `typed s _` cases
both reduce to the pointwise equation
`(z == x) || ((z == s) || X z) = (z == s) || ((z == x) || X z)`,
which is just `Bool.or_left_comm`. -/
theorem ClosedCtx.insertB_insert_comm {X : ClosedCtx} {b : Binder} {x : String}
    (_hb : b.binds x = false) :
    (X.insertB b).insert x = (X.insert x).insertB b := by
  cases b with
  | anon => rfl
  | named s =>
    funext z
    simp only [insertB_named, insert]
    exact Bool.or_left_comm _ _ _
  | typed s _ =>
    funext z
    simp only [insertB_typed, insert]
    exact Bool.or_left_comm _ _ _

/-- `insertB b` absorbs an `insert x` when `x` *is* bound by `b`.

When `b = .named x` or `b = .typed x _`, we need to show
`(z == x) || ((z == x) || X z) = (z == x) || X z`,
which is `Bool.or_self` after regrouping. -/
theorem ClosedCtx.insertB_insert_absorb {X : ClosedCtx} {b : Binder} {x : String}
    (hb : b.binds x = true) :
    (X.insert x).insertB b = X.insertB b := by
  cases b with
  | anon => simp [Binder.binds] at hb
  | named s =>
    simp only [Binder.binds, beq_iff_eq] at hb; subst hb
    funext z
    simp only [insertB_named, insert]
    rw [← Bool.or_assoc, Bool.or_self]
  | typed s _ =>
    simp only [Binder.binds, beq_iff_eq] at hb; subst hb
    funext z
    simp only [insertB_typed, insert]
    rw [← Bool.or_assoc, Bool.or_self]

/-- Substituting a closed replacement into a closed expression yields a
closed expression. Clutch's `is_closed_subst`. -/
theorem Exp.isClosed_subst {e v : Exp} {x : String}
    (hv : v.isClosed .empty = true) :
    ∀ {X : ClosedCtx},
    e.isClosed (X.insert x) = true → (e.subst' x v).isClosed X = true := by
  induction e with
  | lit _ => intro X _; rfl
  | var y =>
    intro X he
    simp only [subst', isClosed] at he ⊢
    by_cases hxy : x = y
    · subst hxy; simp; exact isClosed_weaken_empty hv
    · rw [if_neg hxy]
      simp only [isClosed, ClosedCtx.insert, Bool.or_eq_true, beq_iff_eq] at he ⊢
      rcases he with heq | hY
      · exact absurd heq.symm hxy
      · exact hY
  | letrec f y e ih =>
    intro X he
    simp only [subst', isClosed] at he ⊢
    by_cases hbinds : !f.binds x ∧ !y.binds x
    · rw [if_pos hbinds]
      simp only [isClosed]
      obtain ⟨hf, hy⟩ := hbinds
      simp only [Bool.not_eq_true'] at hf hy
      -- Rewrite `he` so that `.insert x` is innermost, then apply `ih`.
      rw [← ClosedCtx.insertB_insert_comm (b := f) hf,
          ← ClosedCtx.insertB_insert_comm (b := y) hy] at he
      exact ih he
    · rw [if_neg hbinds]
      simp only [isClosed]
      -- `x` is bound by `f` or `y`; the insert collapses. From the negation of
      -- `!f.binds x ∧ !y.binds x`, we get `f.binds x ∨ y.binds x`.
      have hxbinds : f.binds x = true ∨ y.binds x = true := by
        rcases hf : f.binds x with _ | _
        · rcases hy : y.binds x with _ | _
          · exact absurd ⟨by simp [hf], by simp [hy]⟩ hbinds
          · exact .inr rfl
        · exact .inl rfl
      rcases hxbinds with hf | hy
      · rw [ClosedCtx.insertB_insert_absorb hf] at he
        exact he
      · by_cases hf : f.binds x = true
        · rw [ClosedCtx.insertB_insert_absorb hf] at he
          exact he
        · simp only [Bool.not_eq_true] at hf
          rw [← ClosedCtx.insertB_insert_comm (b := f) hf] at he
          rw [ClosedCtx.insertB_insert_absorb hy] at he
          exact he
  | app e1 e2 ih1 ih2
  | binop _ e1 e2 ih1 ih2
  | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2
  | rand e1 e2 ih1 ih2 =>
    intro X he
    simp only [subst', isClosed, Bool.and_eq_true] at he ⊢
    exact ⟨ih1 he.1, ih2 he.2⟩
  | cond e0 e1 e2 ih0 ih1 ih2
  | case e0 e1 e2 ih0 ih1 ih2 =>
    intro X he
    simp only [subst', isClosed, Bool.and_eq_true] at he ⊢
    exact ⟨⟨ih0 he.1.1, ih1 he.1.2⟩, ih2 he.2⟩
  | unop _ e ih
  | fst e ih
  | snd e ih
  | inl e ih
  | inr e ih
  | alloc e ih
  | load e ih
  | tape e ih
  | annot _ e ih
  | scrut e _ ih =>
    intro X he
    simp only [subst', isClosed] at he ⊢
    exact ih he
  | fail => intro X _; rfl

/-- A parallel-substitution environment: variable name → replacement expression. -/
abbrev SubstMap := String → Option Exp

namespace SubstMap

/-- Empty environment. -/
def empty : SubstMap := fun _ => none

/-- Insert a single binding. -/
def insert (vs : SubstMap) (x : String) (v : Exp) : SubstMap :=
  fun y => if y = x then some v else vs y

/-- Remove a binding (used when entering a binder that shadows `x`). -/
def delete (vs : SubstMap) (x : String) : SubstMap :=
  fun y => if y = x then none else vs y

/-- `Binder` variant of `delete`: `named`/`typed` deletes, `anon` is no-op. -/
def deleteB (vs : SubstMap) : Binder → SubstMap
  | .anon       => vs
  | .named s    => vs.delete s
  | .typed s _  => vs.delete s

/-- `Binder` variant of `insert`. -/
def insertB (vs : SubstMap) : Binder → Exp → SubstMap
  | .anon,       _ => vs
  | .named s,    v => vs.insert s v
  | .typed s _,  v => vs.insert s v

end SubstMap

/-- Parallel substitution. Under a binder we delete the bound names from
the environment so that shadowed variables are not replaced. -/
def Exp.substMap (vs : SubstMap) : Exp → Exp
  | .lit l             => .lit l
  | .var y             => (vs y).getD (.var y)
  | .letrec f y e      => .letrec f y (e.substMap ((vs.deleteB f).deleteB y))
  | .app e1 e2         => .app (e1.substMap vs) (e2.substMap vs)
  | .unop op e         => .unop op (e.substMap vs)
  | .binop op e1 e2    => .binop op (e1.substMap vs) (e2.substMap vs)
  | .cond e0 e1 e2     => .cond (e0.substMap vs) (e1.substMap vs) (e2.substMap vs)
  | .pair e1 e2        => .pair (e1.substMap vs) (e2.substMap vs)
  | .fst e             => .fst (e.substMap vs)
  | .snd e             => .snd (e.substMap vs)
  | .inl e             => .inl (e.substMap vs)
  | .inr e             => .inr (e.substMap vs)
  | .case e0 e1 e2     => .case (e0.substMap vs) (e1.substMap vs) (e2.substMap vs)
  | .alloc e           => .alloc (e.substMap vs)
  | .load e            => .load (e.substMap vs)
  | .store e1 e2       => .store (e1.substMap vs) (e2.substMap vs)
  | .rand e1 e2        => .rand (e1.substMap vs) (e2.substMap vs)
  | .tape e            => .tape (e.substMap vs)
  | .fail              => .fail
  | .annot a e         => .annot a (e.substMap vs)
  | .scrut e p         => .scrut (e.substMap vs) p

/-- Substituting the empty environment is a no-op. -/
theorem Exp.substMap_empty (e : Exp) : e.substMap .empty = e := by
  induction e with
  | lit _ => rfl
  | var _ => rfl
  | fail => rfl
  | letrec f y e ih =>
    simp only [substMap]
    have : (SubstMap.empty.deleteB f).deleteB y = SubstMap.empty := by
      funext z
      cases f <;> cases y <;> simp [SubstMap.deleteB, SubstMap.delete, SubstMap.empty]
    rw [this, ih]
  | app e1 e2 ih1 ih2
  | binop _ e1 e2 ih1 ih2
  | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2
  | rand e1 e2 ih1 ih2 =>
    simp only [substMap, ih1, ih2]
  | cond e0 e1 e2 ih0 ih1 ih2
  | case e0 e1 e2 ih0 ih1 ih2 =>
    simp only [substMap, ih0, ih1, ih2]
  | unop _ e ih
  | fst e ih
  | snd e ih
  | inl e ih
  | inr e ih
  | alloc e ih
  | load e ih
  | tape e ih
  | annot _ e ih
  | scrut e _ ih =>
    simp only [substMap, ih]

/-- `Binder`-variant of `isClosed_subst`. -/
theorem Exp.isClosed_subst' {X : ClosedCtx} {e v : Exp} {b : Binder}
    (hv : v.isClosed .empty = true)
    (he : e.isClosed (X.insertB b) = true) :
    (Exp.subst b v e).isClosed X = true := by
  cases b with
  | anon       => exact he
  | named s    => exact isClosed_subst hv he
  | typed s _  => exact isClosed_subst hv he

/-- If `x` isn't bound by `b` and `X x = false`, then `(X.insertB b) x = false`. -/
theorem ClosedCtx.insertB_false {X : ClosedCtx} {b : Binder} {x : String}
    (hb : b.binds x = false) (hx : X x = false) :
    (X.insertB b) x = false := by
  cases b with
  | anon => exact hx
  | named s =>
    simp only [Binder.binds, beq_eq_false_iff_ne, ne_eq] at hb
    simp only [insertB_named, insert, hx, Bool.or_false]
    exact beq_eq_false_iff_ne.mpr (fun h => hb h.symm)
  | typed s _ =>
    simp only [Binder.binds, beq_eq_false_iff_ne, ne_eq] at hb
    simp only [insertB_typed, insert, hx, Bool.or_false]
    exact beq_eq_false_iff_ne.mpr (fun h => hb h.symm)

/-- Substituting for a variable not in the closedness context is a no-op.
Clutch's `subst_is_closed`. -/
theorem Exp.subst_is_closed {e : Exp} {x : String} {es : Exp} :
    ∀ {X : ClosedCtx}, e.isClosed X = true → X x = false → e.subst' x es = e := by
  induction e with
  | lit _ => intros; rfl
  | var y =>
    intro X he hx
    simp only [isClosed] at he
    simp only [subst']
    by_cases hxy : x = y
    · subst hxy; exact absurd he (by rw [hx]; exact Bool.false_ne_true)
    · rw [if_neg hxy]
  | letrec f y e ih =>
    intro X he hx
    simp only [isClosed] at he
    simp only [subst']
    by_cases hbinds : !f.binds x ∧ !y.binds x
    · rw [if_pos hbinds]
      obtain ⟨hf, hy⟩ := hbinds
      simp only [Bool.not_eq_true'] at hf hy
      congr 1
      exact ih he (ClosedCtx.insertB_false hy (ClosedCtx.insertB_false hf hx))
    · rw [if_neg hbinds]
  | app e1 e2 ih1 ih2
  | binop _ e1 e2 ih1 ih2
  | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2
  | rand e1 e2 ih1 ih2 =>
    intro X he hx
    simp only [isClosed, Bool.and_eq_true] at he
    simp only [subst', ih1 he.1 hx, ih2 he.2 hx]
  | cond e0 e1 e2 ih0 ih1 ih2
  | case e0 e1 e2 ih0 ih1 ih2 =>
    intro X he hx
    simp only [isClosed, Bool.and_eq_true] at he
    simp only [subst', ih0 he.1.1 hx, ih1 he.1.2 hx, ih2 he.2 hx]
  | unop _ e ih
  | fst e ih
  | snd e ih
  | inl e ih
  | inr e ih
  | alloc e ih
  | load e ih
  | tape e ih
  | annot _ e ih
  | scrut e _ ih =>
    intro X he hx
    simp only [isClosed] at he
    simp only [subst', ih he hx]
  | fail => intros; rfl

/-- Substituting into a closed expression is a no-op. -/
theorem Exp.subst_is_closed_empty {e : Exp} {x : String} {v : Exp}
    (he : e.isClosed .empty = true) : e.subst' x v = e :=
  subst_is_closed he (by simp [ClosedCtx.empty])

/-- Idempotent substitution with a closed replacement.

Clutch's `subst_subst` works without a closedness hypothesis because their
`subst` is non-recursive on the `Val` constructor, so a `val` replacement
is inert. Our `subst'` recursively descends into the replacement, so we
need `v'` to be closed for the equation to hold. -/
theorem Exp.subst_subst {e v v' : Exp} {x : String}
    (hv' : v'.isClosed .empty = true) :
    (e.subst' x v').subst' x v = e.subst' x v' := by
  induction e with
  | lit _ => rfl
  | var y =>
    simp only [subst']
    by_cases hxy : x = y
    · subst hxy; simp; exact subst_is_closed_empty hv'
    · rw [if_neg hxy]
      simp only [subst', if_neg hxy]
  | letrec f y e ih =>
    simp only [subst']
    by_cases hbinds : !f.binds x ∧ !y.binds x
    · rw [if_pos hbinds]
      simp only [subst', if_pos hbinds, ih]
    · rw [if_neg hbinds]
      simp only [subst', if_neg hbinds]
  | app e1 e2 ih1 ih2
  | binop _ e1 e2 ih1 ih2
  | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2
  | rand e1 e2 ih1 ih2 =>
    simp only [subst', ih1, ih2]
  | cond e0 e1 e2 ih0 ih1 ih2
  | case e0 e1 e2 ih0 ih1 ih2 =>
    simp only [subst', ih0, ih1, ih2]
  | unop _ e ih
  | fst e ih
  | snd e ih
  | inl e ih
  | inr e ih
  | alloc e ih
  | load e ih
  | tape e ih
  | annot _ e ih
  | scrut e _ ih =>
    simp only [subst', ih]
  | fail => rfl

/-- `Binder`-variant of `subst_subst`. -/
theorem Exp.subst_subst_b {e v v' : Exp} {b : Binder}
    (hv' : v'.isClosed .empty = true) :
    Exp.subst b v (Exp.subst b v' e) = Exp.subst b v' e := by
  cases b with
  | anon => rfl
  | named s => exact subst_subst hv'
  | typed s _ => exact subst_subst hv'

/-- `delete` at one name commutes with `deleteB` at a binder (always). -/
theorem SubstMap.delete_deleteB_comm (vs : SubstMap) (x : String) (b : Binder) :
    (vs.delete x).deleteB b = (vs.deleteB b).delete x := by
  funext y
  cases b with
  | anon => rfl
  | named s =>
    simp only [SubstMap.deleteB, SubstMap.delete]
    by_cases hyx : y = x <;> by_cases hys : y = s <;> simp [hyx, hys]
  | typed s _ =>
    simp only [SubstMap.deleteB, SubstMap.delete]
    by_cases hyx : y = x <;> by_cases hys : y = s <;> simp [hyx, hys]

/-- `insert` at a name commutes with `deleteB` at a binder that doesn't bind it. -/
theorem SubstMap.insert_deleteB_comm {vs : SubstMap} {x : String} {v : Exp} {b : Binder}
    (hb : b.binds x = false) :
    (vs.insert x v).deleteB b = (vs.deleteB b).insert x v := by
  funext y
  cases b with
  | anon => rfl
  | named s =>
    simp only [Binder.binds, beq_eq_false_iff_ne, ne_eq] at hb
    simp only [SubstMap.deleteB, SubstMap.delete, SubstMap.insert]
    by_cases hys : y = s
    · subst hys
      have hyx : y ≠ x := hb
      simp [hyx]
    · by_cases hyx : y = x
      · subst hyx
        have hne : y ≠ s := hys
        simp [hne]
      · simp [hys, hyx]
  | typed s _ =>
    simp only [Binder.binds, beq_eq_false_iff_ne, ne_eq] at hb
    simp only [SubstMap.deleteB, SubstMap.delete, SubstMap.insert]
    by_cases hys : y = s
    · subst hys
      have hyx : y ≠ x := hb
      simp [hyx]
    · by_cases hyx : y = x
      · subst hyx
        have hne : y ≠ s := hys
        simp [hne]
      · simp [hys, hyx]

/-- `insert` at a name is absorbed by `deleteB` at a binder that binds it. -/
theorem SubstMap.insert_deleteB_absorb {vs : SubstMap} {x : String} {v : Exp} {b : Binder}
    (hb : b.binds x = true) :
    (vs.insert x v).deleteB b = vs.deleteB b := by
  funext y
  cases b with
  | anon => simp [Binder.binds] at hb
  | named s =>
    simp only [Binder.binds, beq_iff_eq] at hb; subst hb
    simp only [SubstMap.deleteB, SubstMap.delete, SubstMap.insert]
    by_cases hys : y = s
    · subst hys; simp
    · simp [hys]
  | typed s _ =>
    simp only [Binder.binds, beq_iff_eq] at hb; subst hb
    simp only [SubstMap.deleteB, SubstMap.delete, SubstMap.insert]
    by_cases hys : y = s
    · subst hys; simp
    · simp [hys]

/-- `substMap` on an extended environment decomposes into a single
`subst'` followed by a `substMap` on the environment with that variable
deleted. Clutch's `subst_map_insert`.

In Clutch, this needs no hypothesis because `subst` is non-recursive on
the `val` constructor; in our setting we need the range of `vs` to consist
of closed expressions so that `subst'` on them is the identity. -/
theorem Exp.substMap_insert {x : String} {v : Exp} (e : Exp) :
    ∀ {vs : SubstMap},
    (∀ y v', vs y = some v' → v'.isClosed .empty = true) →
    e.substMap (vs.insert x v) = (e.substMap (vs.delete x)).subst' x v := by
  induction e with
  | lit _ => intros; rfl
  | var y =>
    intro vs hvs
    simp only [substMap, SubstMap.insert, SubstMap.delete]
    by_cases hxy : y = x
    · subst hxy
      simp only [if_pos rfl]
      simp [subst']
    · simp only [if_neg hxy]
      cases hvsy : vs y with
      | none =>
        simp only [Option.getD_none]
        have hxy' : x ≠ y := fun h => hxy h.symm
        simp [subst', hxy']
      | some v' =>
        simp only [Option.getD_some]
        exact (subst_is_closed_empty (hvs y v' hvsy)).symm
  | letrec f z e ih =>
    intro vs hvs
    simp only [substMap, subst']
    -- Helper: `deleteB` only shrinks the range of a `SubstMap`, so closedness
    -- of every value in `vs` transfers to any binder-deletion of `vs`.
    have hvs_deleteB : ∀ (vs : SubstMap) (b : Binder),
        (∀ y v', vs y = some v' → v'.isClosed .empty = true) →
        ∀ y v', (vs.deleteB b) y = some v' → v'.isClosed .empty = true := by
      intro vs b hvs y v' h
      cases b with
      | anon => exact hvs y v' h
      | named s =>
        simp only [SubstMap.deleteB, SubstMap.delete] at h
        by_cases hys : y = s
        · subst hys; simp at h
        · simp [hys] at h; exact hvs y v' h
      | typed s _ =>
        simp only [SubstMap.deleteB, SubstMap.delete] at h
        by_cases hys : y = s
        · subst hys; simp at h
        · simp [hys] at h; exact hvs y v' h
    by_cases hbinds : !f.binds x ∧ !z.binds x
    · rw [if_pos hbinds]
      obtain ⟨hf, hz⟩ := hbinds
      simp only [Bool.not_eq_true'] at hf hz
      rw [SubstMap.insert_deleteB_comm hf, SubstMap.insert_deleteB_comm hz]
      have hvs' : ∀ y v', ((vs.deleteB f).deleteB z) y = some v' →
          v'.isClosed .empty = true :=
        hvs_deleteB _ _ (hvs_deleteB _ _ hvs)
      rw [ih hvs']
      congr 2
      rw [SubstMap.delete_deleteB_comm, SubstMap.delete_deleteB_comm]
    · rw [if_neg hbinds]
      -- Negative case: at least one of `f`, `z` binds `x`, so `insert x v`
      -- at position `x` is killed by `deleteB`, and at any other position
      -- `insert x v` and `delete x` are no-ops. Show the two environments
      -- are pointwise equal and pull the `substMap` across.
      congr 1
      have henv :
          ((vs.insert x v).deleteB f).deleteB z
            = ((vs.delete x).deleteB f).deleteB z := by
        -- Reduce to showing `(vs.insert x v).deleteB f (or z) = (vs.delete x).deleteB …`.
        -- Easiest: do a single funext and reason pointwise.
        funext y
        by_cases hyx : y = x
        · rw [hyx]
          -- At position `y = x`: we need both sides to be `none` (or equal).
          -- Since NOT (!f.binds x ∧ !z.binds x), either `f.binds x = true`
          -- or `z.binds x = true`.
          have hxbinds : f.binds x = true ∨ z.binds x = true := by
            rcases hf : f.binds x with _ | _
            · rcases hz : z.binds x with _ | _
              · exact absurd ⟨by simp [hf], by simp [hz]⟩ hbinds
              · exact .inr rfl
            · exact .inl rfl
          rcases hxbinds with hfx | hzx
          · -- `f` binds `x`: then `deleteB f` at position `x` is `none` on both sides.
            have hL : (((vs.insert x v).deleteB f).deleteB z) x = none := by
              have h1 : ((vs.insert x v).deleteB f) x = none := by
                cases f with
                | anon => simp [Binder.binds] at hfx
                | named s =>
                  simp only [Binder.binds, beq_iff_eq] at hfx; subst hfx
                  simp [SubstMap.deleteB, SubstMap.delete, SubstMap.insert]
                | typed s _ =>
                  simp only [Binder.binds, beq_iff_eq] at hfx; subst hfx
                  simp [SubstMap.deleteB, SubstMap.delete, SubstMap.insert]
              cases z with
              | anon => exact h1
              | named s =>
                simp only [SubstMap.deleteB, SubstMap.delete]
                by_cases hxs : x = s
                · subst hxs; simp
                · simp [hxs]; exact h1
              | typed s _ =>
                simp only [SubstMap.deleteB, SubstMap.delete]
                by_cases hxs : x = s
                · subst hxs; simp
                · simp [hxs]; exact h1
            have hR : (((vs.delete x).deleteB f).deleteB z) x = none := by
              have h1 : ((vs.delete x).deleteB f) x = none := by
                cases f with
                | anon =>
                  simp [Binder.binds] at hfx
                | named s =>
                  simp only [Binder.binds, beq_iff_eq] at hfx; subst hfx
                  simp [SubstMap.deleteB, SubstMap.delete]
                | typed s _ =>
                  simp only [Binder.binds, beq_iff_eq] at hfx; subst hfx
                  simp [SubstMap.deleteB, SubstMap.delete]
              cases z with
              | anon => exact h1
              | named s =>
                simp only [SubstMap.deleteB, SubstMap.delete]
                by_cases hxs : x = s
                · subst hxs; simp
                · simp [hxs]; exact h1
              | typed s _ =>
                simp only [SubstMap.deleteB, SubstMap.delete]
                by_cases hxs : x = s
                · subst hxs; simp
                · simp [hxs]; exact h1
            rw [hL, hR]
          · -- `z` binds `x`: outer `deleteB z` at position `x` is `none`.
            have hL : (((vs.insert x v).deleteB f).deleteB z) x = none := by
              cases z with
              | anon => simp [Binder.binds] at hzx
              | named s =>
                simp only [Binder.binds, beq_iff_eq] at hzx; subst hzx
                simp [SubstMap.deleteB, SubstMap.delete]
              | typed s _ =>
                simp only [Binder.binds, beq_iff_eq] at hzx; subst hzx
                simp [SubstMap.deleteB, SubstMap.delete]
            have hR : (((vs.delete x).deleteB f).deleteB z) x = none := by
              cases z with
              | anon => simp [Binder.binds] at hzx
              | named s =>
                simp only [Binder.binds, beq_iff_eq] at hzx; subst hzx
                simp [SubstMap.deleteB, SubstMap.delete]
              | typed s _ =>
                simp only [Binder.binds, beq_iff_eq] at hzx; subst hzx
                simp [SubstMap.deleteB, SubstMap.delete]
            rw [hL, hR]
        · -- At position `y ≠ x`: `insert x v` and `delete x` are no-ops.
          have hins : (vs.insert x v) y = vs y := by
            show (if y = x then some v else vs y) = vs y
            rw [if_neg hyx]
          have hdel : (vs.delete x) y = vs y := by
            show (if y = x then none else vs y) = vs y
            rw [if_neg hyx]
          -- We need to push these equalities through two `deleteB`s.
          -- Strategy: show each `deleteB` preserves pointwise equality at `y`.
          have step : ∀ (m1 m2 : SubstMap), m1 y = m2 y →
              ∀ (b : Binder), (m1.deleteB b) y = (m2.deleteB b) y := by
            intro m1 m2 heq b
            cases b with
            | anon => exact heq
            | named s =>
              simp only [SubstMap.deleteB, SubstMap.delete]
              by_cases hys : y = s
              · subst hys; simp
              · simp [hys]; exact heq
            | typed s _ =>
              simp only [SubstMap.deleteB, SubstMap.delete]
              by_cases hys : y = s
              · subst hys; simp
              · simp [hys]; exact heq
          have h1 : ((vs.insert x v).deleteB f) y = ((vs.delete x).deleteB f) y :=
            step _ _ (by rw [hins, hdel]) f
          exact step _ _ h1 z
      rw [henv]
  | app e1 e2 ih1 ih2
  | binop _ e1 e2 ih1 ih2
  | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2
  | rand e1 e2 ih1 ih2 =>
    intro vs hvs
    simp only [substMap, subst', ih1 hvs, ih2 hvs]
  | cond e0 e1 e2 ih0 ih1 ih2
  | case e0 e1 e2 ih0 ih1 ih2 =>
    intro vs hvs
    simp only [substMap, subst', ih0 hvs, ih1 hvs, ih2 hvs]
  | unop _ e ih
  | fst e ih
  | snd e ih
  | inl e ih
  | inr e ih
  | alloc e ih
  | load e ih
  | tape e ih
  | annot _ e ih
  | scrut e _ ih =>
    intro vs hvs
    simp only [substMap, subst', ih hvs]
  | fail => intros; rfl

/-- Singleton substMap reduces to a single `subst'`. -/
theorem Exp.substMap_singleton (x : String) (v : Exp) (e : Exp) :
    e.substMap (SubstMap.empty.insert x v) = e.subst' x v := by
  have hvs : ∀ y v', SubstMap.empty y = some v' → v'.isClosed .empty = true := by
    intro y v' h; simp [SubstMap.empty] at h
  rw [substMap_insert e hvs]
  have : SubstMap.empty.delete x = SubstMap.empty := by
    funext y; simp [SubstMap.delete, SubstMap.empty]
  rw [this, substMap_empty]

/-- `Binder`-variant of `substMap_insert`. -/
theorem Exp.substMap_insertB {b : Binder} {v : Exp} {vs : SubstMap}
    (hvs : ∀ y v', vs y = some v' → v'.isClosed .empty = true)
    (e : Exp) :
    e.substMap (vs.insertB b v) = Exp.subst b v (e.substMap (vs.deleteB b)) := by
  cases b with
  | anon => rfl
  | named s => exact substMap_insert e hvs
  | typed s _ => exact substMap_insert e hvs

/-- Specialization of `substMap_insertB` to the empty environment. -/
theorem Exp.substMap_insertB_empty (b : Binder) (v : Exp) (e : Exp) :
    e.substMap (SubstMap.empty.insertB b v) = Exp.subst b v e := by
  have hvs : ∀ y v', SubstMap.empty y = some v' → v'.isClosed .empty = true := by
    intro y v' h; simp [SubstMap.empty] at h
  rw [substMap_insertB hvs]
  have hdel : SubstMap.empty.deleteB b = SubstMap.empty := by
    funext y; cases b <;> simp [SubstMap.deleteB, SubstMap.delete, SubstMap.empty]
  rw [hdel, substMap_empty]

/-- Under a binder, if the environment has `none` for every free variable
of the context, then the environment with the binder variables deleted
also has `none` for every free variable of the extended context. -/
theorem SubstMap.deleteB_preserves_closed {X : ClosedCtx} {vs : SubstMap} {b : Binder}
    (hvs : ∀ x, X x = true → vs x = none) :
    ∀ x, (X.insertB b) x = true → (vs.deleteB b) x = none := by
  intro x hx
  cases b with
  | anon => exact hvs x hx
  | named s =>
    simp only [SubstMap.deleteB, SubstMap.delete]
    by_cases hxs : x = s
    · rw [if_pos hxs]
    · rw [if_neg hxs]
      apply hvs
      simp only [ClosedCtx.insertB_named, ClosedCtx.insert, Bool.or_eq_true, beq_iff_eq] at hx
      rcases hx with heq | h
      · exact absurd heq hxs
      · exact h
  | typed s _ =>
    simp only [SubstMap.deleteB, SubstMap.delete]
    by_cases hxs : x = s
    · rw [if_pos hxs]
    · rw [if_neg hxs]
      apply hvs
      simp only [ClosedCtx.insertB_typed, ClosedCtx.insert, Bool.or_eq_true, beq_iff_eq] at hx
      rcases hx with heq | h
      · exact absurd heq hxs
      · exact h

/-- `substMap` through a closed expression is a no-op. -/
theorem Exp.substMap_isClosed {e : Exp} :
    ∀ {X : ClosedCtx} {vs : SubstMap},
    e.isClosed X = true →
    (∀ x, X x = true → vs x = none) →
    e.substMap vs = e := by
  induction e with
  | lit _ => intros; rfl
  | var y =>
    intro X vs he hvs
    simp only [isClosed] at he
    simp only [substMap]
    rw [hvs y he]
    rfl
  | letrec f z e ih =>
    intro X vs he hvs
    simp only [isClosed] at he
    simp only [substMap]
    congr 1
    exact ih he (SubstMap.deleteB_preserves_closed
      (SubstMap.deleteB_preserves_closed hvs))
  | app e1 e2 ih1 ih2
  | binop _ e1 e2 ih1 ih2
  | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2
  | rand e1 e2 ih1 ih2 =>
    intro X vs he hvs
    simp only [isClosed, Bool.and_eq_true] at he
    simp only [substMap, ih1 he.1 hvs, ih2 he.2 hvs]
  | cond e0 e1 e2 ih0 ih1 ih2
  | case e0 e1 e2 ih0 ih1 ih2 =>
    intro X vs he hvs
    simp only [isClosed, Bool.and_eq_true] at he
    simp only [substMap, ih0 he.1.1 hvs, ih1 he.1.2 hvs, ih2 he.2 hvs]
  | unop _ e ih
  | fst e ih
  | snd e ih
  | inl e ih
  | inr e ih
  | alloc e ih
  | load e ih
  | tape e ih
  | annot _ e ih
  | scrut e _ ih =>
    intro X vs he hvs
    simp only [isClosed] at he
    simp only [substMap, ih he hvs]
  | fail => intros; rfl

/-- Specialization of `substMap_isClosed` to the fully closed case. -/
theorem Exp.substMap_isClosed_empty {e : Exp} {vs : SubstMap}
    (he : e.isClosed .empty = true) : e.substMap vs = e := by
  exact substMap_isClosed he (fun _ h => by simp [ClosedCtx.empty] at h)

/-- Commutativity of substitution at different names, with closed replacements.
Clutch's `subst_subst_ne` (closed-replacements variant). -/
theorem Exp.subst_subst_ne {e v v' : Exp} {x y : String}
    (hne : x ≠ y)
    (hv : v.isClosed .empty = true)
    (hv' : v'.isClosed .empty = true) :
    (e.subst' y v').subst' x v = (e.subst' x v).subst' y v' := by
  induction e with
  | lit _ => rfl
  | var z =>
    by_cases hyz : y = z
    · subst hyz
      -- Here `z = y`. LHS: `(var y).subst' y v'` = `v'`, then `.subst' x v = v'` (v' closed).
      -- RHS: `(var y).subst' x v` = `var y` (x ≠ y), then `.subst' y v' = v'`.
      have hLHS : ((Exp.var y).subst' y v').subst' x v = v' := by
        rw [show (Exp.var y).subst' y v' = v' from by simp [subst']]
        exact subst_is_closed_empty hv'
      have hRHS : ((Exp.var y).subst' x v).subst' y v' = v' := by
        rw [show (Exp.var y).subst' x v = Exp.var y from by simp [subst', hne]]
        simp [subst']
      rw [hLHS, hRHS]
    · by_cases hxz : x = z
      · subst hxz
        have hyx : y ≠ x := hyz
        have hLHS : ((Exp.var x).subst' y v').subst' x v = v := by
          rw [show (Exp.var x).subst' y v' = Exp.var x from by simp [subst', hyx]]
          simp [subst']
        have hRHS : ((Exp.var x).subst' x v).subst' y v' = v := by
          rw [show (Exp.var x).subst' x v = v from by simp [subst']]
          exact subst_is_closed_empty hv
        rw [hLHS, hRHS]
      · have hLHS : ((Exp.var z).subst' y v').subst' x v = Exp.var z := by
          rw [show (Exp.var z).subst' y v' = Exp.var z from by simp [subst', hyz]]
          simp [subst', hxz]
        have hRHS : ((Exp.var z).subst' x v).subst' y v' = Exp.var z := by
          rw [show (Exp.var z).subst' x v = Exp.var z from by simp [subst', hxz]]
          simp [subst', hyz]
        rw [hLHS, hRHS]
  | letrec f z e ih =>
    simp only [subst']
    by_cases hby : !f.binds y ∧ !z.binds y
    · rw [if_pos hby]
      by_cases hbx : !f.binds x ∧ !z.binds x
      · rw [if_pos hbx]
        simp only [subst', if_pos hby, if_pos hbx, ih]
      · rw [if_neg hbx]
        simp only [subst']; rw [if_neg hbx, if_pos hby]
    · rw [if_neg hby]
      by_cases hbx : !f.binds x ∧ !z.binds x
      · rw [if_pos hbx]
        simp only [subst']; rw [if_neg hby, if_pos hbx]
      · rw [if_neg hbx]
        simp only [subst']; rw [if_neg hby, if_neg hbx]
  | app e1 e2 ih1 ih2
  | binop _ e1 e2 ih1 ih2
  | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2
  | rand e1 e2 ih1 ih2 =>
    simp only [subst', ih1, ih2]
  | cond e0 e1 e2 ih0 ih1 ih2
  | case e0 e1 e2 ih0 ih1 ih2 =>
    simp only [subst', ih0, ih1, ih2]
  | unop _ e ih
  | fst e ih
  | snd e ih
  | inl e ih
  | inr e ih
  | alloc e ih
  | load e ih
  | tape e ih
  | annot _ e ih
  | scrut e _ ih =>
    simp only [subst', ih]
  | fail => rfl

/-! ## Group D — Deterministic / probabilistic head-step characterization

Port of the predicate-based step classification from Clutch's
`metatheory.v` (roughly lines 1448–1713 of the upstream file, minus the
Laplace/Tick cases). We **reuse** our existing `HeadStepSupport` (from
`HeadStep.lean`) as the "step relation" — Clutch's `det_head_step_rel`
is subsumed — and introduce predicate-only versions for det/prob
classification.

**Omissions relative to Clutch:**
* `RecDS`/`PairDS`/`InjLDS`/`InjRDS` value-reduction cases (our values
  are already inert).
* All Laplace/Tick cases.
-/

/-- Expressions that take a single *deterministic* head step in state `σ`.
Mirrors the deterministic subset of `HeadStepSupport` constructors. -/
inductive DetHeadStepPred : Exp → State → Prop
  | beta {f x e1 e2 σ} : e2.isValue →
      DetHeadStepPred (.app (.letrec f x e1) e2) σ
  | unop {op e σ e'} : e.isValue → op.eval e = some e' →
      DetHeadStepPred (.unop op e) σ
  | binop {op e1 e2 σ e'} : e1.isValue → e2.isValue → op.eval e1 e2 = some e' →
      DetHeadStepPred (.binop op e1 e2) σ
  | ifTrue {et ef σ} : DetHeadStepPred (.cond (.lit (.bool true)) et ef) σ
  | ifFalse {et ef σ} : DetHeadStepPred (.cond (.lit (.bool false)) et ef) σ
  | fst {e1 e2 σ} : e1.isValue → e2.isValue →
      DetHeadStepPred (.fst (.pair e1 e2)) σ
  | snd {e1 e2 σ} : e1.isValue → e2.isValue →
      DetHeadStepPred (.snd (.pair e1 e2)) σ
  | caseL {e el er σ} : e.isValue →
      DetHeadStepPred (.case (.inl e) el er) σ
  | caseR {e el er σ} : e.isValue →
      DetHeadStepPred (.case (.inr e) el er) σ
  | alloc {ed σ} : ed.isValue → DetHeadStepPred (.alloc ed) σ
  | load {ℓ v σ} : σ.heap[ℓ]? = some v →
      DetHeadStepPred (.load (.lit (.loc ℓ))) σ
  | store {ℓ e σ} : e.isValue → σ.heap[ℓ]?.isSome →
      DetHeadStepPred (.store (.lit (.loc ℓ)) e) σ
  | tape {z σ} : DetHeadStepPred (.tape (.lit (.int z))) σ
  | scrutSuccess {e p σ bindings} : e.isValue → Pat.tryMatch p e = some bindings →
      DetHeadStepPred (.scrut e p) σ
  | scrutFailure {e p σ} : e.isValue → Pat.tryMatch p e = none →
      DetHeadStepPred (.scrut e p) σ
  | annot {a e σ} : e.isValue → DetHeadStepPred (.annot a e) σ

/-- Expressions that take a *probabilistic* head step in state `σ`. Only
the four `rand` cases (no Laplace in our port). -/
inductive ProbHeadStepPred : Exp → State → Prop
  | randNoTape {z σ} : 0 < z →
      ProbHeadStepPred (.rand (.lit (.int z)) (.lit .unit)) σ
  | randTape {z α σ N nn ns} : 0 < z → σ.tapes[α]? = some ⟨N, nn :: ns⟩ → z = N →
      ProbHeadStepPred (.rand (.lit (.int z)) (.lit (.lbl α))) σ
  | randTapeEmpty {z α σ N} : 0 < z → σ.tapes[α]? = some ⟨N, []⟩ → z = N →
      ProbHeadStepPred (.rand (.lit (.int z)) (.lit (.lbl α))) σ
  | randTapeOther {z α σ N L} : 0 < z → σ.tapes[α]? = some ⟨N, L⟩ → z ≠ N →
      ProbHeadStepPred (.rand (.lit (.int z)) (.lit (.lbl α))) σ

/-- Either a deterministic or a probabilistic head step is taken. -/
def HeadStepPred (e : Exp) (σ : State) : Prop :=
  DetHeadStepPred e σ ∨ ProbHeadStepPred e σ

/-- Boolean test for determinism of a head step. Clutch's `is_det_head_step`.
Uses `decide` on the `Decidable` `Exp.isValue` instance. -/
def isDetHeadStep (e : Exp) (σ : State) : Bool :=
  match e with
  | .app (.letrec _ _ _) e2 => decide e2.isValue
  | .unop op e =>
      decide e.isValue && (op.eval e).isSome
  | .binop op e1 e2 =>
      decide e1.isValue && decide e2.isValue && (op.eval e1 e2).isSome
  | .cond (.lit (.bool _)) _ _ => true
  | .fst (.pair e1 e2) => decide e1.isValue && decide e2.isValue
  | .snd (.pair e1 e2) => decide e1.isValue && decide e2.isValue
  | .case (.inl e) _ _ => decide e.isValue
  | .case (.inr e) _ _ => decide e.isValue
  | .alloc ed => decide ed.isValue
  | .load (.lit (.loc ℓ)) => σ.heap[ℓ]?.isSome
  | .store (.lit (.loc ℓ)) e => decide e.isValue && σ.heap[ℓ]?.isSome
  | .tape (.lit (.int _)) => true
  | .scrut e _ => decide e.isValue
  | .annot _ e => decide e.isValue
  | _ => false

/-- Values don't take head steps. Clutch's `val_not_head_step`. -/
theorem val_not_HeadStepPred {e : Exp} {σ : State}
    (hv : e.isValue) : ¬ HeadStepPred e σ := by
  rw [Exp.isValue_iff_isValueR] at hv
  rintro (hdet | hprob)
  · -- No det constructor applies to values.
    cases hdet <;> simp [Exp.isValueR] at hv
  · -- No prob constructor applies to values.
    cases hprob <;> simp [Exp.isValueR] at hv

/-- `isDetHeadStep ↔ DetHeadStepPred`. Clutch's `is_det_head_step_true`. -/
theorem isDetHeadStep_iff_pred (e : Exp) (σ : State) :
    isDetHeadStep e σ = true ↔ DetHeadStepPred e σ := by
  constructor
  · intro h
    unfold isDetHeadStep at h
    split at h
    · rename_i e2 f x e1
      exact .beta (by simpa using h)
    · rename_i op e'
      rw [Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at h
      obtain ⟨hv, e'', heval⟩ := h
      exact .unop hv heval
    · rename_i op e1 e2
      rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          decide_eq_true_eq, Option.isSome_iff_exists] at h
      obtain ⟨⟨hv1, hv2⟩, e', heval⟩ := h
      exact .binop hv1 hv2 heval
    · rename_i b et ef
      cases b with
      | true => exact .ifTrue
      | false => exact .ifFalse
    · rename_i e1 e2
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
      exact .fst h.1 h.2
    · rename_i e1 e2
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
      exact .snd h.1 h.2
    · rename_i e el er
      rw [decide_eq_true_eq] at h
      exact .caseL h
    · rename_i e el er
      rw [decide_eq_true_eq] at h
      exact .caseR h
    · rename_i ed
      rw [decide_eq_true_eq] at h
      exact .alloc h
    · rename_i ℓ
      rw [Option.isSome_iff_exists] at h
      obtain ⟨v, hv⟩ := h
      exact .load hv
    · rename_i ℓ e
      rw [Bool.and_eq_true, decide_eq_true_eq] at h
      exact .store h.1 h.2
    · rename_i z
      exact .tape
    · rename_i e p
      rw [decide_eq_true_eq] at h
      -- Need to split on whether tryMatch succeeds.
      cases hm : Pat.tryMatch p e with
      | some bindings => exact .scrutSuccess h hm
      | none => exact .scrutFailure h hm
    · rename_i a e
      rw [decide_eq_true_eq] at h
      exact .annot h
    · simp at h
  · intro hpred
    cases hpred with
    | beta hv => simp [isDetHeadStep, hv]
    | unop hv heval => simp [isDetHeadStep, hv, heval]
    | binop hv1 hv2 heval => simp [isDetHeadStep, hv1, hv2, heval]
    | ifTrue => simp [isDetHeadStep]
    | ifFalse => simp [isDetHeadStep]
    | fst hv1 hv2 => simp [isDetHeadStep, hv1, hv2]
    | snd hv1 hv2 => simp [isDetHeadStep, hv1, hv2]
    | caseL hv => simp [isDetHeadStep, hv]
    | caseR hv => simp [isDetHeadStep, hv]
    | alloc hv => simp [isDetHeadStep, hv]
    | load hlook => simp [isDetHeadStep, hlook]
    | store hv hsome => simp [isDetHeadStep, hv, hsome]
    | tape => simp [isDetHeadStep]
    | scrutSuccess hv _ => simp [isDetHeadStep, hv]
    | scrutFailure hv _ => simp [isDetHeadStep, hv]
    | annot hv => simp [isDetHeadStep, hv]

/-- `HeadStepPred ↔ a successor exists in `HeadStepSupport`.
Clutch's `head_step_pred_ex_rel`. -/
theorem HeadStepPred_iff_exists_support (e : Exp) (σ : State) :
    HeadStepPred e σ ↔ ∃ ρ', HeadStepSupport ⟨e, σ⟩ ρ' := by
  constructor
  · rintro (hdet | hprob)
    · cases hdet with
      | beta hv => exact ⟨_, .BetaS hv rfl⟩
      | unop hv heval => exact ⟨_, .UnOpS hv heval.symm⟩
      | binop hv1 hv2 heval => exact ⟨_, .BinOpS hv1 hv2 heval.symm⟩
      | ifTrue => exact ⟨_, .IfTrueS⟩
      | ifFalse => exact ⟨_, .IfFalseS⟩
      | fst hv1 hv2 => exact ⟨_, .FstS hv1 hv2⟩
      | snd hv1 hv2 => exact ⟨_, .SndS hv1 hv2⟩
      | caseL hv => exact ⟨_, .CaseLS hv⟩
      | caseR hv => exact ⟨_, .CaseRS hv⟩
      | @alloc ed σ hv =>
          have : ed.toVal?.isSome := by
            rw [Option.isSome_iff_ne_none]; intro h
            exact (Exp.toVal?_eq_none.mp h) hv
          obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp this
          exact ⟨_, .AllocS hv' rfl rfl⟩
      | load hlook => exact ⟨_, .LoadS hlook rfl⟩
      | @store ℓ e σ hv hsome =>
          have : e.toVal?.isSome := by
            rw [Option.isSome_iff_ne_none]; intro h
            exact (Exp.toVal?_eq_none.mp h) hv
          obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp this
          exact ⟨_, .StoreS hv' hsome rfl⟩
      | tape => exact ⟨_, .TapeS rfl rfl⟩
      | scrutSuccess hv hm => exact ⟨_, .ScrutSuccessS hv hm⟩
      | scrutFailure hv hm => exact ⟨_, .ScrutFailureS hv hm⟩
      | annot hv => exact ⟨_, .AnnotS hv⟩
    · cases hprob with
      | randNoTape hz => exact ⟨_, .RandNoTapeS hz (le_refl 0) hz⟩
      | randTape hz htape hzN =>
          exact ⟨_, .RandTapeS hz htape hzN rfl rfl⟩
      | randTapeEmpty hz htape hzN =>
          exact ⟨_, .RandTapeEmptyS hz htape hzN (le_refl 0) hz rfl⟩
      | randTapeOther hz htape hzN =>
          exact ⟨_, .RandTapeOtherS hz htape hzN (le_refl 0) hz rfl⟩
  · rintro ⟨ρ', hsupp⟩
    cases hsupp with
    | BetaS hv _ => exact .inl (.beta hv)
    | UnOpS hv heval => exact .inl (.unop hv heval.symm)
    | BinOpS hv1 hv2 heval => exact .inl (.binop hv1 hv2 heval.symm)
    | IfTrueS => exact .inl .ifTrue
    | IfFalseS => exact .inl .ifFalse
    | FstS hv1 hv2 => exact .inl (.fst hv1 hv2)
    | SndS hv1 hv2 => exact .inl (.snd hv1 hv2)
    | CaseLS hv => exact .inl (.caseL hv)
    | CaseRS hv => exact .inl (.caseR hv)
    | AllocS htoval _ _ =>
        exact .inl (.alloc (Exp.toVal?_isValue htoval))
    | LoadS hlook _ => exact .inl (.load hlook)
    | StoreS htoval hsome _ =>
        exact .inl (.store (Exp.toVal?_isValue htoval) hsome)
    | TapeS _ _ => exact .inl .tape
    | ScrutSuccessS hv hm => exact .inl (.scrutSuccess hv hm)
    | ScrutFailureS hv hm => exact .inl (.scrutFailure hv hm)
    | AnnotS hv => exact .inl (.annot hv)
    | RandNoTapeS hz _ _ => exact .inr (.randNoTape hz)
    | RandTapeS hz htape hzN _ _ => exact .inr (.randTape hz htape hzN)
    | RandTapeEmptyS hz htape hzN _ _ _ => exact .inr (.randTapeEmpty hz htape hzN)
    | RandTapeOtherS hz htape hzN _ _ _ => exact .inr (.randTapeOther hz htape hzN)

/-- `¬ HeadStepPred e σ ↔ headStep ⟨e, σ⟩ = 0`. Clutch's `not_head_step_pred_dzero`.
Follows from `HeadStepPred_iff_exists_support` + the support-zero equivalence
for `headStep`. -/
theorem not_HeadStepPred_iff_zero (e : Exp) (σ : State) :
    ¬ HeadStepPred e σ ↔ headStep ⟨e, σ⟩ = 0 := by
  rw [HeadStepPred_iff_exists_support]
  constructor
  · intro hne
    -- No configuration has positive support, so headStep is zero.
    have hzero : ∀ ρ', (headStep ⟨e, σ⟩) {ρ'} = 0 := by
      intro ρ'
      by_contra hpos
      apply hne
      refine ⟨ρ', ?_⟩
      obtain ⟨e2, σ2⟩ := ρ'
      exact (headStep_support_iff e e2 σ σ2).mp
        (lt_of_le_of_ne bot_le (Ne.symm hpos))
    have hunivzero : (headStep ⟨e, σ⟩) Set.univ = 0 := by
      rw [show (Set.univ : Set Cfg) = ⋃ c : Cfg, ({c} : Set Cfg) from by ext; simp]
      rw [MeasureTheory.measure_iUnion
          (fun i j hij => by simp only [Set.disjoint_singleton]; exact hij)
          (fun _ => .of_discrete)]
      simp [hzero]
    exact (MeasureTheory.Measure.measure_univ_eq_zero).mp hunivzero
  · rintro h0 ⟨ρ', hsupp⟩
    obtain ⟨e2, σ2⟩ := ρ'
    have : 0 < headStep ⟨e, σ⟩ {⟨e2, σ2⟩} :=
      (headStep_support_iff e e2 σ σ2).mpr hsupp
    rw [h0] at this
    simp at this

/-- Every `(e, σ)` is either a det step, a prob step, or stuck (`headStep = 0`).
Clutch's `det_or_prob_or_dzero`. -/
theorem det_or_prob_or_zero (e : Exp) (σ : State) :
    DetHeadStepPred e σ ∨ ProbHeadStepPred e σ ∨ headStep ⟨e, σ⟩ = 0 := by
  by_cases hpred : HeadStepPred e σ
  · rcases hpred with hdet | hprob
    · exact .inl hdet
    · exact .inr (.inl hprob)
  · exact .inr (.inr ((not_HeadStepPred_iff_zero e σ).mp hpred))

/-! ## Group E — Tape and fresh-location update lemmas

Port of the tape / fresh-location update fragment of Clutch's
`metatheory.v` (roughly lines 1714–1881 of the upstream file, minus
the Laplace / Tick cases). These lemmas describe how `State` updates
(via `update_tapes`) interact with each other and with `headStep` /
`primStep`.

We adapt the statements to our `ExtTreeMap Loc Tape` representation.
`σ.tapes[α]?` plays the role of Clutch's `σ.(tapes) !! α`. -/

/-- Clutch's `upd_tape_some`: after inserting `t` at `α`, reading the
tape at `α` yields `t`. We state it at the whole-tape level — Clutch's
"append one sample" version is a specialization. -/
theorem State.upd_tape_some (σ : State) (α : Loc) (t : Tape) :
    (σ.update_tapes (·.insert α t)).tapes[α]? = some t := by
  simp [State.update_tapes]

/-- Two tape updates at different locations commute. Clutch's
`upd_diff_tape_comm`. Proof deferred: requires low-level `ExtTreeMap`
reasoning about `insert` commutativity at distinct keys. -/
theorem State.upd_diff_tape_comm {σ : State} {α β : Loc} {bs bs' : Tape}
    (hne : α ≠ β) :
    ((σ.update_tapes (·.insert β bs)).update_tapes (·.insert α bs'))
      = ((σ.update_tapes (·.insert α bs')).update_tapes (·.insert β bs)) := by
  unfold State.update_tapes
  congr 1
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  simp [Std.ExtTreeMap.getElem?_insert]
  by_cases hαk : α = k
  · subst hαk
    have : ¬ (β = α) := fun h => hne h.symm
    simp [this]
  · by_cases hβk : β = k
    · subst hβk
      simp [hαk]
    · simp [hαk, hβk]

/-- Reading tape `α` after an update at a *different* tape location `β`
is the identity: the tape at `α` is unaffected. Clutch's
`upd_diff_tape_tot`. -/
theorem State.upd_diff_tape_tot {σ : State} {α β : Loc} {bs : Tape}
    (hne : α ≠ β) :
    (σ.update_tapes (·.insert β bs)).tapes[α]? = σ.tapes[α]? := by
  simp [State.update_tapes, Std.ExtTreeMap.getElem?_insert, Ne.symm hne]

/-- `fresh` is unaffected by re-inserting at an already-present key.
Stated in the general `ExtTreeMap Int V` form. -/
theorem Std.ExtTreeMap.fresh_insert_of_mem
    {V : Type*} (t : Std.ExtTreeMap Int V compare) {α : Int} {v w : V}
    (h : t[α]? = some v) :
    (t.insert α w).fresh = t.fresh := by
  unfold Std.ExtTreeMap.fresh
  have hkeys : (t.insert α w).maxKey? = t.maxKey? := by
    rw [Std.ExtTreeMap.maxKey?_insert]
    have hmem : α ∈ t := Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [h]; rfl)
    have hsome : t.maxKey?.isSome := Std.ExtTreeMap.isSome_maxKey?_of_mem hmem
    obtain ⟨km, hkm⟩ : ∃ km, t.maxKey? = some km := ⟨_, Option.eq_some_of_isSome hsome⟩
    rw [hkm]
    simp only [Option.elim, Option.some.injEq]
    have hle_αkm : (compare α km).isLE := by
      have hget : t.maxKey?.get (Std.ExtTreeMap.isSome_maxKey?_of_mem hmem) = km :=
        Option.get_of_eq_some _ hkm
      exact Std.ExtTreeMap.le_maxKey?_of_mem hmem hget
    -- From α ≤ km (via compare α km ≠ .gt), deduce the if-then-else result is km
    have hα_le_km : α ≤ km := by
      simp [compare, compareOfLessAndEq] at hle_αkm
      split at hle_αkm
      · omega
      · split at hle_αkm
        · omega
        · simp [Ordering.isLE] at hle_αkm
    by_cases heq : α = km
    · have hcmp : compare km α = .eq := by
        simp [compare, compareOfLessAndEq, heq.symm]
      simp [hcmp, Ordering.isLE, heq.symm]
    · have hlt : α < km := lt_of_le_of_ne hα_le_km heq
      have hcmp : compare km α = .gt := by
        show compareOfLessAndEq km α = .gt
        unfold compareOfLessAndEq
        have h1 : ¬ (km < α) := by omega
        have h2 : km ≠ α := by omega
        simp [h1, h2]
      simp [hcmp, Ordering.isLE]
  rw [hkeys]

/-- Clutch's `fresh_loc_upd_some`: inserting at an already-present tape
location leaves the fresh location unchanged. -/
theorem State.fresh_loc_upd_some {σ : State} {α : Loc} {bs bs' : Tape}
    (h : σ.tapes[α]? = some bs) :
    (σ.tapes.insert α bs').fresh = σ.tapes.fresh :=
  Std.ExtTreeMap.fresh_insert_of_mem σ.tapes h

/-- Clutch's `elem_fresh_ne`: an existing key is distinct from the
fresh key. Direct corollary of `fresh_get?`. -/
theorem Std.ExtTreeMap.elem_fresh_ne
    {V : Type*} {t : Std.ExtTreeMap Int V compare} {k : Int} {v : V}
    (h : t[k]? = some v) : t.fresh ≠ k := by
  intro heq
  have hfresh := Std.ExtTreeMap.fresh_get? t
  rw [heq] at hfresh
  rw [hfresh] at h
  simp at h

/-- Clutch's `fresh_loc_upd_swap`: we can swap a fresh-allocation
insert past an existing-key insert. Proof deferred; same kind of
`ExtTreeMap` `insert`-commutativity bookkeeping as `upd_diff_tape_comm`. -/
theorem State.fresh_loc_upd_swap {σ : State} {α : Loc} {bs bs' : Tape} {t : Tape}
    (h : σ.tapes[α]? = some bs) :
    ((σ.tapes.insert α bs').insert (σ.tapes.insert α bs').fresh t)
      = ((σ.tapes.insert σ.tapes.fresh t).insert α bs') := by
  rw [State.fresh_loc_upd_some h]
  have hne : σ.tapes.fresh ≠ α := Std.ExtTreeMap.elem_fresh_ne h
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  simp [Std.ExtTreeMap.getElem?_insert]
  by_cases hαk : α = k
  · subst hαk
    have : ¬ (σ.tapes.fresh = α) := hne
    simp [this]
  · by_cases hfk : σ.tapes.fresh = k
    · subst hfk
      simp [hαk]
    · simp [hαk, hfk]

/-- Clutch's `fresh_loc_lookup`: looking up an existing key survives a
fresh-key insertion. Proof deferred; requires `ExtTreeMap` `insert`
look-through at distinct keys. -/
theorem State.fresh_loc_lookup {σ : State} {α : Loc} {bs : Tape} {t : Tape}
    (h : σ.tapes[α]? = some bs) :
    (σ.tapes.insert σ.tapes.fresh t)[α]? = some bs := by
  have hne : σ.tapes.fresh ≠ α := Std.ExtTreeMap.elem_fresh_ne h
  rw [Std.ExtTreeMap.getElem?_insert]
  have hcmp : compare σ.tapes.fresh α ≠ .eq := by
    simp [compare, compareOfLessAndEq]
    split <;> simp_all
  simp [hcmp, h]

/-- Helper: `Cfg.uniform z σ` is the zero measure iff `z` is non-positive.
The dependence on `σ` is only via the post-state in the support, so
zero-ness is uniform in `σ`. -/
theorem Cfg.uniform_eq_zero_iff {z : Int} {σ : State} :
    Cfg.uniform z σ = 0 ↔ ¬ 0 < z := by
  constructor
  · intro h hz
    have heq : Cfg.uniform z σ =
        (PMF.uniformOfFinset (Finset.Ico 0 z)
            (Finset.nonempty_Ico.mpr hz)).toMeasure.map
            (fun x => (⟨.lit (.int x), σ⟩ : Cfg)) := by
      unfold Cfg.uniform Int.isPos Option.unwrapM
      rw [dif_pos hz]
    have hprob : MeasureTheory.IsProbabilityMeasure
        ((PMF.uniformOfFinset (Finset.Ico 0 z)
            (Finset.nonempty_Ico.mpr hz)).toMeasure.map
            (fun x => (⟨.lit (.int x), σ⟩ : Cfg))) :=
      MeasureTheory.Measure.isProbabilityMeasure_map .of_discrete
    have h1 := hprob.measure_univ
    rw [← heq, h] at h1
    simp at h1
  · intro hnz
    unfold Cfg.uniform Int.isPos Option.unwrapM
    rw [dif_neg hnz]

/-- At `z = 1`, `Cfg.uniform 1 σ` is the dirac at `⟨.lit (.int 0), σ⟩`.
This is because `Finset.Ico 0 1 = {0}` is a singleton, so the uniform
PMF is a dirac PMF, and mapping through the state fiber preserves this. -/
theorem Cfg.uniform_one_eq_dirac (σ : State) :
    Cfg.uniform 1 σ = MeasureTheory.Measure.dirac (⟨.lit (.int 0), σ⟩ : Cfg) := by
  classical
  unfold Cfg.uniform Int.isPos Option.unwrapM
  simp only [show (0 : Int) < 1 from Int.one_pos, dite_true]
  -- The uniform PMF on `Ico 0 1 = {0}` is the dirac at 0.
  have hico : Finset.Ico (0 : Int) 1 = {0} := by
    ext x; simp [Finset.mem_Ico]; omega
  refine MeasureTheory.Measure.ext fun S hS => ?_
  rw [MeasureTheory.Measure.map_apply Measurable.of_discrete hS]
  rw [PMF.toMeasure_uniformOfFinset_apply _ _ (MeasurableSet.of_discrete)]
  rw [hico]
  simp only [Finset.card_singleton, Nat.cast_one]
  by_cases hmem : (⟨.lit (.int 0), σ⟩ : Cfg) ∈ S
  · rw [MeasureTheory.Measure.dirac_apply_of_mem hmem]
    have hfilt : ({x ∈ ({0} : Finset Int) |
        x ∈ (fun x : Int => (⟨.lit (.int x), σ⟩ : Cfg)) ⁻¹' S}).card = 1 := by
      simp [Finset.filter_singleton, hmem]
    rw [hfilt]; simp
  · rw [show (MeasureTheory.Measure.dirac (⟨.lit (.int 0), σ⟩ : Cfg)) S = 0 from by
          rw [MeasureTheory.Measure.dirac_apply' _ hS]
          simp [hmem]]
    have hfilt : ({x ∈ ({0} : Finset Int) |
        x ∈ (fun x : Int => (⟨.lit (.int x), σ⟩ : Cfg)) ⁻¹' S}).card = 0 := by
      simp [Finset.filter_singleton, hmem]
    rw [hfilt]; simp

/-- `Cfg.uniform z σ` is never a Dirac when `1 < z`: for any singleton
`{ρ}` the mass is strictly less than `1`. The argument is that when
`1 < z` the uniform measure over `Finset.Ico 0 z` has `≥ 2` distinct
elements (`0` and `1`), so at least two different singletons carry
positive mass — forcing the mass of any single singleton below `1`.

Note: for `z = 1` this lemma is **false** — `Cfg.uniform 1 σ` is a
dirac at `⟨.lit (.int 0), σ⟩`. Callers that need to rule out rand at
`z = 1` must handle that case separately. -/
theorem Cfg.uniform_singleton_ne_one {z : Int} {σ : State} {ρ : Cfg}
    (Hz : 1 < z) : Cfg.uniform z σ {ρ} ≠ 1 := by
  intro h1
  have Hz0 : 0 < z := by omega
  -- The uniform measure is a probability measure.
  have hprob : MeasureTheory.IsProbabilityMeasure (Cfg.uniform z σ) :=
    Cfg.uniform_isProbabilityMeasure Hz0
  -- Both `v = 0` and `v = 1` are in `Ico 0 z` and carry positive mass.
  have hpos0 : 0 < Cfg.uniform z σ {⟨.lit (.int 0), σ⟩} :=
    Cfg.uniform_singleton_pos_of_mem Hz0 (le_refl 0) Hz0
  have hpos1 : 0 < Cfg.uniform z σ {⟨.lit (.int 1), σ⟩} :=
    Cfg.uniform_singleton_pos_of_mem Hz0 (by norm_num) Hz
  -- The two configurations are distinct.
  have hne : (⟨.lit (.int 0), σ⟩ : Cfg) ≠ ⟨.lit (.int 1), σ⟩ := by
    intro heq
    have := (Cfg.mk.injEq ..).mp heq |>.1
    simp at this
  -- From `{ρ} = 1` and probability measure total mass = 1, we get
  -- `{ρ}ᶜ` has measure zero.
  have hcompl : Cfg.uniform z σ ({ρ}ᶜ) = 0 := by
    have htot : Cfg.uniform z σ Set.univ = 1 := hprob.measure_univ
    have hsplit : Cfg.uniform z σ Set.univ =
        Cfg.uniform z σ {ρ} + Cfg.uniform z σ ({ρ}ᶜ) := by
      rw [← MeasureTheory.measure_add_measure_compl (s := {ρ}) MeasurableSet.of_discrete]
    rw [htot, h1] at hsplit
    -- `1 = 1 + x` in `ℝ≥0∞` forces `x = 0` (since `1 ≠ ⊤`).
    have hone_ne_top : (1 : ENNReal) ≠ ⊤ := ENNReal.one_ne_top
    have heq : (1 : ENNReal) + 0 = 1 + Cfg.uniform z σ ({ρ}ᶜ) := by
      rw [add_zero]; exact hsplit
    exact ((ENNReal.add_right_inj hone_ne_top).mp heq).symm
  -- At least one of the two points `⟨.lit (.int 0), σ⟩`, `⟨.lit (.int 1), σ⟩`
  -- is distinct from `ρ`, hence lies in `{ρ}ᶜ`, hence has mass zero —
  -- contradicting the positivity result.
  by_cases h0 : (⟨.lit (.int 0), σ⟩ : Cfg) = ρ
  · -- Then ⟨.lit (.int 1), σ⟩ ≠ ρ.
    have hnρ : (⟨.lit (.int 1), σ⟩ : Cfg) ≠ ρ := by
      intro heq; apply hne; rw [h0, ← heq]
    have hin : (⟨.lit (.int 1), σ⟩ : Cfg) ∈ ({ρ} : Set Cfg)ᶜ := by
      simp [Set.mem_compl_iff, Set.mem_singleton_iff, hnρ]
    have : Cfg.uniform z σ {⟨.lit (.int 1), σ⟩} ≤ Cfg.uniform z σ ({ρ}ᶜ) :=
      MeasureTheory.measure_mono (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx; exact hin)
    rw [hcompl] at this
    exact absurd (lt_of_lt_of_le hpos1 this) (lt_irrefl _)
  · -- Then ⟨.lit (.int 0), σ⟩ ≠ ρ.
    have hin : (⟨.lit (.int 0), σ⟩ : Cfg) ∈ ({ρ} : Set Cfg)ᶜ := by
      simp [Set.mem_compl_iff, Set.mem_singleton_iff, h0]
    have : Cfg.uniform z σ {⟨.lit (.int 0), σ⟩} ≤ Cfg.uniform z σ ({ρ}ᶜ) :=
      MeasureTheory.measure_mono (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx; exact hin)
    rw [hcompl] at this
    exact absurd (lt_of_lt_of_le hpos0 this) (lt_irrefl _)

/-- Clutch's `head_step_dzero_upd_tapes`: if `headStep ⟨e, σ⟩` is the
zero measure (nothing reducible), then appending a presample to an
already-present tape keeps it zero. The Clutch version appends a
single sample; we state it at the whole-tape-update level.

Proof deferred: requires a case analysis on `e` mirroring the
`headStep` definition. The only case that interacts with the tapes
component is `.rand _ (.lit (.lbl α))`, and appending to an existing
tape never creates new reductions. -/
theorem State.head_step_dzero_upd_tapes
    {e : Exp} {σ : State} {α : Loc} {bs bs' : Tape}
    (hmem : σ.tapes[α]? = some bs)
    (h0 : ProbLang.headStep ⟨e, σ⟩ = 0) :
    ProbLang.headStep ⟨e, σ.update_tapes (·.insert α bs')⟩ = 0 := by
  revert h0
  head_case
  -- Dispatch the trivially-zero and state-irrelevant cases via `head_case`
  -- split. A handful of state-dependent cases remain (`alloc.no_redex`,
  -- `load.segfault`, `store.no_redex`/`segfault`, `rand.plain`,
  -- `rand.tape.*`) — each is tractable but needs individual finishing.
  all_goals try (intro h0; simpa using h0)
  all_goals try (intro h0; simp_all)
  all_goals try (intro h0; unfold Option.unwrapM at h0 ⊢; split at h0 <;> simp_all)
  -- Remaining cases: unop.redex, binop.redex, alloc.no_redex,
  -- load.segfault, store.no_redex, store.segfault, rand.plain,
  -- rand.tape.unalloc, rand.tape.mismatch, rand.tape.empty.
  case unop.redex h0 =>
    unfold Option.unwrapM at h0 ⊢
    split <;> rename_i hopt
    · rw [hopt] at h0
      exact absurd h0 MeasureTheory.Measure.dirac_ne_zero
    · rfl
  case binop.redex h0 =>
    unfold Option.unwrapM at h0 ⊢
    split <;> rename_i hopt
    · rw [hopt] at h0
      exact absurd h0 MeasureTheory.Measure.dirac_ne_zero
    · rfl
  case alloc.no_redex hned =>
    simp [Exp.toVal?_eq_none.mpr hned]
  case load.segfault hheap =>
    -- (σ.update_tapes f).heap = σ.heap, so the segfault persists.
    have hnotmem : ‹Loc› ∉ (σ.update_tapes (·.insert α bs')).heap := hheap
    have hnone := Option.not_isSome_iff_eq_none.mp
      (fun hsome => hnotmem (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr hsome))
    rw [hnone]
  case store.no_redex hned =>
    simp [Exp.toVal?_eq_none.mpr hned]
  case store.segfault hv hheap =>
    have hnotmem : ‹Loc› ∉ (σ.update_tapes (·.insert α bs')).heap := hheap
    have hnone := Option.not_isSome_iff_eq_none.mp
      (fun hsome => hnotmem (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr hsome))
    rw [hnone]
  case rand.plain h0 =>
    rw [Cfg.uniform_eq_zero_iff] at h0 ⊢; exact h0
  case rand.tape.unalloc hnotin =>
    have hne : α ≠ ‹Lbl› := by
      intro he
      exact hnotin (he ▸ Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [hmem]; rfl))
    have hnone : σ.tapes[‹Lbl›]? = none :=
      Option.not_isSome_iff_eq_none.mp
        (fun hsome => hnotin (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr hsome))
    rw [State.upd_diff_tape_tot (Ne.symm hne), hnone]
  case rand.tape.mismatch =>
    -- Inaccessibles: ..., α'_lbl : Lbl, _ : Option Tape, M' : ℤ, ns_orig : List, heq, hMne
    -- Already named: h0 (from dispatch).
    rename_i _ z' α' _ M' _ heq hMne
    rw [Cfg.uniform_eq_zero_iff] at h0
    by_cases hαeq : α = α'
    · subst hαeq
      have hupd : (σ.update_tapes (·.insert α bs')).tapes[α]? = some bs' :=
        State.upd_tape_some σ α bs'
      rw [hupd]
      -- Goal: an `if M = z' then ... else Cfg.uniform z' new_σ` over bs'.{bound,presamples}
      obtain ⟨bbnd, bps⟩ := bs'
      simp only
      by_cases hbnd : bbnd = z'
      · subst hbnd
        simp only [if_true]
        cases bps with
        | nil => rw [Cfg.uniform_eq_zero_iff]; exact h0
        | cons n _ =>
          exfalso; apply h0
          have hn := n.2
          omega
      · simp only [if_neg hbnd]
        rw [Cfg.uniform_eq_zero_iff]; exact h0
    · have hupd : (σ.update_tapes (·.insert α bs')).tapes[α']? = σ.tapes[α']? :=
        State.upd_diff_tape_tot (Ne.symm hαeq)
      rw [hupd, heq]
      simp only [if_neg hMne]
      rw [Cfg.uniform_eq_zero_iff]; exact h0
  case rand.tape.empty =>
    rename_i _ z' α' _ _ heq
    rw [Cfg.uniform_eq_zero_iff] at h0
    by_cases hαeq : α = α'
    · subst hαeq
      have hupd : (σ.update_tapes (·.insert α bs')).tapes[α]? = some bs' :=
        State.upd_tape_some σ α bs'
      rw [hupd]
      obtain ⟨bbnd, bps⟩ := bs'
      simp only
      by_cases hbnd : bbnd = z'
      · subst hbnd
        simp only [if_true]
        cases bps with
        | nil => rw [Cfg.uniform_eq_zero_iff]; exact h0
        | cons n _ =>
          exfalso; apply h0
          have hn := n.2
          omega
      · simp only [if_neg hbnd]
        rw [Cfg.uniform_eq_zero_iff]; exact h0
    · have hupd : (σ.update_tapes (·.insert α bs')).tapes[α']? = σ.tapes[α']? :=
        State.upd_diff_tape_tot (Ne.symm hαeq)
      rw [hupd, heq]
      simp only [if_true]
      rw [Cfg.uniform_eq_zero_iff]; exact h0

/-- Clutch's `det_head_step_upd_tapes`: a deterministic head step is
preserved by appending to an unrelated tape. The hypothesis
`DetHeadStep ⟨e1, σ⟩ ⟨e2, σ⟩` requires the post-state to equal the
pre-state, which excludes the state-modifying head steps
(`alloc`/`store`/`tape`/`rand`/`rand-tape`); the surviving cases all
read at most the heap, so they are unaffected by a tape update.

**Known limitation (2 deferred sorries):** under our `{0, …, N−1}` rand
semantics, `rand 1` is genuinely deterministic (it always produces 0),
so the `RandTapeEmptyS` and `RandTapeOtherS` cases at `z = 1` are no
longer impossible via the "rand isn't dirac" argument. Their
conclusions fail when the updated tape `α` coincides with the rand's
label `α_rand`: `σ.update_tapes (·.insert α bs')` introduces an
arbitrary `bs'` at `α_rand`, whose dirac value may differ from the
original. Closing these cases properly requires adding a premise
`α ≠ α_rand` or otherwise restricting overlap; left deferred since
the theorem has no callers yet. The `RandNoTapeS` case is closed
directly since `rand 1 unit` has no tape interaction. -/
theorem State.det_head_step_upd_tapes
    {e1 e2 : Exp} {σ : State} {α : Loc} {bs bs' : Tape}
    (hmem : σ.tapes[α]? = some bs)
    (hdet : ProbLang.DetHeadStep ⟨e1, σ⟩ ⟨e2, σ⟩) :
    ProbLang.DetHeadStep
      ⟨e1, σ.update_tapes (·.insert α bs')⟩
      ⟨e2, σ.update_tapes (·.insert α bs')⟩ := by
  -- First convert the determinism witness into a HeadStepSupport, then
  -- case-split on the support.
  have hpos := hdet.pos
  have hsupp : HeadStepSupport ⟨e1, σ⟩ ⟨e2, σ⟩ :=
    (headStep_support_iff e1 e2 σ σ).mp hpos
  cases hsupp with
  | BetaS hv heq =>
    refine .of_det _ _ ?_
    subst heq
    simp [headStep, Exp.isValM_some hv]
  | UnOpS hv heval =>
    refine .of_det _ _ ?_
    simp [headStep, Option.unwrapM, Exp.isValM_some hv, ← heval]
  | BinOpS hv1 hv2 heval =>
    refine .of_det _ _ ?_
    simp [headStep, Option.unwrapM, Exp.isValM_some hv1, Exp.isValM_some hv2, ← heval]
  | IfTrueS => refine .of_det _ _ ?_; simp [headStep]
  | IfFalseS => refine .of_det _ _ ?_; simp [headStep]
  | FstS hv1 hv2 =>
    refine .of_det _ _ ?_
    simp [headStep, Exp.isValM_some hv1, Exp.isValM_some hv2]
  | SndS hv1 hv2 =>
    refine .of_det _ _ ?_
    simp [headStep, Exp.isValM_some hv1, Exp.isValM_some hv2]
  | CaseLS hv =>
    refine .of_det _ _ ?_
    simp [headStep, Exp.isValM_some hv]
  | CaseRS hv =>
    refine .of_det _ _ ?_
    simp [headStep, Exp.isValM_some hv]
  | AllocS hv heq hσ =>
    exfalso
    rename_i vd _ ed
    subst heq
    have hheap : σ.heap = σ.heap.insert σ.heap.fresh vd := by
      have := congrArg State.heap hσ
      simpa [State.update_heap] using this
    have h2 : σ.heap[σ.heap.fresh]? = none := Std.ExtTreeMap.fresh_get? σ.heap
    have hcmp : compare σ.heap.fresh σ.heap.fresh = .eq := by
      simp [compare, compareOfLessAndEq]
    have h3 : (σ.heap.insert σ.heap.fresh vd)[σ.heap.fresh]? = some vd := by
      rw [Std.ExtTreeMap.getElem?_insert, hcmp]; rfl
    rw [← hheap] at h3
    rw [h2] at h3
    cases h3
  | LoadS hlook heq =>
    refine .of_det _ _ ?_
    subst heq
    simp [headStep]
    -- (σ.update_tapes f).heap = σ.heap
    have : (σ.update_tapes (·.insert α bs')).heap[‹Loc›]? = some ‹Val› := hlook
    rw [this]
    simp
  | StoreS htoval hsome hσ =>
    refine .of_det _ _ ?_
    rename_i v ℓ _
    have hheap_no_op : σ.heap.insert ℓ v = σ.heap := by
      have := congrArg State.heap hσ
      simpa [State.update_heap] using this.symm
    obtain ⟨v_old, hv_old⟩ := Option.isSome_iff_exists.mp hsome
    have hheap_lookup : (σ.update_tapes (·.insert α bs')).heap[ℓ]? = some v_old := hv_old
    simp only [headStep, Exp.asValM, htoval, hheap_lookup]
    have hgoal_state : (σ.update_tapes (·.insert α bs')).update_heap (·.insert ℓ v) =
        (σ.update_tapes (·.insert α bs')) := by
      simp [State.update_heap, State.update_tapes, hheap_no_op]
    rw [hgoal_state]
    simp [MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_singleton _)]
  | RandNoTapeS hz hv0 hvz =>
    -- For `1 < z`: `Cfg.uniform z σ` has ≥ 2 support points, exfalso.
    -- For `z = 1`: `rand 1 unit` is a dirac at `v = 0`, and the step
    -- is genuinely deterministic. We prove it directly via `of_det`
    -- using `Cfg.uniform_one_eq_dirac`.
    rename_i z _
    by_cases hz1 : 1 < z
    · exfalso
      have hdet' := hdet.det
      simp only [headStep] at hdet'
      exact Cfg.uniform_singleton_ne_one hz1 hdet'
    · -- z = 1 (since 0 < z and ¬ 1 < z).
      have hzeq : z = 1 := by omega
      have hveq : ‹Int› = 0 := by omega
      subst hzeq; subst hveq
      refine .of_det _ _ ?_
      simp only [headStep, Cfg.uniform_one_eq_dirac,
                 MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_singleton _)]
  | TapeS heq hσ =>
    exfalso
    -- Post-state inserts a fresh tape; lookup at fresh in σ is none.
    have hfresh_none : σ.tapes[σ.tapes.fresh]? = none := Std.ExtTreeMap.fresh_get? σ.tapes
    have htapes_eq : σ.tapes = σ.tapes.insert σ.tapes.fresh (Tape.empty ‹Int›) := by
      have := congrArg State.tapes hσ
      have heq' := heq
      simpa [State.update_tapes, ← heq'] using this
    have hcmp : compare σ.tapes.fresh σ.tapes.fresh = .eq := by
      simp [compare, compareOfLessAndEq]
    have hsome : (σ.tapes.insert σ.tapes.fresh (Tape.empty ‹Int›))[σ.tapes.fresh]? =
        some (Tape.empty ‹Int›) := by
      rw [Std.ExtTreeMap.getElem?_insert, hcmp]; rfl
    rw [← htapes_eq] at hsome
    rw [hfresh_none] at hsome
    cases hsome
  | RandTapeS hz htape hzN hv hσ =>
    exfalso
    -- State mismatch. After the step the tape at the label becomes `⟨N, ns⟩`,
    -- but `hσ` says the state is unchanged — so σ's tape at that label
    -- is `⟨N, ns⟩` too, contradicting `htape : σ.tapes[·]? = some ⟨N, nn :: ns⟩`.
    have hσ_tapes := congrArg State.tapes hσ
    simp only [State.update_tapes] at hσ_tapes
    have h2 := htape
    rw [hσ_tapes] at h2
    simp only [Std.ExtTreeMap.getElem?_insert,
      show ∀ l : Lbl, compare l l = Ordering.eq from
        fun l => by simp [compare, compareOfLessAndEq],
      if_true] at h2
    -- h2 : some ⟨N, ns⟩ = some ⟨N, nn :: ns⟩ (bounds match, lists differ)
    -- Taking `Tape.presamples` of both sides eliminates dependent-type HEq.
    have hcontra : ∀ {N : Int} {l1 l2 : List _}, (some ⟨N, l1⟩ : Option Tape) = some ⟨N, l2⟩ → l1 = l2 := by
      rintro _ _ _ heq
      exact (Tape.mk.injEq ..).mp (Option.some.inj heq) |>.2 |> eq_of_heq
    have hlist := hcontra h2
    exact absurd hlist.symm (List.cons_ne_self _ _)
  | RandTapeEmptyS hz htape hzN _ _ _ =>
    -- For `1 < z`: `Cfg.uniform z σ` has ≥ 2 support points, exfalso.
    -- For `z = 1`: `rand 1 (lbl α_rand)` is a dirac, but the theorem's
    -- conclusion fails when the updated tape `α` overlaps `α_rand`
    -- (the post-headStep value depends on `σ_new.tapes[α_rand]`, which
    -- is `bs'` under overlap and may not produce the same dirac as σ).
    -- **Deferred** with signature limitation: this case would require
    -- a premise `α ≠ α_rand` (or restricting the theorem to non-overlapping
    -- tape updates). The theorem is currently unused; see Clutch's
    -- `det_head_step_upd_tapes` for the intended scope.
    sorry
  | RandTapeOtherS hz htape hzN _ _ _ =>
    -- Same story as RandTapeEmptyS: for `z = 1` with `α = α_rand`,
    -- the theorem conclusion depends on the arbitrary replacement tape
    -- content `bs'`, which is unconstrained. Deferred with signature
    -- limitation.
    sorry
  | ScrutSuccessS hv hm =>
    refine .of_det _ _ ?_
    simp [headStep, Exp.isValM_some hv, hm]
  | ScrutFailureS hv hm =>
    refine .of_det _ _ ?_
    simp [headStep, Exp.isValM_some hv, hm]
  | AnnotS hv =>
    refine .of_det _ _ ?_
    simp [headStep, Exp.isValM_some hv]

/-- Clutch's `prim_step_empty_tape`: reading from an empty-presample
tape is the same as reading from the "no-tape" marker `.lit .unit`.
In our representation an empty tape is `⟨N, []⟩`.

**Signature note:** Clutch states this with `z : Z` (a raw Rocq integer,
automatically a value via `#z`); we mirror that with `z : Int` and
quote it as `.lit (.int z)` on both sides. An earlier attempt with
`z : Exp` is genuinely not provable, since for non-value `z` the two
sides recurse into stepping `z` under different `.randL` contexts,
yielding measures with disjoint support. -/
theorem State.prim_step_empty_tape
    {K : ProbLang.Ectx} {σ : State} {α : Loc} {z : Int} {N : Int}
    (_hmem : σ.tapes[α]? = some ⟨N, []⟩) :
    ProbLang.primStep ⟨K.fill (.rand (.lit (.int z)) (.lit (.lbl α))), σ⟩
      = ProbLang.primStep ⟨K.fill (.rand (.lit (.int z)) (.lit .unit)), σ⟩ := by
  -- The outer context `K` is irrelevant: `.rand _ _` is never a value,
  -- so we can pull K out on both sides via `primStep_fill`.
  have hv_lbl : ¬ (Exp.rand (.lit (.int z)) (.lit (.lbl α))).isValue := by
    intro h; obtain ⟨hv⟩ := h; cases hv
  have hv_unit : ¬ (Exp.rand (.lit (.int z)) (.lit .unit)).isValue := by
    intro h; obtain ⟨hv⟩ := h; cases hv
  rw [primStep_fill hv_lbl, primStep_fill hv_unit]
  -- It suffices to show the inner measures agree.
  suffices h : ProbLang.primStep ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩
      = ProbLang.primStep ⟨.rand (.lit (.int z)) (.lit .unit), σ⟩ by rw [h]
  -- Both args are values, so `decompItem = none` and `primStep = headStep`.
  have hdecomp_lbl : (Exp.rand (.lit (.int z)) (.lit (.lbl α))).decomp
      = ([], .rand (.lit (.int z)) (.lit (.lbl α))) := by
    rw [Exp.decomp_unfold]
    simp only [Exp.decompItem]
    have hlbl : (Exp.lit (.lbl α)).toVal? = some ⟨.lit (.lbl α), .lit⟩ := rfl
    have hint : (Exp.lit (.int z)).toVal? = some ⟨.lit (.int z), .lit⟩ := rfl
    rw [hlbl, hint]
  have hdecomp_unit : (Exp.rand (.lit (.int z)) (.lit .unit)).decomp
      = ([], .rand (.lit (.int z)) (.lit .unit)) := by
    rw [Exp.decomp_unfold]
    simp only [Exp.decompItem]
    have hunit : (Exp.lit .unit).toVal? = some ⟨.lit .unit, .lit⟩ := rfl
    have hint : (Exp.lit (.int z)).toVal? = some ⟨.lit (.int z), .lit⟩ := rfl
    rw [hunit, hint]
  simp only [primStep, hdecomp_lbl, hdecomp_unit, Ectx.fillCfg_empty, MeasureTheory.Measure.map_id]
  -- Both sides reduce to `Cfg.uniform z σ`: the `lbl α` side hits
  -- `RandTape*`, finds an empty-presample tape via `_hmem`, and the
  -- `if M = z` collapses to `Cfg.uniform z σ` regardless (via `ite_self`).
  simp only [headStep, _hmem]
  rw [ite_self]

end ProbLang
