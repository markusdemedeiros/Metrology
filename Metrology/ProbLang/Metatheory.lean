import Metrology.ProbLang.DetStep
import Metrology.ProbLang.Exec
import Metrology.ProbLang.Syntax.Properties

namespace ProbLang
open Cslib Exp

/-! ## Group A — Closed contexts and the `isClosed` predicate

In the locally-nameless encoding, a "closed context" is just a finite set of
atoms (free variables) in scope. A term is *closed* in `X` when it is locally
closed (no dangling de-Bruijn indices) and its free variables are all in `X`.

Port of Clutch's `is_closed` / `is_closed_weaken` on top of LN. The old
`String → Bool` encoding and `Binder.binds` bookkeeping collapse away. -/

/-- Closed context: a finite set of free-variable atoms. -/
abbrev ClosedCtx := Finset Var

namespace ClosedCtx

def empty : ClosedCtx := ∅

def insert (X : ClosedCtx) (x : Var) : ClosedCtx := Insert.insert x X

/-- Subset of closed contexts. -/
def subset (X Y : ClosedCtx) : Prop := X ⊆ Y

theorem subset.insert {X Y : ClosedCtx} (h : X.subset Y) (x : Var) :
    (X.insert x).subset (Y.insert x) := by
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (h hz)

end ClosedCtx

/-- `Exp.isClosed X e` : `e` is locally closed and every free variable of `e` is in `X`. -/
def Exp.isClosed (X : ClosedCtx) (e : Exp) : Prop := e.IsLocallyClosed ∧ e.fv ⊆ X

theorem Exp.isClosed_weaken {X Y : ClosedCtx} (hXY : X.subset Y)
    {e : Exp} (h : e.isClosed X) : e.isClosed Y :=
  ⟨h.1, fun _ hz => hXY (h.2 hz)⟩

theorem Exp.isClosed_weaken_empty {X : ClosedCtx} {e : Exp}
    (h : e.isClosed .empty) : e.isClosed X := by
  refine ⟨h.1, fun z hz => ?_⟩
  have := h.2 hz
  simp [ClosedCtx.empty] at this

/-! ## Group B — Substitution maps

An LN substitution map is a finite association list from atoms to LC terms.
Application walks the expression and applies each substitution in turn. No
binder bookkeeping is needed: `subst` is capture-free.
-/

/-- Finite substitution map from atoms to expressions. -/
abbrev SubstMap := List (Var × Exp)

namespace SubstMap

def empty : SubstMap := []

/-- Insert a (var, value) pair, shadowing any existing binding for the key. -/
def insert (vs : SubstMap) (x : Var) (v : Exp) : SubstMap := (x, v) :: vs

/-- Remove all entries for `x`. -/
def delete (vs : SubstMap) (x : Var) : SubstMap :=
  vs.filter (fun p => p.1 ≠ x)

end SubstMap

/-- Apply a substitution map: fold `subst` left-to-right.
    Each pair `(x, v)` replaces free `fvar x` by `v` in the current accumulator. -/
def Exp.substMap (vs : SubstMap) (e : Exp) : Exp :=
  vs.foldr (fun p acc => Exp.subst acc p.1 p.2) e

@[simp] theorem Exp.substMap_empty (e : Exp) : e.substMap .empty = e := rfl

@[simp] theorem Exp.substMap_insert (vs : SubstMap) (x : Var) (v e : Exp) :
    e.substMap (vs.insert x v) = Exp.subst (e.substMap vs) x v := rfl

/-- A substitution that substitutes a single variable. -/
theorem Exp.substMap_singleton (x : Var) (v e : Exp) :
    e.substMap [(x, v)] = Exp.subst e x v := rfl

/-! ### Substitution and closedness -/

/-- Substitution of a value with no free variables in `X` preserves closedness in `X`. -/
theorem Exp.subst_isClosed {X : ClosedCtx} {e v : Exp} {x : Var}
    (he : e.isClosed (X.insert x)) (hv : v.isClosed X) :
    (Exp.subst e x v).isClosed X := by
  refine ⟨Exp.subst_lc he.1 hv.1, ?_⟩
  intro z hz
  have hsub := Exp.fv_subst_subset e x v hz
  rcases Finset.mem_union.mp hsub with h | h
  · have ⟨hfv, hne⟩ := Finset.mem_sdiff.mp h
    have := he.2 hfv
    rcases Finset.mem_insert.mp this with rfl | hx
    · exact absurd (Finset.mem_singleton.mpr rfl) hne
    · exact hx
  · exact hv.2 h

/-- Substitution of a closed-in-`X` value into a closed-in-`X.insert x` term is closed in `X`. -/
theorem Exp.subst_is_closed {e : Exp} {x : Var} {v : Exp} {X : ClosedCtx}
    (he : e.isClosed (X.insert x)) (hv : v.isClosed X) :
    (Exp.subst e x v).isClosed X :=
  Exp.subst_isClosed he hv

/-- Substitution of a fully closed value. -/
theorem Exp.subst_is_closed_empty {e : Exp} {x : Var} {v : Exp}
    (he : e.isClosed (ClosedCtx.empty.insert x)) (hv : v.isClosed .empty) :
    (Exp.subst e x v).isClosed .empty :=
  Exp.subst_is_closed he hv

/-! ### Commutation of substitutions -/

/-- Substitutions at different variables commute when `v'` has no `x` free. -/
theorem Exp.subst_subst {e v v' : Exp} {x : Var} {y : Var}
    (hne : x ≠ y) (hv' : x ∉ v'.fv) (_hv'_lc : v'.IsLocallyClosed) :
    Exp.subst (Exp.subst e x v) y v'
      = Exp.subst (Exp.subst e y v') x (Exp.subst v y v') := by
  induction e with
  | fvar z =>
      by_cases h1 : x = z <;> by_cases h2 : y = z
      · subst h1; exact absurd h2 hne.symm
      · subst h1
        have hs : Exp.subst v' x v' = v' := Exp.subst_fresh _ _ _ hv'
        simp [Exp.subst, h2, hs]
      · subst h2
        have hv'_fresh : Exp.subst v' x (Exp.subst v y v') = v' :=
          Exp.subst_fresh _ _ _ hv'
        simp [Exp.subst, h1, hv'_fresh]
      · simp [Exp.subst, h1, h2]
  | bvar _ | lit _ | fail => rfl
  | lam e ih | fix e ih | unop _ e ih | fst e ih | snd e ih
  | inl e ih | inr e ih | alloc e ih | load e ih | tape e ih | scrut e _ ih =>
      simp [Exp.subst, ih]
  | app e1 e2 ih1 ih2 | binop _ e1 e2 ih1 ih2 | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2 | rand e1 e2 ih1 ih2 =>
      simp [Exp.subst, ih1, ih2]
  | cond e0 e1 e2 ih0 ih1 ih2 | case e0 e1 e2 ih0 ih1 ih2 =>
      simp [Exp.subst, ih0, ih1, ih2]

/-- Independence of substitutions at distinct, mutually-fresh variables. -/
theorem Exp.subst_subst_ne {e v v' : Exp} {x y : Var}
    (hne : x ≠ y) (hxv' : x ∉ v'.fv) (hyv : y ∉ v.fv)
    (hv_lc : v.IsLocallyClosed) (hv'_lc : v'.IsLocallyClosed) :
    Exp.subst (Exp.subst e x v) y v' = Exp.subst (Exp.subst e y v') x v := by
  rw [Exp.subst_subst hne hxv' hv'_lc]
  rw [Exp.subst_fresh y v v' hyv]

/-! ### Substitution-map-level closedness lemmas

Ports of `SubstMap.deleteB_preserves_closed`, `Exp.substMap_isClosed`,
`Exp.substMap_isClosed_empty`. The original (Binder/String) versions had
to thread the binder-shadowing dance through `deleteB`; under LN there is
no shadowing and the proofs simplify to fold-style induction over the list.

The key invariant is "every value in `vs` is locally-closed and has empty
free-variable set" — i.e., the substitution range consists of fully-closed
values. Under that invariant, `substMap` reduces to repeated `subst`. -/

/-- Predicate: every value bound in the substitution map is fully closed. -/
def SubstMap.AllClosed (vs : SubstMap) : Prop :=
  ∀ p ∈ vs, p.2.isClosed .empty

theorem SubstMap.AllClosed_nil : SubstMap.AllClosed ([] : SubstMap) := by
  intro p hp; cases hp

theorem SubstMap.AllClosed_cons {x v vs} :
    SubstMap.AllClosed ((x, v) :: vs) ↔ v.isClosed .empty ∧ SubstMap.AllClosed vs := by
  constructor
  · intro h
    refine ⟨h (x, v) (List.mem_cons_self), fun p hp => h p (List.mem_cons_of_mem _ hp)⟩
  · rintro ⟨hv, hvs⟩ p hp
    rcases List.mem_cons.mp hp with rfl | hpm
    · exact hv
    · exact hvs p hpm

theorem SubstMap.AllClosed_delete {vs : SubstMap} (x : Var)
    (h : SubstMap.AllClosed vs) : SubstMap.AllClosed (vs.delete x) := by
  intro p hp
  have hmem : p ∈ vs := by
    have := List.mem_filter.mp hp; exact this.1
  exact h p hmem

/-- `substMap` through a closed expression is a no-op (Clutch's
`Exp.substMap_isClosed` for the empty `X = ∅` case). -/
theorem Exp.substMap_isClosed_empty {e : Exp} (vs : SubstMap)
    (he : e.isClosed .empty) : e.substMap vs = e := by
  -- Closed expression has fv ⊆ ∅, so no `subst` step changes it.
  induction vs with
  | nil => rfl
  | cons p vs ih =>
      simp only [substMap, List.foldr_cons]
      -- After IH: e.substMap vs = e. Then subst at p.1 with p.2 is identity
      -- since p.1 ∉ e.fv (e has no free vars at all).
      rw [show vs.foldr (fun q acc => Exp.subst acc q.1 q.2) e = e from ih]
      apply Exp.subst_fresh
      intro hcontra
      have := he.2 hcontra
      simp [ClosedCtx.empty] at this

/-- General version: if `e` is closed in `X` and `vs` only assigns variables
NOT in `X`, then `substMap vs e = e`. (Clutch's `substMap_isClosed`.) -/
theorem Exp.substMap_isClosed {X : ClosedCtx} {e : Exp} (vs : SubstMap)
    (he : e.isClosed X)
    (hvs : ∀ p ∈ vs, p.1 ∉ X) :
    e.substMap vs = e := by
  induction vs with
  | nil => rfl
  | cons p vs ih =>
      simp only [substMap, List.foldr_cons]
      have hvs' : ∀ q ∈ vs, q.1 ∉ X :=
        fun q hq => hvs q (List.mem_cons_of_mem _ hq)
      rw [show vs.foldr (fun q acc => Exp.subst acc q.1 q.2) e = e from ih hvs']
      -- Now subst e p.1 p.2 = e since p.1 ∉ e.fv (because p.1 ∉ X ⊇ e.fv).
      apply Exp.subst_fresh
      have hp1_notin : p.1 ∉ X := hvs p List.mem_cons_self
      intro hcontra
      exact hp1_notin (he.2 hcontra)

/-! ### Substitution-map insertion (closed-range version)

Port of Clutch's `substMap_insert`: extending a substitution map with a
single binding decomposes into a `subst'` followed by a `substMap` on the
deleted environment. The proof is much simpler under LN — `insert` is just
`cons`, so `substMap (cons p vs) e = subst (substMap vs e) p.1 p.2`
holds definitionally. -/

@[simp] theorem Exp.substMap_cons (p : Var × Exp) (vs : SubstMap) (e : Exp) :
    e.substMap (p :: vs) = Exp.subst (e.substMap vs) p.1 p.2 := rfl

/-! ## Group D — Deterministic / probabilistic head-step characterization

Predicate-based step classification (Clutch's `metatheory.v` ~1448–1713,
minus Laplace/Tick). The `HeadStepSupport` relation lives in `HeadStep.lean`. -/

/-- Expressions that take a single deterministic head step in state `σ`. -/
inductive DetHeadStepPred : Exp → State → Prop
  | betaLam {e1 e2 σ} : e2.isValue →
      DetHeadStepPred (.app (.lam e1) e2) σ
  | betaFix {e1 e2 σ} : e2.isValue →
      DetHeadStepPred (.app (.fix e1) e2) σ
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

/-- Expressions that take a probabilistic head step in state `σ`. -/
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

/-- Boolean test for determinism of a head step. -/
def isDetHeadStep (e : Exp) (σ : State) : Bool :=
  match e with
  | .app (.lam _) e2 => decide e2.isValue
  | .app (.fix _) e2 => decide e2.isValue
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
  | _ => false

/-- Values don't take head steps. -/
theorem val_not_HeadStepPred {e : Exp} {σ : State}
    (hv : e.isValue) : ¬ HeadStepPred e σ := by
  rw [Exp.isValue_iff_isValueR] at hv
  rintro (hdet | hprob)
  · cases hdet <;> simp [Exp.isValueR] at hv
  · cases hprob <;> simp [Exp.isValueR] at hv

/-- `isDetHeadStep ↔ DetHeadStepPred`. -/
theorem isDetHeadStep_iff_pred (e : Exp) (σ : State) :
    isDetHeadStep e σ = true ↔ DetHeadStepPred e σ := by
  constructor
  · intro h
    unfold isDetHeadStep at h
    split at h
    · exact .betaLam (by simpa using h)
    · exact .betaFix (by simpa using h)
    · rw [Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at h
      obtain ⟨hv, e'', heval⟩ := h
      exact .unop hv heval
    · rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          decide_eq_true_eq, Option.isSome_iff_exists] at h
      obtain ⟨⟨hv1, hv2⟩, e', heval⟩ := h
      exact .binop hv1 hv2 heval
    · rename_i b _ _
      cases b with
      | true => exact .ifTrue
      | false => exact .ifFalse
    · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
      exact .fst h.1 h.2
    · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
      exact .snd h.1 h.2
    · rw [decide_eq_true_eq] at h
      exact .caseL h
    · rw [decide_eq_true_eq] at h
      exact .caseR h
    · rw [decide_eq_true_eq] at h
      exact .alloc h
    · rw [Option.isSome_iff_exists] at h
      obtain ⟨v, hv⟩ := h
      exact .load hv
    · rw [Bool.and_eq_true, decide_eq_true_eq] at h
      exact .store h.1 h.2
    · exact .tape
    · rename_i e p
      rw [decide_eq_true_eq] at h
      cases hm : Pat.tryMatch p e with
      | some bindings => exact .scrutSuccess h hm
      | none => exact .scrutFailure h hm
    · simp at h
  · intro hpred
    cases hpred with
    | betaLam hv => simp [isDetHeadStep, hv]
    | betaFix hv => simp [isDetHeadStep, hv]
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

theorem HeadStepPred_iff_exists_support (e : Exp) (σ : State) :
    HeadStepPred e σ ↔ ∃ ρ', HeadStepSupport ⟨e, σ⟩ ρ' := by
  constructor
  · rintro (hdet | hprob)
    · cases hdet with
      | betaLam hv => exact ⟨_, .BetaLamS hv rfl⟩
      | betaFix hv => exact ⟨_, .BetaFixS hv rfl⟩
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
    | BetaLamS hv _ => exact .inl (.betaLam hv)
    | BetaFixS hv _ => exact .inl (.betaFix hv)
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
    | RandNoTapeS hz _ _ => exact .inr (.randNoTape hz)
    | RandTapeS hz htape hzN _ _ => exact .inr (.randTape hz htape hzN)
    | RandTapeEmptyS hz htape hzN _ _ _ => exact .inr (.randTapeEmpty hz htape hzN)
    | RandTapeOtherS hz htape hzN _ _ _ => exact .inr (.randTapeOther hz htape hzN)

theorem not_HeadStepPred_iff_zero (e : Exp) (σ : State) :
    ¬ HeadStepPred e σ ↔ headStep ⟨e, σ⟩ = 0 := by
  rw [HeadStepPred_iff_exists_support]
  constructor
  · intro hne
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

theorem det_or_prob_or_zero (e : Exp) (σ : State) :
    DetHeadStepPred e σ ∨ ProbHeadStepPred e σ ∨ headStep ⟨e, σ⟩ = 0 := by
  by_cases hpred : HeadStepPred e σ
  · rcases hpred with hdet | hprob
    · exact .inl hdet
    · exact .inr (.inl hprob)
  · exact .inr (.inr ((not_HeadStepPred_iff_zero e σ).mp hpred))

/-! ## Group E — Tape and fresh-location update lemmas -/

theorem State.upd_tape_some (σ : State) (α : Loc) (t : Tape) :
    (σ.update_tapes (·.insert α t)).tapes[α]? = some t := by
  simp [State.update_tapes]

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

theorem State.upd_diff_tape_tot {σ : State} {α β : Loc} {bs : Tape}
    (hne : α ≠ β) :
    (σ.update_tapes (·.insert β bs)).tapes[α]? = σ.tapes[α]? := by
  simp [State.update_tapes, Std.ExtTreeMap.getElem?_insert, Ne.symm hne]

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
      simp [Ordering.isLE, heq.symm]
    · have hlt : α < km := lt_of_le_of_ne hα_le_km heq
      have hcmp : compare km α = .gt := by
        show compareOfLessAndEq km α = .gt
        unfold compareOfLessAndEq
        have h1 : ¬ (km < α) := by omega
        have h2 : km ≠ α := by omega
        simp [h1, h2]
      simp [hcmp, Ordering.isLE]
  rw [hkeys]

theorem State.fresh_loc_upd_some {σ : State} {α : Loc} {bs bs' : Tape}
    (h : σ.tapes[α]? = some bs) :
    (σ.tapes.insert α bs').fresh = σ.tapes.fresh :=
  Std.ExtTreeMap.fresh_insert_of_mem σ.tapes h

theorem Std.ExtTreeMap.elem_fresh_ne
    {V : Type*} {t : Std.ExtTreeMap Int V compare} {k : Int} {v : V}
    (h : t[k]? = some v) : t.fresh ≠ k := by
  intro heq
  have hfresh := Std.ExtTreeMap.fresh_get? t
  rw [heq] at hfresh
  rw [hfresh] at h
  simp at h

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

theorem State.fresh_loc_lookup {σ : State} {α : Loc} {bs : Tape} {t : Tape}
    (h : σ.tapes[α]? = some bs) :
    (σ.tapes.insert σ.tapes.fresh t)[α]? = some bs := by
  have hne : σ.tapes.fresh ≠ α := Std.ExtTreeMap.elem_fresh_ne h
  rw [Std.ExtTreeMap.getElem?_insert]
  have hcmp : compare σ.tapes.fresh α ≠ .eq := by
    simp [compare, compareOfLessAndEq]
    split <;> simp_all
  simp [hcmp, h]

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

theorem Cfg.uniform_one_eq_dirac (σ : State) :
    Cfg.uniform 1 σ = MeasureTheory.Measure.dirac (⟨.lit (.int 0), σ⟩ : Cfg) := by
  classical
  unfold Cfg.uniform Int.isPos Option.unwrapM
  simp only [show (0 : Int) < 1 from Int.one_pos, dite_true]
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

theorem Cfg.uniform_singleton_ne_one {z : Int} {σ : State} {ρ : Cfg}
    (Hz : 1 < z) : Cfg.uniform z σ {ρ} ≠ 1 := by
  intro h1
  have Hz0 : 0 < z := by omega
  have hprob : MeasureTheory.IsProbabilityMeasure (Cfg.uniform z σ) :=
    Cfg.uniform_isProbabilityMeasure Hz0
  have hpos0 : 0 < Cfg.uniform z σ {⟨.lit (.int 0), σ⟩} :=
    Cfg.uniform_singleton_pos_of_mem Hz0 (le_refl 0) Hz0
  have hpos1 : 0 < Cfg.uniform z σ {⟨.lit (.int 1), σ⟩} :=
    Cfg.uniform_singleton_pos_of_mem Hz0 (by norm_num) Hz
  have hne : (⟨.lit (.int 0), σ⟩ : Cfg) ≠ ⟨.lit (.int 1), σ⟩ := by
    intro heq
    have := (Cfg.mk.injEq ..).mp heq |>.1
    simp at this
  have hcompl : Cfg.uniform z σ ({ρ}ᶜ) = 0 := by
    have htot : Cfg.uniform z σ Set.univ = 1 := hprob.measure_univ
    have hsplit : Cfg.uniform z σ Set.univ =
        Cfg.uniform z σ {ρ} + Cfg.uniform z σ ({ρ}ᶜ) := by
      rw [← MeasureTheory.measure_add_measure_compl (s := {ρ}) MeasurableSet.of_discrete]
    rw [htot, h1] at hsplit
    have hone_ne_top : (1 : ENNReal) ≠ ⊤ := ENNReal.one_ne_top
    have heq : (1 : ENNReal) + 0 = 1 + Cfg.uniform z σ ({ρ}ᶜ) := by
      rw [add_zero]; exact hsplit
    exact ((ENNReal.add_right_inj hone_ne_top).mp heq).symm
  by_cases h0 : (⟨.lit (.int 0), σ⟩ : Cfg) = ρ
  · have hnρ : (⟨.lit (.int 1), σ⟩ : Cfg) ≠ ρ := by
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
  · have hin : (⟨.lit (.int 0), σ⟩ : Cfg) ∈ ({ρ} : Set Cfg)ᶜ := by
      simp [Set.mem_compl_iff, Set.mem_singleton_iff, h0]
    have : Cfg.uniform z σ {⟨.lit (.int 0), σ⟩} ≤ Cfg.uniform z σ ({ρ}ᶜ) :=
      MeasureTheory.measure_mono (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx; exact hin)
    rw [hcompl] at this
    exact absurd (lt_of_lt_of_le hpos0 this) (lt_irrefl _)

set_option linter.unnecessarySimpa false in
theorem State.head_step_dzero_upd_tapes
    {e : Exp} {σ : State} {α : Loc} {bs bs' : Tape}
    (hmem : σ.tapes[α]? = some bs)
    (h0 : ProbLang.headStep ⟨e, σ⟩ = 0) :
    ProbLang.headStep ⟨e, σ.update_tapes (·.insert α bs')⟩ = 0 := by
  revert h0
  head_case
  all_goals try (intro h0; simpa using h0)
  all_goals try (intro h0; simp_all)
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
    rename_i _ z' α' _ M' _ heq hMne
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

theorem State.det_head_step_upd_tapes
    {e : Exp} {σ : State} {α : Loc} {bs' : Tape}
    (hdet : ProbLang.DetHeadStepPred e σ) :
    ProbLang.DetHeadStepPred e (σ.update_tapes (·.insert α bs')) := by
  cases hdet with
  | betaLam hv => exact .betaLam hv
  | betaFix hv => exact .betaFix hv
  | unop hv heval => exact .unop hv heval
  | binop hv1 hv2 heval => exact .binop hv1 hv2 heval
  | ifTrue => exact .ifTrue
  | ifFalse => exact .ifFalse
  | fst hv1 hv2 => exact .fst hv1 hv2
  | snd hv1 hv2 => exact .snd hv1 hv2
  | caseL hv => exact .caseL hv
  | caseR hv => exact .caseR hv
  | alloc hv => exact .alloc hv
  | load hlook => exact .load hlook
  | store hv hsome => exact .store hv hsome
  | tape => exact .tape
  | scrutSuccess hv hm => exact .scrutSuccess hv hm
  | scrutFailure hv hm => exact .scrutFailure hv hm

theorem State.prim_step_empty_tape
    {K : ProbLang.Ectx} {σ : State} {α : Loc} {z : Int} {N : Int}
    (_hmem : σ.tapes[α]? = some ⟨N, []⟩) :
    ProbLang.primStep ⟨K.fill (.rand (.lit (.int z)) (.lit (.lbl α))), σ⟩
      = ProbLang.primStep ⟨K.fill (.rand (.lit (.int z)) (.lit .unit)), σ⟩ := by
  have hv_lbl : ¬ (Exp.rand (.lit (.int z)) (.lit (.lbl α))).isValue := by
    intro h; obtain ⟨hv⟩ := h; cases hv
  have hv_unit : ¬ (Exp.rand (.lit (.int z)) (.lit .unit)).isValue := by
    intro h; obtain ⟨hv⟩ := h; cases hv
  rw [primStep_fill hv_lbl, primStep_fill hv_unit]
  suffices h : ProbLang.primStep ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩
      = ProbLang.primStep ⟨.rand (.lit (.int z)) (.lit .unit), σ⟩ by rw [h]
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
  simp only [headStep, _hmem]
  rw [ite_self]

end ProbLang
