module

public import Metrology.ProbLang.DetStep
public import Metrology.ProbLang.Exec
public import Metrology.ProbLang.Syntax.LocallyClosed

@[expose] public section

namespace ProbLang
open Cslib Exp


variable {rT : Type _} [ProbLangℝ rT]

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
def Exp.isClosed (X : ClosedCtx) (e : Exp rT) : Prop := e.IsLocallyClosed ∧ e.fv ⊆ X

theorem Exp.isClosed_weaken {X Y : ClosedCtx} (hXY : X.subset Y)
    {e : Exp α} (h : e.isClosed X) : e.isClosed Y :=
  ⟨h.1, fun _ hz => hXY (h.2 hz)⟩

theorem Exp.isClosed_weaken_empty {X : ClosedCtx} {e : Exp α}
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
abbrev SubstMap (rT : Type _) [ProbLangℝ rT] := List (Var × Exp rT)

namespace SubstMap

def empty : SubstMap rT := []

/-- Insert a (var, value) pair, shadowing any existing binding for the key. -/
def insert (vs : SubstMap rT) (x : Var) (v : Exp rT) : SubstMap rT := (x, v) :: vs

/-- Remove all entries for `x`. -/
def delete (vs : SubstMap rT) (x : Var) : SubstMap rT :=
  vs.filter (fun p => p.1 ≠ x)

/-- Lookup: **rightmost binding wins**, mirroring `Exp.substMap`'s foldr
semantics (the rightmost binding's `subst` is applied first, so its value
becomes the innermost intermediate; under closedness assumptions, outer
substs are no-ops). -/
def lookup : SubstMap rT → Var → Option (Exp rT)
  | [], _ => none
  | (y, v) :: rest, x =>
    match lookup rest x with
    | some w => some w
    | none => if x = y then some v else none

end SubstMap

/-- Apply a substitution map: fold `subst` left-to-right.
    Each pair `(x, v)` replaces free `fvar x` by `v` in the current accumulator. -/
def Exp.substMap (vs : SubstMap rT) (e : Exp rT) : Exp rT :=
  vs.foldr (fun p acc => Exp.subst acc p.1 p.2) e

@[simp] theorem Exp.substMap_empty (e : Exp rT) : e.substMap .empty = e := rfl

@[simp] theorem Exp.substMap_insert (vs : SubstMap rT) (x : Var) (v e : Exp rT) :
    e.substMap (vs.insert x v) = Exp.subst (e.substMap vs) x v := rfl

/-- A substitution that substitutes a single variable. -/
theorem Exp.substMap_singleton (x : Var) (v e : Exp rT) :
    e.substMap [(x, v)] = Exp.subst e x v := rfl

/-! ### Substitution and closedness -/

/-- Substitution of a value with no free variables in `X` preserves closedness in `X`. -/
theorem Exp.subst_isClosed {X : ClosedCtx} {e v : Exp α} {x : Var}
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
theorem Exp.subst_is_closed {e : Exp α} {x : Var} {v : Exp α} {X : ClosedCtx}
    (he : e.isClosed (X.insert x)) (hv : v.isClosed X) :
    (Exp.subst e x v).isClosed X :=
  Exp.subst_isClosed he hv

/-- Substitution of a fully closed value. -/
theorem Exp.subst_is_closed_empty {e : Exp α} {x : Var} {v : Exp α}
    (he : e.isClosed (ClosedCtx.empty.insert x)) (hv : v.isClosed .empty) :
    (Exp.subst e x v).isClosed .empty :=
  Exp.subst_is_closed he hv

/-! ### Commutation of substitutions -/

/-- Substitutions at different variables commute when `v'` has no `x` free. -/
theorem Exp.subst_subst {e v v' : Exp α} {x : Var} {y : Var}
    (hne : x ≠ y) (hv' : x ∉ v'.fv) (_hv'_lc : v'.IsLocallyClosed) :
    Exp.subst (Exp.subst e x v) y v'
      = Exp.subst (Exp.subst e y v') x (Exp.subst v y v') := by
  induction e with
  | fvar z =>
      by_cases h1 : x = z <;> by_cases h2 : y = z
      · subst h1; exact absurd h2 hne.symm
      · subst h1
        simp [Exp.subst, h2]
      · subst h2
        have hv'_fresh : Exp.subst v' x (Exp.subst v y v') = v' :=
          Exp.subst_fresh _ _ _ hv'
        simp [Exp.subst, h1, hv'_fresh]
      · simp [Exp.subst, h1, h2]
  | bvar _ | lit _ | fail | urand => rfl
  | lam e ih | fix e ih | unop _ e ih | fst e ih | snd e ih
  | inl e ih | inr e ih | alloc e ih | load e ih | tape e ih | scrut e _ ih =>
      simp [Exp.subst, ih]
  | app e1 e2 ih1 ih2 | binop _ e1 e2 ih1 ih2 | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2 | rand e1 e2 ih1 ih2 =>
      simp [Exp.subst, ih1, ih2]
  | cond e0 e1 e2 ih0 ih1 ih2 | case e0 e1 e2 ih0 ih1 ih2 =>
      simp [Exp.subst, ih0, ih1, ih2]

/-- Independence of substitutions at distinct, mutually-fresh variables. -/
theorem Exp.subst_subst_ne {e v v' : Exp α} {x y : Var}
    (hne : x ≠ y) (hxv' : x ∉ v'.fv) (hyv : y ∉ v.fv)
    (_hv_lc : v.IsLocallyClosed) (hv'_lc : v'.IsLocallyClosed) :
    Exp.subst (Exp.subst e x v) y v' = Exp.subst (Exp.subst e y v') x v := by
  rw [Exp.subst_subst hne hxv' hv'_lc]
  rw [Exp.subst_fresh y v v' hyv]

/-! ### α-renaming infrastructure

For the Soundness precongruence's binder cases (`lam x` etc.) we need to
transport `bin_log_related_ty` along an atom rename: from related-at-`x`
infer related-at-fresh-`y` after substituting `x ↦ .fvar y`. The core
syntactic ingredient is `subst_subst_fvar_id` below. The substMap-level
commutation `Exp.substMap_subst_fvar_comm` lives further down (after
`SubstMap.AllClosed`'s definition). -/

/-- Two-step substitution where the bridge is a fresh atom: `e[x ↦ y][y ↦ w] = e[x ↦ w]`
when `y` doesn't already appear free in `e` (so the only `y` introduced by the
first step is the one at `x`'s position). -/
theorem Exp.subst_subst_fvar_id (e w : Exp α) (x y : Var) (hyv : y ∉ e.fv) :
    Exp.subst (Exp.subst e x (.fvar y)) y w = Exp.subst e x w := by
  induction e with
  | fvar z =>
    by_cases h1 : x = z
    · subst h1
      simp [Exp.subst]
    · -- z ≠ x, so subst e x (.fvar y) = .fvar z; then subst by y leaves it alone (y ≠ z since y ∉ e.fv).
      have hyz : y ≠ z := fun h => hyv (h ▸ by simp [Exp.fv])
      simp [Exp.subst, h1, hyz]
  | bvar _ | lit _ | fail | urand => rfl
  | lam e ih | fix e ih | unop _ e ih | fst e ih | snd e ih
  | inl e ih | inr e ih | alloc e ih | load e ih | tape e ih | scrut e _ ih =>
    have hyv' : y ∉ e.fv := by
      intro h; exact hyv (by simp [Exp.fv]; exact h)
    simp [Exp.subst, ih hyv']
  | app e1 e2 ih1 ih2 | binop _ e1 e2 ih1 ih2 | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2 | rand e1 e2 ih1 ih2 =>
    have hyv1 : y ∉ e1.fv := fun h => hyv (by simp [Exp.fv]; exact Or.inl h)
    have hyv2 : y ∉ e2.fv := fun h => hyv (by simp [Exp.fv]; exact Or.inr h)
    simp [Exp.subst, ih1 hyv1, ih2 hyv2]
  | cond e0 e1 e2 ih0 ih1 ih2 | case e0 e1 e2 ih0 ih1 ih2 =>
    have hyv0 : y ∉ e0.fv := fun h => hyv (by simp [Exp.fv]; exact Or.inl h)
    have hyv1 : y ∉ e1.fv :=
      fun h => hyv (by simp [Exp.fv]; exact Or.inr (Or.inl h))
    have hyv2 : y ∉ e2.fv :=
      fun h => hyv (by simp [Exp.fv]; exact Or.inr (Or.inr h))
    simp [Exp.subst, ih0 hyv0, ih1 hyv1, ih2 hyv2]

/-! ### Substitution-map-level closedness lemmas

Ports of `SubstMap.deleteB_preserves_closed`, `Exp.substMap_isClosed`,
`Exp.substMap_isClosed_empty`. The original (Binder/String) versions had
to thread the binder-shadowing dance through `deleteB`; under LN there is
no shadowing and the proofs simplify to fold-style induction over the list.

The key invariant is "every value in `vs` is locally-closed and has empty
free-variable set" — i.e., the substitution range consists of fully-closed
values. Under that invariant, `substMap` reduces to repeated `subst`. -/

/-- Predicate: every value bound in the substitution map is fully closed. -/
def SubstMap.AllClosed (vs : SubstMap rT) : Prop :=
  ∀ p ∈ vs, p.2.isClosed .empty

theorem SubstMap.AllClosed_nil : SubstMap.AllClosed ([] : SubstMap rT) := by
  intro p hp; cases hp

theorem SubstMap.AllClosed_cons {x : Var} {v : Exp rT} {vs : SubstMap rT} :
    SubstMap.AllClosed ((x, v) :: vs) ↔ v.isClosed .empty ∧ SubstMap.AllClosed vs := by
  constructor
  · intro h
    refine ⟨h (x, v) (List.mem_cons_self), fun p hp => h p (List.mem_cons_of_mem _ hp)⟩
  · rintro ⟨hv, hvs⟩ p hp
    rcases List.mem_cons.mp hp with rfl | hpm
    · exact hv
    · exact hvs p hpm

theorem SubstMap.AllClosed_delete {vs : SubstMap rT} (x : Var)
    (h : SubstMap.AllClosed vs) : SubstMap.AllClosed (vs.delete x) := by
  intro p hp
  have hmem : p ∈ vs := by
    have := List.mem_filter.mp hp; exact this.1
  exact h p hmem

/-- A filter on an AllClosed substMap is still AllClosed. -/
theorem SubstMap.AllClosed_filter (vs : SubstMap rT) (P : Var × Exp rT → Bool)
    (h : SubstMap.AllClosed vs) :
    SubstMap.AllClosed (vs.filter P) := by
  intro p hp
  have hmem : p ∈ vs := (List.mem_filter.mp hp).1
  exact h p hmem

/-- Filter on a domain-disjoint atom is the identity. -/
theorem SubstMap.filter_notMem_dom (vs : SubstMap rT) {y : Var}
    (h : y ∉ (vs.map (·.1)).toFinset) :
    vs.filter (fun p => !decide (p.1 = y)) = vs := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, w⟩ := p
    have hky : k ≠ y := by intro hk; apply h; rw [hk]; simp
    have hyRest : y ∉ (rest.map (·.1)).toFinset := by
      intro h'; apply h
      simp at h' ⊢; exact Or.inr h'
    have hcond : (!decide ((k, w).1 = y)) = true := by simp [hky]
    simp only [List.filter_cons]
    rw [if_pos hcond]
    congr 1
    exact ih hyRest

/-- The pair returned by `lookup` is the rightmost matching member. -/
theorem SubstMap.mem_of_lookup_eq_some {vs : SubstMap rT} {y : Var} {w : Exp rT}
    (h : vs.lookup y = some w) : (y, w) ∈ vs := by
  induction vs with
  | nil => simp [SubstMap.lookup] at h
  | cons p rest ih =>
    obtain ⟨z, v⟩ := p
    simp only [SubstMap.lookup] at h
    cases hr : SubstMap.lookup rest y with
    | some w' =>
      rw [hr] at h
      have hweq : w' = w := by injection h
      have ihp := ih (by rw [hr, hweq])
      exact List.mem_cons.mpr (.inr ihp)
    | none =>
      rw [hr] at h
      split_ifs at h with hyz
      · subst hyz
        simp at h
        subst h
        exact List.mem_cons.mpr (.inl rfl)

/-- If `y ∈ vs.dom`, then `vs.lookup y` is some. -/
theorem SubstMap.lookup_isSome_of_mem_dom {vs : SubstMap rT} {y : Var}
    (h : y ∈ (vs.map (·.1)).toFinset) : (vs.lookup y).isSome := by
  simp only [List.mem_toFinset, List.mem_map] at h
  obtain ⟨q, hqmem, hqeq⟩ := h
  induction vs with
  | nil => exact absurd hqmem (by simp)
  | cons p rest ih =>
    obtain ⟨z, v⟩ := p
    rcases List.mem_cons.mp hqmem with hp_eq | hpm
    · have hzy : z = y := by
        have : q.1 = y := hqeq
        rw [hp_eq] at this; exact this
      subst hzy
      simp only [SubstMap.lookup]
      cases SubstMap.lookup rest z with
      | some _ => simp
      | none => simp
    · simp only [SubstMap.lookup]
      cases hrr : SubstMap.lookup rest y with
      | some _ => simp
      | none =>
        have hihres := ih hpm
        rw [hrr] at hihres
        cases hihres

/-- `substMap` commutes with `subst _ x (.fvar y)` when both atoms are outside
`vs`'s domain and `vs`'s payloads are fully closed (so don't introduce new fvs). -/
theorem Exp.substMap_subst_fvar_comm
    (vs : SubstMap rT) (E : Exp rT) (x y : Var)
    (hxNotDom : x ∉ (vs.map (·.1)).toFinset)
    (hyNotDom : y ∉ (vs.map (·.1)).toFinset)
    (hvs : SubstMap.AllClosed vs) :
    Exp.substMap vs (Exp.subst E x (.fvar y))
      = Exp.subst (Exp.substMap vs E) x (.fvar y) := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨z, w⟩ := p
    have hzx : z ≠ x := fun h => hxNotDom (h ▸ by simp)
    have hzy : z ≠ y := fun h => hyNotDom (h ▸ by simp)
    have hxNotRest : x ∉ (rest.map (·.1)).toFinset := by
      intro h
      apply hxNotDom
      simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert]
      exact Or.inr h
    have hyNotRest : y ∉ (rest.map (·.1)).toFinset := by
      intro h
      apply hyNotDom
      simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert]
      exact Or.inr h
    have hw_closed : w.isClosed .empty := (SubstMap.AllClosed_cons.mp hvs).1
    have hw_lc : w.IsLocallyClosed := hw_closed.1
    have hxNotW : x ∉ w.fv := fun h => by
      have := hw_closed.2 h; simp [ClosedCtx.empty] at this
    have hvs_rest : SubstMap.AllClosed rest := (SubstMap.AllClosed_cons.mp hvs).2
    -- substMap (cons (z,w) rest) F = subst (substMap rest F) z w (foldr).
    have hcons1 : Exp.substMap ((z, w) :: rest) (Exp.subst E x (.fvar y))
        = Exp.subst (Exp.substMap rest (Exp.subst E x (.fvar y))) z w := rfl
    have hcons2 : Exp.substMap ((z, w) :: rest) E
        = Exp.subst (Exp.substMap rest E) z w := rfl
    rw [hcons1, hcons2, ih hxNotRest hyNotRest hvs_rest]
    -- Use subst_subst_ne to swap (subst _ x (.fvar y)) and (subst _ z w):
    -- subst_subst_ne with x := z, y := x, v := w, v' := .fvar y.
    have hzNotFvY : z ∉ (Exp.fvar (rT := rT) y).fv := by
      simp only [Exp.fv, Finset.mem_singleton]; exact hzy
    have hsw := Exp.subst_subst_ne (e := Exp.substMap rest E)
      (v := w) (v' := Exp.fvar (rT := rT) y) (x := z) (y := x)
      hzx hzNotFvY hxNotW hw_lc (Exp.IsLocallyClosed.fvar y)
    rw [← hsw]

/-- `substMap` through a closed expression is a no-op (Clutch's
`Exp.substMap_isClosed` for the empty `X = ∅` case). -/
theorem Exp.substMap_isClosed_empty {e : Exp rT} (vs : SubstMap rT)
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
theorem Exp.substMap_isClosed {X : ClosedCtx} {e : Exp rT} (vs : SubstMap rT)
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

@[simp] theorem Exp.substMap_cons (p : Var × Exp rT) (vs : SubstMap rT) (e : Exp rT) :
    e.substMap (p :: vs) = Exp.subst (e.substMap vs) p.1 p.2 := rfl

/-! ### `substMap` distributivity over expression constructors

These let `simp` push `Exp.substMap vs` through every constructor of `Exp rT`,
mirroring the recursive structure of `Exp.subst`. Each lemma is one
`induction vs` on the substitution list. They are critical for the
`Fundamental.lean` lemmas, which need to commute `substMap vs` with the
relational expression constructors before invoking the corresponding
`refines_*` compatibility rule. -/

@[simp] theorem Exp.substMap_lit (vs : SubstMap rT) (b : BaseLit rT) :
    (Exp.lit b).substMap vs = .lit b := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_bvar (vs : SubstMap rT) (j : Nat) :
    (Exp.bvar j).substMap vs = .bvar j := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_fail (vs : SubstMap rT) :
    Exp.fail.substMap vs = .fail := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_urand (vs : SubstMap rT) :
    Exp.urand.substMap vs = .urand := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_pair (vs : SubstMap rT) (e1 e2 : Exp rT) :
    (Exp.pair e1 e2).substMap vs = .pair (e1.substMap vs) (e2.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_fst (vs : SubstMap rT) (e : Exp rT) :
    (Exp.fst e).substMap vs = .fst (e.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_snd (vs : SubstMap rT) (e : Exp rT) :
    (Exp.snd e).substMap vs = .snd (e.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_inl (vs : SubstMap rT) (e : Exp rT) :
    (Exp.inl e).substMap vs = .inl (e.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_inr (vs : SubstMap rT) (e : Exp rT) :
    (Exp.inr e).substMap vs = .inr (e.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_case (vs : SubstMap rT) (e0 e1 e2 : Exp rT) :
    (Exp.case e0 e1 e2).substMap vs =
      .case (e0.substMap vs) (e1.substMap vs) (e2.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_cond (vs : SubstMap rT) (e0 e1 e2 : Exp rT) :
    (Exp.cond e0 e1 e2).substMap vs =
      .cond (e0.substMap vs) (e1.substMap vs) (e2.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_app (vs : SubstMap rT) (e1 e2 : Exp rT) :
    (Exp.app e1 e2).substMap vs = .app (e1.substMap vs) (e2.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_lam (vs : SubstMap rT) (e : Exp rT) :
    (Exp.lam e).substMap vs = .lam (e.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_fix (vs : SubstMap rT) (e : Exp rT) :
    (Exp.fix e).substMap vs = .fix (e.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_unop (vs : SubstMap rT) (op : UnOp) (e : Exp rT) :
    (Exp.unop op e).substMap vs = .unop op (e.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_binop (vs : SubstMap rT) (op : BinOp) (e1 e2 : Exp rT) :
    (Exp.binop op e1 e2).substMap vs =
      .binop op (e1.substMap vs) (e2.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_alloc (vs : SubstMap rT) (e : Exp rT) :
    (Exp.alloc e).substMap vs = .alloc (e.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_load (vs : SubstMap rT) (e : Exp rT) :
    (Exp.load e).substMap vs = .load (e.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_store (vs : SubstMap rT) (e1 e2 : Exp rT) :
    (Exp.store e1 e2).substMap vs = .store (e1.substMap vs) (e2.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_tape (vs : SubstMap rT) (e : Exp rT) :
    (Exp.tape e).substMap vs = .tape (e.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_rand (vs : SubstMap rT) (e1 e2 : Exp rT) :
    (Exp.rand e1 e2).substMap vs = .rand (e1.substMap vs) (e2.substMap vs) := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

@[simp] theorem Exp.substMap_scrut (vs : SubstMap rT) (e : Exp rT) (p : Pat rT) :
    (Exp.scrut e p).substMap vs = .scrut (e.substMap vs) p := by
  induction vs with
  | nil => rfl
  | cons _ _ ih => rw [Exp.substMap_cons, ih]; simp [Exp.subst]

/-- `substMap` distributes over `openRec` when all bindings are LC. The key
binder-substitution lemma: `substMap vs (openRec k u e) = openRec k (substMap vs u) (substMap vs e)`. -/
theorem Exp.substMap_openRec (vs : SubstMap rT) (k : Nat) (u e : Exp rT)
    (hClosed : SubstMap.AllClosed vs) :
    Exp.substMap vs (Exp.openRec k u e) =
      Exp.openRec k (Exp.substMap vs u) (Exp.substMap vs e) := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨y, w⟩ := p
    rw [SubstMap.AllClosed_cons] at hClosed
    obtain ⟨hwClosed, hRestClosed⟩ := hClosed
    rw [Exp.substMap_cons, ih hRestClosed, Exp.substMap_cons, Exp.substMap_cons]
    -- subst (openRec k (substMap rest u) (substMap rest e)) y w
    --  = openRec k (subst (substMap rest u) y w) (subst (substMap rest e) y w)
    exact Exp.subst_openRec y w k _ _ hwClosed.1

/-- `substMap` distributes over `open'`. -/
theorem Exp.substMap_open (vs : SubstMap rT) (u e : Exp rT)
    (hClosed : SubstMap.AllClosed vs) :
    Exp.substMap vs (Exp.open' e u) =
      Exp.open' (Exp.substMap vs e) (Exp.substMap vs u) :=
  Exp.substMap_openRec vs 0 u e hClosed

/-- If `x ∉ e.fv` and `vs` is closed, then `x ∉ (substMap vs e).fv`.
A closed substMap can only remove free vars, not introduce new ones. -/
theorem Exp.notFv_substMap {vs : SubstMap rT} {e : Exp rT} {x : Var}
    (hClosed : SubstMap.AllClosed vs) (hx : x ∉ e.fv) :
    x ∉ (Exp.substMap vs e).fv := by
  induction vs with
  | nil => exact hx
  | cons p rest ih =>
    obtain ⟨y, w⟩ := p
    rw [SubstMap.AllClosed_cons] at hClosed
    obtain ⟨hwClosed, hRestClosed⟩ := hClosed
    rw [Exp.substMap_cons]
    -- Goal: x ∉ (subst (substMap rest e) y w).fv
    -- subst y w doesn't introduce new free vars beyond fv(prev) ∪ fv(w).
    -- fv(w) = ∅ (since w is closed).
    have hxRest : x ∉ (substMap rest e).fv := ih hRestClosed
    intro hmem
    -- (subst e' y w).fv ⊆ (e'.fv \ {y}) ∪ w.fv
    have := fv_subst_subset (substMap rest e) y w hmem
    rcases Finset.mem_union.mp this with h1 | h2
    · exact hxRest (Finset.mem_sdiff.mp h1).1
    · -- w is closed, so x ∉ w.fv
      have : w.fv = ∅ := by
        have := hwClosed.2
        ext z
        simp only [Finset.notMem_empty, iff_false]
        intro hzw
        have := this hzw
        simp [ClosedCtx.empty] at this
      rw [this] at h2
      exact (Finset.notMem_empty _ h2)

/-- Helper: when `x` is unbound in `vs`, `substMap` is a no-op on `.fvar x`. -/
theorem Exp.substMap_fvar_lookup_none {vs : SubstMap rT} {x : Var}
    (hv : SubstMap.lookup vs x = none) :
    Exp.substMap vs (.fvar x) = .fvar x := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨y, w⟩ := p
    simp only [SubstMap.lookup] at hv
    cases hr : SubstMap.lookup rest x with
    | some w' => rw [hr] at hv; cases hv
    | none =>
      rw [hr] at hv
      simp only at hv
      split_ifs at hv with hxy
      rw [Exp.substMap_cons, ih hr]
      show (Exp.fvar x).subst y w = .fvar x
      simp only [Exp.subst]
      have : ¬ y = x := fun h => hxy h.symm
      rw [if_neg this]

/-- Closedness of looked-up values in an `AllClosed` SubstMap. -/
theorem SubstMap.lookup_closed {vs : SubstMap rT} {x : Var} {v : Exp rT}
    (hv : SubstMap.lookup vs x = some v) (hClosed : SubstMap.AllClosed vs) :
    v.isClosed .empty := by
  induction vs with
  | nil => simp [SubstMap.lookup] at hv
  | cons p rest ih =>
    obtain ⟨y, w⟩ := p
    rw [SubstMap.AllClosed_cons] at hClosed
    simp only [SubstMap.lookup] at hv
    cases hr : SubstMap.lookup rest x with
    | some w' =>
      rw [hr] at hv; injection hv with hw'v; subst hw'v
      exact ih hr hClosed.2
    | none =>
      rw [hr] at hv
      simp only at hv
      split_ifs at hv with hxy
      injection hv with hwv; subst hwv
      exact hClosed.1

/-- Bridge for binder-shifting in fundamental's `lam`/`fix`/`tlam`/`unpack`.
After picking a fresh atom `x` and specializing the IH at vs' = (x, v) :: vs,
the substMap of an opened body `open' e (.fvar x)` simplifies to `open' (substMap vs e) v`. -/
theorem Exp.substMap_open_fresh {vs : SubstMap rT} {e v : Exp rT} {x : Var}
    (hClosed : SubstMap.AllClosed vs) (hxFv : x ∉ e.fv)
    (hxDom : SubstMap.lookup vs x = none) (hvLC : v.IsLocallyClosed) :
    Exp.substMap ((x, v) :: vs) (Exp.open' e (.fvar x)) =
      Exp.open' (Exp.substMap vs e) v := by
  show Exp.subst (Exp.substMap vs (Exp.open' e (.fvar x))) x v =
    Exp.open' (Exp.substMap vs e) v
  rw [Exp.substMap_open _ _ _ hClosed]
  rw [Exp.substMap_fvar_lookup_none hxDom]
  have hxFv' : x ∉ (Exp.substMap vs e).fv := Exp.notFv_substMap hClosed hxFv
  rw [Exp.subst_intro x v _ hxFv' hvLC]

/-- `substMap` preserves local closedness when all bindings are LC. -/
theorem Exp.substMap_lc {vs : SubstMap rT} {e : Exp rT}
    (hClosed : SubstMap.AllClosed vs) (he : e.IsLocallyClosed) :
    (Exp.substMap vs e).IsLocallyClosed := by
  induction vs with
  | nil => exact he
  | cons p rest ih =>
    obtain ⟨y, w⟩ := p
    rw [SubstMap.AllClosed_cons] at hClosed
    obtain ⟨hwClosed, hRestClosed⟩ := hClosed
    rw [Exp.substMap_cons]
    exact subst_lc (ih hRestClosed) hwClosed.1

/-- A free variable of `(substMap vs e)` either was already free in `e` (and
not substituted out), or comes from one of the substituted values. -/
theorem Exp.fv_substMap_subset (vs : SubstMap rT) (e : Exp rT) :
    (Exp.substMap vs e).fv ⊆
      e.fv ∪ ((vs.map (·.2)).foldr (fun w acc => w.fv ∪ acc) ∅) := by
  induction vs generalizing e with
  | nil => simp [Exp.substMap]
  | cons p rest ih =>
    obtain ⟨z, w⟩ := p
    rw [Exp.substMap_cons]
    -- Goal: (subst (substMap rest e) z w).fv ⊆ e.fv ∪ ((w.fv ∪ rest_w_fv) ∪ acc).
    intro y hy
    have h1 := fv_subst_subset (substMap rest e) z w hy
    rcases Finset.mem_union.mp h1 with hL | hR
    · -- y ∈ (substMap rest e).fv \ {z} ⊆ (substMap rest e).fv ⊆ e.fv ∪ rest_w_fv.
      have hyRest : y ∈ (substMap rest e).fv := (Finset.mem_sdiff.mp hL).1
      have hih : y ∈ e.fv ∪ ((rest.map (·.2)).foldr (fun w acc => w.fv ∪ acc) ∅) := by
        exact (ih (e := e)) hyRest
      simp only [List.map_cons, List.foldr_cons, Finset.mem_union]
      rcases Finset.mem_union.mp hih with h_e | h_rest
      · exact .inl h_e
      · exact .inr (.inr h_rest)
    · -- y ∈ w.fv. Goal: in the rhs.
      simp only [List.map_cons, List.foldr_cons, Finset.mem_union]
      exact .inr (.inl hR)

/-- Closed-bindings have no free variables (combined). -/
theorem SubstMap.allClosed_values_fv_empty {vs : SubstMap rT}
    (hClosed : SubstMap.AllClosed vs) :
    ((vs.map (·.2)).foldr (fun w acc => w.fv ∪ acc) ∅) = ∅ := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨z, w⟩ := p
    rw [SubstMap.AllClosed_cons] at hClosed
    obtain ⟨hwClosed, hRestClosed⟩ := hClosed
    simp only [List.map_cons, List.foldr_cons]
    rw [ih hRestClosed]
    have hwfv : w.fv = ∅ := by
      ext z'
      simp only [Finset.notMem_empty, iff_false]
      intro hz'
      have := hwClosed.2 hz'
      simp [ClosedCtx.empty] at this
    rw [hwfv]
    simp

/-- Stronger: `(substMap vs e).fv ⊆ e.fv \ vs.dom` when `vs` is closed.
i.e., a closed substMap removes exactly the `vs.dom`-variables. -/
theorem Exp.fv_substMap_sdiff_dom {vs : SubstMap rT} {e : Exp rT}
    (hClosed : SubstMap.AllClosed vs) :
    (Exp.substMap vs e).fv ⊆ e.fv \ (vs.map (·.1)).toFinset := by
  induction vs generalizing e with
  | nil =>
    simp [Exp.substMap]
  | cons p rest ih =>
    obtain ⟨z, w⟩ := p
    rw [SubstMap.AllClosed_cons] at hClosed
    obtain ⟨hwClosed, hRestClosed⟩ := hClosed
    rw [Exp.substMap_cons]
    intro y hy
    -- hy : y ∈ (subst (substMap rest e) z w).fv.
    -- (subst e' z w).fv ⊆ (e'.fv \ {z}) ∪ w.fv. w.fv = ∅.
    have h1 := fv_subst_subset (substMap rest e) z w hy
    rcases Finset.mem_union.mp h1 with hL | hR
    · -- y ∈ (substMap rest e).fv \ {z}.
      have hyRest : y ∈ (substMap rest e).fv := (Finset.mem_sdiff.mp hL).1
      have hyNeZ : y ∉ ({z} : Finset Var) := (Finset.mem_sdiff.mp hL).2
      have hih : y ∈ e.fv \ (rest.map (·.1)).toFinset := (ih (e := e) hRestClosed) hyRest
      simp only [Finset.mem_sdiff, List.map_cons, List.toFinset_cons, Finset.mem_insert,
        not_or]
      have hyDecomp := Finset.mem_sdiff.mp hih
      refine ⟨hyDecomp.1, ?_, hyDecomp.2⟩
      intro h; exact hyNeZ (by simp [h])
    · -- y ∈ w.fv. But w is closed, so w.fv = ∅. Contradiction.
      have hwfv : w.fv = ∅ := by
        ext z'
        simp only [Finset.notMem_empty, iff_false]
        intro hz'
        have := hwClosed.2 hz'
        simp [ClosedCtx.empty] at this
      rw [hwfv] at hR
      exact (Finset.notMem_empty _ hR).elim

/-- If `e.fv ⊆ dom(vs)` and `vs` is closed, then `(substMap vs e).fv = ∅`. -/
theorem Exp.substMap_fv_eq_empty {vs : SubstMap rT} {e : Exp rT}
    (hClosed : SubstMap.AllClosed vs)
    (hsub : e.fv ⊆ (vs.map (·.1)).toFinset) :
    (Exp.substMap vs e).fv = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro y hy
  have h := Exp.fv_substMap_sdiff_dom hClosed (e := e) hy
  have h' := Finset.mem_sdiff.mp h
  exact h'.2 (hsub h'.1)

/-- The α-renaming key equation: when `vs` maps `y` to `w` and `x` is fresh,
`substMap vs (subst E x (.fvar y)) = subst (substMap (vs without y) E) x w`. -/
theorem Exp.substMap_subst_fvar_lookup
    (vs : SubstMap rT) (E : Exp rT) (x y : Var) (w : Exp rT)
    (_hxy : x ≠ y)
    (hxNotDom : x ∉ (vs.map (·.1)).toFinset)
    (hvs : SubstMap.AllClosed vs)
    (hyLookup : vs.lookup y = some w)
    (hyFvE : y ∉ E.fv) :
    Exp.substMap vs (Exp.subst E x (.fvar y))
      = Exp.subst (Exp.substMap (vs.filter (fun p => !decide (p.1 = y))) E) x w := by
  have hw_closed : w.isClosed .empty :=
    hvs (y, w) (SubstMap.mem_of_lookup_eq_some hyLookup)
  have hw_lc : w.IsLocallyClosed := hw_closed.1
  have hxNotW : x ∉ w.fv := fun h => by
    have := hw_closed.2 h; simp [ClosedCtx.empty] at this
  have hyNotW : y ∉ w.fv := fun h => by
    have := hw_closed.2 h; simp [ClosedCtx.empty] at this
  induction vs with
  | nil => simp [SubstMap.lookup] at hyLookup
  | cons p rest ih =>
    obtain ⟨z, v⟩ := p
    have hcons1 : Exp.substMap ((z, v) :: rest) (Exp.subst E x (.fvar y))
        = Exp.subst (Exp.substMap rest (Exp.subst E x (.fvar y))) z v := rfl
    have hzx : z ≠ x := fun h => hxNotDom (h ▸ by simp)
    have hxNotRest : x ∉ (rest.map (·.1)).toFinset := by
      intro h
      apply hxNotDom
      simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert]
      exact Or.inr h
    have hv_closed : v.isClosed .empty := (SubstMap.AllClosed_cons.mp hvs).1
    have hv_lc : v.IsLocallyClosed := hv_closed.1
    have hxNotV : x ∉ v.fv := fun h => by
      have := hv_closed.2 h; simp [ClosedCtx.empty] at this
    have hvs_rest : SubstMap.AllClosed rest := (SubstMap.AllClosed_cons.mp hvs).2
    rw [hcons1]
    by_cases hzy : z = y
    · simp only [hzy, SubstMap.lookup] at hyLookup
      cases hr : SubstMap.lookup rest y with
      | some w' =>
        rw [hr] at hyLookup
        have hw'eq : w' = w := by injection hyLookup
        rw [hw'eq] at hr
        rw [ih hxNotRest hvs_rest hr]
        have hfilter_cons :
            ((z, v) :: rest).filter (fun p => !decide (p.1 = y))
              = rest.filter (fun p => !decide (p.1 = y)) := by
          show List.filter _ _ = List.filter _ _
          rw [List.filter_cons]
          have : (!decide ((z, v).1 = y)) = false := by simp [hzy]
          rw [if_neg (by rw [this]; simp)]
        rw [hfilter_cons]
        rw [hzy]
        have hfilter_closed : SubstMap.AllClosed (rest.filter (fun p => !decide (p.1 = y))) :=
          SubstMap.AllClosed_filter rest _ hvs_rest
        have hyNotFinner : y ∉ (Exp.substMap (rest.filter (fun p => !decide (p.1 = y))) E).fv :=
          Exp.notFv_substMap hfilter_closed hyFvE
        have hyNotFsubst : y ∉ (Exp.subst (Exp.substMap (rest.filter (fun p => !decide (p.1 = y))) E) x w).fv := by
          intro hy
          have := Exp.fv_subst_subset _ x w hy
          rcases Finset.mem_union.mp this with h1 | h2
          · exact hyNotFinner (Finset.mem_sdiff.mp h1).1
          · exact hyNotW h2
        rw [Exp.subst_fresh y _ v hyNotFsubst]
      | none =>
        rw [hr] at hyLookup
        simp at hyLookup
        subst hyLookup
        have hfilter_cons :
            ((z, v) :: rest).filter (fun p => !decide (p.1 = y))
              = rest.filter (fun p => !decide (p.1 = y)) := by
          show List.filter _ _ = List.filter _ _
          rw [List.filter_cons]
          have : (!decide ((z, v).1 = y)) = false := by simp [hzy]
          rw [if_neg (by rw [this]; simp)]
        rw [hfilter_cons]
        have hyNotRest : y ∉ (rest.map (·.1)).toFinset := by
          intro h
          have := SubstMap.lookup_isSome_of_mem_dom h
          rw [hr] at this
          cases this
        have hcomm := Exp.substMap_subst_fvar_comm rest E x y hxNotRest hyNotRest hvs_rest
        rw [hcomm]
        have hyNotInner : y ∉ (Exp.substMap rest E).fv :=
          Exp.notFv_substMap hvs_rest hyFvE
        rw [SubstMap.filter_notMem_dom rest hyNotRest, hzy]
        exact Exp.subst_subst_fvar_id (Exp.substMap rest E) v x y hyNotInner
    · simp only [SubstMap.lookup] at hyLookup
      cases hr : SubstMap.lookup rest y with
      | some w' =>
        rw [hr] at hyLookup
        have hw'eq : w' = w := by injection hyLookup
        rw [hw'eq] at hr
        rw [ih hxNotRest hvs_rest hr]
        have hfilter_cons :
            ((z, v) :: rest).filter (fun p => !decide (p.1 = y))
              = (z, v) :: rest.filter (fun p => !decide (p.1 = y)) := by
          show List.filter _ _ = _
          rw [List.filter_cons]
          have : (!decide ((z, v).1 = y)) = true := by simp [hzy]
          rw [if_pos this]
        rw [hfilter_cons]
        have hxz : x ≠ z := fun h => hzx h.symm
        have hzNotW : z ∉ w.fv := fun h => by
          have := hw_closed.2 h; simp [ClosedCtx.empty] at this
        have hsw := Exp.subst_subst_ne
          (e := Exp.substMap (rest.filter (fun p => !decide (p.1 = y))) E)
          (v := w) (v' := v) (x := x) (y := z)
          hxz hxNotV hzNotW hw_lc hv_lc
        rw [hsw]
        rfl
      | none =>
        rw [hr] at hyLookup
        simp [Ne.symm hzy] at hyLookup

/-- `substMap` on `fvar x` looks up the rightmost binding for `x`, provided
all bindings are closed expressions. -/
theorem Exp.substMap_fvar_lookup_some (vs : SubstMap rT) (x : Var)
    (hClosed : SubstMap.AllClosed vs) :
    ∀ {v : Exp rT}, SubstMap.lookup vs x = some v → Exp.substMap vs (.fvar x) = v := by
  induction vs with
  | nil => intro v hv; simp [SubstMap.lookup] at hv
  | cons p rest ih =>
    intro v hv
    obtain ⟨y, w⟩ := p
    rw [SubstMap.AllClosed_cons] at hClosed
    obtain ⟨hwClosed, hRestClosed⟩ := hClosed
    rw [Exp.substMap_cons]
    simp only [SubstMap.lookup] at hv
    cases hr : SubstMap.lookup rest x with
    | some w' =>
      rw [hr] at hv; injection hv with hw'v; subst hw'v
      rw [ih hRestClosed hr]
      have hw'Closed := SubstMap.lookup_closed hr hRestClosed
      show w'.subst y w = w'
      apply Exp.subst_fresh
      intro hmem
      have := hw'Closed.2 hmem
      simp [ClosedCtx.empty] at this
    | none =>
      rw [hr] at hv
      simp only at hv
      split_ifs at hv with hxy
      injection hv with hwv; subst hwv; subst hxy
      rw [Exp.substMap_fvar_lookup_none hr]
      show (Exp.fvar x).subst x w = w
      simp [Exp.subst]

/-! ## Group D — Deterministic / probabilistic head-step characterization

Predicate-based step classification (Clutch's `metatheory.v` ~1448–1713,
minus Laplace/Tick). The `HeadStepSupport` relation lives in `HeadStep.lean`. -/

/-- Expressions that take a single deterministic head step in state `σ`. -/
inductive DetHeadStepPred : Exp rT → State rT → Prop
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
inductive ProbHeadStepPred : Exp rT → State rT → Prop
  | randNoTape {z σ} : 0 < z →
      ProbHeadStepPred (.rand (.lit (.int z)) (.lit .unit)) σ
  | randTape {z α σ N nn ns} : σ.tapes[α]? = some ⟨N, nn :: ns⟩ → z = N →
      ProbHeadStepPred (.rand (.lit (.int z)) (.lit (.lbl α))) σ
  | randTapeEmpty {z α σ N} : 0 < z → σ.tapes[α]? = some ⟨N, []⟩ → z = N →
      ProbHeadStepPred (.rand (.lit (.int z)) (.lit (.lbl α))) σ
  | randTapeOther {z α σ N L} : 0 < z → σ.tapes[α]? = some ⟨N, L⟩ → z ≠ N →
      ProbHeadStepPred (.rand (.lit (.int z)) (.lit (.lbl α))) σ
  | randNonpos {z σ} : ¬ 0 < z →
      ProbHeadStepPred (.rand (.lit (.int z)) (.lit .unit)) σ
  | randTapeNonposEmpty {z α σ N} : ¬ 0 < z → σ.tapes[α]? = some ⟨N, []⟩ → z = N →
      ProbHeadStepPred (.rand (.lit (.int z)) (.lit (.lbl α))) σ
  | randTapeNonposOther {z α σ N L} : ¬ 0 < z → σ.tapes[α]? = some ⟨N, L⟩ → z ≠ N →
      ProbHeadStepPred (.rand (.lit (.int z)) (.lit (.lbl α))) σ
  | urand {σ} : ProbHeadStepPred Exp.urand σ

/-- Either a deterministic or a probabilistic head step is taken. -/
def HeadStepPred (e : Exp rT) (σ : State rT) : Prop :=
  DetHeadStepPred e σ ∨ ProbHeadStepPred e σ

/-- Boolean test for determinism of a head step. -/
def isDetHeadStep (e : Exp rT) (σ : State rT) : Bool :=
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
theorem val_not_HeadStepPred {e : Exp rT} {σ : State rT}
    (hv : e.isValue) : ¬ HeadStepPred e σ := by
  rw [Exp.isValue_iff_isValueR] at hv
  rintro (hdet | hprob)
  · cases hdet <;> simp [Exp.isValueR] at hv
  · cases hprob <;> simp [Exp.isValueR] at hv

/-- `isDetHeadStep ↔ DetHeadStepPred`. -/
theorem isDetHeadStep_iff_pred (e : Exp rT) (σ : State rT) :
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

theorem HeadStepPred_iff_exists_support (e : Exp rT) (σ : State rT) :
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
      | randTape htape hzN =>
          exact ⟨_, .RandTapeS htape hzN rfl rfl⟩
      | randTapeEmpty hz htape hzN =>
          exact ⟨_, .RandTapeEmptyS hz htape hzN (le_refl 0) hz rfl⟩
      | randTapeOther hz htape hzN =>
          exact ⟨_, .RandTapeOtherS hz htape hzN (le_refl 0) hz rfl⟩
      | randNonpos hz => exact ⟨_, .RandNonposS hz⟩
      | randTapeNonposEmpty hz htape hzN =>
          exact ⟨_, .RandTapeNonposEmptyS hz htape hzN⟩
      | randTapeNonposOther hz htape hzN =>
          exact ⟨_, .RandTapeNonposOtherS hz htape hzN⟩
      | urand =>
          obtain ⟨r, hr⟩ := ProbLangℝ.unifUnitSupport_nonempty rT
          exact ⟨_, .UrandS (r := r) hr⟩
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
    | RandTapeS htape hzN _ _ => exact .inr (.randTape htape hzN)
    | RandTapeEmptyS hz htape hzN _ _ _ => exact .inr (.randTapeEmpty hz htape hzN)
    | RandTapeOtherS hz htape hzN _ _ _ => exact .inr (.randTapeOther hz htape hzN)
    | RandNonposS hz => exact .inr (.randNonpos hz)
    | RandTapeNonposEmptyS hz htape hzN => exact .inr (.randTapeNonposEmpty hz htape hzN)
    | RandTapeNonposOtherS hz htape hzN => exact .inr (.randTapeNonposOther hz htape hzN)
    | UrandS _ => exact .inr .urand

theorem not_HeadStepPred_iff_zero [MeasurableSingletonClass rT]
    (e : Exp rT) (σ : State rT) :
    ¬ HeadStepPred e σ ↔ headStep ⟨e, σ⟩ = 0 := by
  rw [HeadStepPred_iff_exists_support]
  constructor
  · -- No support point ⇒ `headStep` is zero. Countability-free via the
    -- structural atomicity lemma `headStep_exists_support_of_ne_zero`.
    intro hns
    by_contra h0
    exact hns (headStep_exists_support_of_ne_zero h0)
  · -- A support point witnesses `headStep ≠ 0` directly.
    rintro h0 ⟨ρ', hsupp⟩
    exact HeadStepSupport.ne_zero hsupp h0

theorem det_or_prob_or_zero [MeasurableSingletonClass rT]
    (e : Exp rT) (σ : State rT) :
    DetHeadStepPred e σ ∨ ProbHeadStepPred e σ ∨ headStep ⟨e, σ⟩ = 0 := by
  by_cases hpred : HeadStepPred e σ
  · rcases hpred with hdet | hprob
    · exact .inl hdet
    · exact .inr (.inl hprob)
  · exact .inr (.inr ((not_HeadStepPred_iff_zero e σ).mp hpred))

/-! ## Group E — Tape and fresh-location update lemmas -/

theorem State.upd_tape_some (σ : State α) (α : Loc) (t : Tape) :
    (σ.update_tapes (·.insert α t)).tapes[α]? = some t := by
  simp [State.update_tapes]

theorem State.upd_diff_tape_comm {σ : State α} {α β : Loc} {bs bs' : Tape}
    (hne : α ≠ β) :
    ((σ.update_tapes (·.insert β bs)).update_tapes (·.insert α bs'))
      = ((σ.update_tapes (·.insert α bs')).update_tapes (·.insert β bs)) := by
  unfold State.update_tapes
  congr 2
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

theorem State.upd_diff_tape_tot {σ : State α} {α β : Loc} {bs : Tape}
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

theorem State.fresh_loc_upd_some {σ : State α} {α : Loc} {bs bs' : Tape}
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

theorem State.fresh_loc_upd_swap {σ : State β} {α : Loc} {bs bs' : Tape} {t : Tape}
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

theorem State.fresh_loc_lookup {σ : State α} {α : Loc} {bs : Tape} {t : Tape}
    (h : σ.tapes[α]? = some bs) :
    (σ.tapes.insert σ.tapes.fresh t)[α]? = some bs := by
  have hne : σ.tapes.fresh ≠ α := Std.ExtTreeMap.elem_fresh_ne h
  rw [Std.ExtTreeMap.getElem?_insert]
  have hcmp : compare σ.tapes.fresh α ≠ .eq := by
    simp [compare, compareOfLessAndEq]
    split <;> simp_all
  simp [hcmp, h]

theorem Cfg.uniform_nonpos_eq {z : Int} {σ : State rT} (hz : ¬ 0 < z) :
    Cfg.uniform z σ = MeasureTheory.Measure.dirac ⟨.lit (.int (-1)), σ⟩ := by
  unfold Cfg.uniform Int.isPos
  rw [dif_neg hz]

theorem Cfg.uniform_ne_zero
    (z : Int) (σ : State rT) : Cfg.uniform z σ ≠ 0 := by
  intro heq
  have hp : MeasureTheory.IsProbabilityMeasure (Cfg.uniform z σ) :=
    Cfg.uniform_isProbabilityMeasure
  have := hp.measure_univ; rw [heq] at this; simp at this

/-- Integrate a function over `Cfg.uniform z σ`: the result is the uniform
average over `n ∈ Ico 0 z` of `φ ⟨#n, σ⟩`. -/
theorem Cfg.lintegral_uniform [Countable rT] [MeasurableSingletonClass rT]
    {z : Int} (Hz : 0 < z) (σ : State rT) (φ : Cfg rT → ENNReal) :
    ∫⁻ c, φ c ∂(Cfg.uniform z σ) =
      ((z.toNat : ENNReal)⁻¹) * ∑ n ∈ Finset.Ico (0 : Int) z,
        φ (⟨.lit (.int n), σ⟩ : Cfg rT) := by
  classical
  have Huniform : Cfg.uniform z σ =
      ((PMF.uniformOfFinset (Finset.Ico (0 : Int) z)
          (Finset.nonempty_Ico.mpr Hz)).toMeasure).map
        (fun n : Int => (⟨.lit (.int n), σ⟩ : Cfg rT)) := by
    unfold Cfg.uniform Int.isPos
    simp only [Hz, dite_true]
  rw [Huniform,
      MeasureTheory.lintegral_map (Measurable.of_discrete) Measurable.of_discrete]
  rw [MeasureTheory.lintegral_countable']
  have hcard : (Finset.Ico (0 : Int) z).card = z.toNat := by
    rw [Int.card_Ico]
    omega
  have hpmf_mem : ∀ n ∈ Finset.Ico (0 : Int) z,
      ((PMF.uniformOfFinset (Finset.Ico (0 : Int) z) (Finset.nonempty_Ico.mpr Hz)).toMeasure)
        {n} = ((z.toNat : ENNReal)⁻¹) := by
    intro n hn
    rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
        PMF.uniformOfFinset_apply_of_mem _ hn, hcard]
  have hpmf_notmem : ∀ n ∉ Finset.Ico (0 : Int) z,
      ((PMF.uniformOfFinset (Finset.Ico (0 : Int) z) (Finset.nonempty_Ico.mpr Hz)).toMeasure)
        {n} = 0 := by
    intro n hn
    rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
        PMF.uniformOfFinset_apply_of_notMem _ hn]
  have htsum : ∑' n : Int, φ (⟨.lit (.int n), σ⟩ : Cfg rT) *
      ((PMF.uniformOfFinset (Finset.Ico (0 : Int) z) (Finset.nonempty_Ico.mpr Hz)).toMeasure)
        {n}
      = ∑ n ∈ Finset.Ico (0 : Int) z,
          φ (⟨.lit (.int n), σ⟩ : Cfg rT) * ((z.toNat : ENNReal)⁻¹) := by
    rw [tsum_eq_sum (s := Finset.Ico (0 : Int) z) ?_]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [hpmf_mem n hn]
    · intro n hn
      rw [hpmf_notmem n hn, mul_zero]
  rw [htsum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem Cfg.uniform_one_eq_dirac [Countable rT] [MeasurableSingletonClass rT]
    (σ : State rT) :
    Cfg.uniform 1 σ = MeasureTheory.Measure.dirac (⟨.lit (.int 0), σ⟩ : Cfg rT) := by
  classical
  unfold Cfg.uniform Int.isPos
  simp only [show (0 : Int) < 1 from Int.one_pos, dite_true]
  have hico : Finset.Ico (0 : Int) 1 = {0} := by
    ext x; simp [Finset.mem_Ico]; omega
  refine MeasureTheory.Measure.ext fun S hS => ?_
  rw [MeasureTheory.Measure.map_apply Measurable.of_discrete hS]
  rw [PMF.toMeasure_uniformOfFinset_apply _ _ (MeasurableSet.of_discrete)]
  rw [hico]
  simp only [Finset.card_singleton, Nat.cast_one]
  by_cases hmem : (⟨.lit (.int 0), σ⟩ : Cfg rT) ∈ S
  · rw [MeasureTheory.Measure.dirac_apply_of_mem hmem]
    have hfilt : ({x ∈ ({0} : Finset Int) |
        x ∈ (fun x : Int => (⟨.lit (.int x), σ⟩ : Cfg rT)) ⁻¹' S}).card = 1 := by
      simp [Finset.filter_singleton, hmem]
    rw [hfilt]; simp
  · rw [show (MeasureTheory.Measure.dirac (⟨.lit (.int 0), σ⟩ : Cfg rT)) S = 0 from by
          rw [MeasureTheory.Measure.dirac_apply' _ hS]
          simp [hmem]]
    have hfilt : ({x ∈ ({0} : Finset Int) |
        x ∈ (fun x : Int => (⟨.lit (.int x), σ⟩ : Cfg rT)) ⁻¹' S}).card = 0 := by
      simp [Finset.filter_singleton, hmem]
    rw [hfilt]; simp

theorem Cfg.uniform_singleton_ne_one [Countable rT] [MeasurableSingletonClass rT]
    {z : Int} {σ : State rT} {ρ : Cfg rT}
    (Hz : 1 < z) : Cfg.uniform z σ {ρ} ≠ 1 := by
  intro h1
  have Hz0 : 0 < z := by omega
  have hprob : MeasureTheory.IsProbabilityMeasure (Cfg.uniform z σ) :=
    Cfg.uniform_isProbabilityMeasure
  have hpos0 : 0 < Cfg.uniform z σ {⟨.lit (.int 0), σ⟩} :=
    Discrete.Cfg.uniform_singleton_pos_of_mem Hz0 (le_refl 0) Hz0
  have hpos1 : 0 < Cfg.uniform z σ {⟨.lit (.int 1), σ⟩} :=
    Discrete.Cfg.uniform_singleton_pos_of_mem Hz0 (by norm_num) Hz
  have hne : (⟨.lit (.int 0), σ⟩ : Cfg rT) ≠ ⟨.lit (.int 1), σ⟩ := by
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
  by_cases h0 : (⟨.lit (.int 0), σ⟩ : Cfg rT) = ρ
  · have hnρ : (⟨.lit (.int 1), σ⟩ : Cfg rT) ≠ ρ := by
      intro heq; apply hne; rw [h0, ← heq]
    have hin : (⟨.lit (.int 1), σ⟩ : Cfg rT) ∈ ({ρ} : Set (Cfg rT))ᶜ := by
      simp [Set.mem_compl_iff, Set.mem_singleton_iff, hnρ]
    have : Cfg.uniform z σ {⟨.lit (.int 1), σ⟩} ≤ Cfg.uniform z σ ({ρ}ᶜ) :=
      MeasureTheory.measure_mono (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx; exact hin)
    rw [hcompl] at this
    exact absurd (lt_of_lt_of_le hpos1 this) (lt_irrefl _)
  · have hin : (⟨.lit (.int 0), σ⟩ : Cfg rT) ∈ ({ρ} : Set (Cfg rT))ᶜ := by
      simp [Set.mem_compl_iff, Set.mem_singleton_iff, h0]
    have : Cfg.uniform z σ {⟨.lit (.int 0), σ⟩} ≤ Cfg.uniform z σ ({ρ}ᶜ) :=
      MeasureTheory.measure_mono (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx; exact hin)
    rw [hcompl] at this
    exact absurd (lt_of_lt_of_le hpos0 this) (lt_irrefl _)

set_option linter.unnecessarySimpa false in
theorem State.head_step_dzero_upd_tapes [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT} {α : Loc} {bs bs' : Tape}
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
    exact absurd h0 (Cfg.uniform_ne_zero _ _)
  case rand.tape.unalloc hnotin =>
    have hne : α ≠ ‹Lbl› := by
      intro he
      exact hnotin (he ▸ Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [hmem]; rfl))
    have hnone : σ.tapes[‹Lbl›]? = none :=
      Option.not_isSome_iff_eq_none.mp
        (fun hsome => hnotin (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr hsome))
    rw [State.upd_diff_tape_tot (Ne.symm hne), hnone]
  case rand.tape.mismatch =>
    exact absurd h0 (Cfg.uniform_ne_zero _ _)
  case rand.tape.empty =>
    exact absurd h0 (Cfg.uniform_ne_zero _ _)
  case urand h0 =>
    -- `urand` always steps (probability measure), so the `headStep = 0` premise is false.
    exact absurd h0 (MeasureTheory.IsProbabilityMeasure.ne_zero _)

theorem State.det_head_step_upd_tapes
    {e : Exp rT} {σ : State rT} {α : Loc} {bs' : Tape}
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

theorem State.prim_step_empty_tape [Countable rT] [MeasurableSingletonClass rT]
    {K : ProbLang.Ectx rT} {σ : State rT} {α : Loc} {z : Int} {N : Int}
    (_hmem : σ.tapes[α]? = some ⟨N, []⟩) :
    ProbLang.primStep ⟨K.fill (.rand (.lit (.int z)) (.lit (.lbl α))), σ⟩
      = ProbLang.primStep ⟨K.fill (.rand (.lit (.int z)) (.lit .unit)), σ⟩ := by
  have hv_lbl : ¬ (Exp.rand (rT := rT) (.lit (.int z)) (.lit (.lbl α))).isValue := by
    intro h; obtain ⟨hv⟩ := h; cases hv
  have hv_unit : ¬ (Exp.rand (rT := rT) (.lit (.int z)) (.lit .unit)).isValue := by
    intro h; obtain ⟨hv⟩ := h; cases hv
  rw [primStep_fill hv_lbl, primStep_fill hv_unit]
  suffices h : ProbLang.primStep ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩
      = ProbLang.primStep ⟨.rand (.lit (.int z)) (.lit .unit), σ⟩ by rw [h]
  have hdecomp_lbl : (Exp.rand (rT := rT) (.lit (.int z)) (.lit (.lbl α))).decomp
      = ([], .rand (.lit (.int z)) (.lit (.lbl α))) := by
    rw [Exp.decomp_unfold]
    simp only [Exp.decompItem]
    have hlbl : (Exp.lit (rT := rT) (.lbl α)).toVal? = some (.lbl α) := rfl
    have hint : (Exp.lit (rT := rT) (.int z)).toVal? = some (.int z) := rfl
    rw [hlbl, hint]
  have hdecomp_unit : (Exp.rand (rT := rT) (.lit (.int z)) (.lit .unit)).decomp
      = ([], .rand (.lit (.int z)) (.lit .unit)) := by
    rw [Exp.decomp_unfold]
    simp only [Exp.decompItem]
    have hunit : (Exp.lit (rT := rT) .unit).toVal? = some .unit := rfl
    have hint : (Exp.lit (rT := rT) (.int z)).toVal? = some (.int z) := rfl
    rw [hunit, hint]
  simp only [primStep, hdecomp_lbl, hdecomp_unit, Ectx.fillCfg_empty, MeasureTheory.Measure.map_id]
  simp only [headStep, _hmem]
  rw [ite_self]

end ProbLang
