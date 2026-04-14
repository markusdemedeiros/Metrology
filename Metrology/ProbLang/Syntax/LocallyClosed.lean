import Metrology.ProbLang.Syntax.Syntax

/-!
# LN plumbing theorems for `Exp`

Standard locally-nameless substitution theory, mirroring
`cslib/Cslib/Languages/LambdaCalculus/LocallyNameless/Untyped/Properties.lean`
for our ProbLang `Exp` syntax.

All theorems here concern `openRec` / `closeRec` / `subst` / `fv` / `LC`.
-/

namespace ProbLang
open Cslib
open Exp

namespace Exp

variable {x y : Var} {e e' u t : Exp}

/-- An opening appearing on both sides of an equality can be removed. -/
theorem open_lc_aux (e : Exp) (j v i u) (neq : i ≠ j)
    (heq : openRec j v e = openRec i u (openRec j v e)) :
    e = openRec i u e := by
  induction e generalizing i j <;> grind

/-- Swap opens at non-clashing depths (both substituting free variables). -/
theorem swap_open_fvars (k n : Nat) (x y : Var) (e : Exp) (neq : k ≠ n) :
    openRec k (fvar x) (openRec n (fvar y) e)
      = openRec n (fvar y) (openRec k (fvar x) e) := by
  induction e generalizing k n <;> grind

/-- Substitution of an absent free variable is the identity. -/
@[scoped grind =]
theorem subst_fresh (x : Var) (e sub : Exp) (h : x ∉ e.fv) :
    subst e x sub = e := by
  induction e <;> grind

/-- Opening then closing at the same depth recovers the term, provided the atom is fresh. -/
theorem open_close (x : Var) (e : Exp) (k : Nat) (h : x ∉ e.fv) :
    e = closeRec k x (openRec k (fvar x) e) := by
  induction e generalizing k <;> grind

/-- Specialisation of `open_close` to the outermost binder. -/
theorem open_close_var (x : Var) (e : Exp) (h : x ∉ e.fv) :
    e = close (open' e (fvar x)) x :=
  open_close x e 0 h

/-- Opening at a free variable is injective on terms not containing that variable. -/
theorem open_injective (x : Var) (e e' : Exp) (hx : x ∉ e.fv) (hx' : x ∉ e'.fv)
    (heq : open' e (fvar x) = open' e' (fvar x)) : e = e' := by
  grind [open_close x e 0 hx, open_close x e' 0 hx']

/-- Opening and closing commute at non-clashing depths / variables. -/
theorem swap_open_fvar_close (k n : Nat) (x y : Var) (e : Exp)
    (hk : k ≠ n) (hxy : x ≠ y) :
    closeRec k x (openRec n (fvar y) e)
      = openRec n (fvar y) (closeRec k x e) := by
  induction e generalizing k n <;> grind

/-- Closing preserves the absence of other free variables. -/
theorem close_preserve_not_fvar {k x y} (e : Exp) (h : x ∉ e.fv) :
    x ∉ (closeRec k y e).fv := by
  induction e generalizing k <;> grind

/-- Opening at a fresh free variable preserves the absence of `x`. -/
theorem open_fresh_preserve_not_fvar {k x y} (e : Exp) (h : x ∉ e.fv) (hne : x ≠ y) :
    x ∉ (openRec k (fvar y) e).fv := by
  induction e generalizing k <;> grind

/-- Opening preserves free-variable absence. -/
theorem open_preserve_not_fvar {k x} (e u : Exp) (he : x ∉ e.fv) (hu : x ∉ u.fv) :
    x ∉ (openRec k u e).fv := by
  induction e generalizing k <;> grind

/-- Substitution cannot introduce `x` if it is absent from both arguments. -/
theorem subst_preserve_not_fvar {x y : Var} (e u : Exp)
    (h : x ∉ e.fv ∪ u.fv) : x ∉ (subst e y u).fv := by
  induction e <;> grind

/-- The free variables after substituting `v` for `x` in `e` are contained in
    `(e.fv \ {x}) ∪ v.fv`. -/
theorem fv_subst_subset (e : Exp) (x : Var) (v : Exp) :
    (subst e x v).fv ⊆ (e.fv \ {x}) ∪ v.fv := by
  intro z hz
  induction e with
  | fvar y =>
      by_cases hxy : x = y
      · subst hxy; simp [subst] at hz; exact Finset.mem_union_right _ hz
      · simp [subst, hxy] at hz; subst hz
        refine Finset.mem_union_left _ ?_
        simp; exact fun h => hxy h.symm
  | bvar _ | lit _ | fail => simp [subst] at hz
  | lam e ih | fix e ih | unop _ e ih | fst e ih | snd e ih
  | inl e ih | inr e ih | alloc e ih | load e ih | tape e ih | scrut e _ ih =>
      simp [subst] at hz; exact ih hz
  | app e1 e2 ih1 ih2 | binop _ e1 e2 ih1 ih2 | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2 | rand e1 e2 ih1 ih2 =>
      simp [subst] at hz
      rcases hz with h1 | h2
      · have hi := ih1 h1
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton] at hi
        simp only [fv, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
        rcases hi with ⟨hf, hne⟩ | hv
        · exact .inl ⟨.inl hf, hne⟩
        · exact .inr hv
      · have hi := ih2 h2
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton] at hi
        simp only [fv, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
        rcases hi with ⟨hf, hne⟩ | hv
        · exact .inl ⟨.inr hf, hne⟩
        · exact .inr hv
  | cond e0 e1 e2 ih0 ih1 ih2 | case e0 e1 e2 ih0 ih1 ih2 =>
      simp only [subst, fv, Finset.mem_union] at hz
      simp only [fv, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
      rcases hz with (h0 | h1) | h2
      · have hi := ih0 h0
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton] at hi
        rcases hi with ⟨hf, hne⟩ | hv
        · exact .inl ⟨.inl (.inl hf), hne⟩
        · exact .inr hv
      · have hi := ih1 h1
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton] at hi
        rcases hi with ⟨hf, hne⟩ | hv
        · exact .inl ⟨.inl (.inr hf), hne⟩
        · exact .inr hv
      · have hi := ih2 h2
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton] at hi
        rcases hi with ⟨hf, hne⟩ | hv
        · exact .inl ⟨.inr hf, hne⟩
        · exact .inr hv

/-- Closing always removes the closed variable from the fv set. -/
@[scoped grind ←]
theorem close_var_not_fvar_rec (x) (k) (e : Exp) : x ∉ (closeRec k x e).fv := by
  induction e generalizing k <;> grind

/-- Specialisation to the outermost closing. -/
theorem close_var_not_fvar (x : Var) (e : Exp) : x ∉ (close e x).fv :=
  close_var_not_fvar_rec x 0 e

/-- A locally-closed term is unchanged by opening. -/
@[scoped grind =_]
theorem open_lc (k : Nat) (t : Exp) (e : Exp) (he : e.IsLocallyClosed) :
    e = openRec k t e := by
  induction he generalizing k with
  | lam L e _ ih =>
      obtain ⟨x, hx⟩ := HasFresh.fresh_exists L
      grind [open_lc_aux e 0 (fvar x) (k+1) t]
  | fix L e _ ih =>
      obtain ⟨x, hx⟩ := HasFresh.fresh_exists L
      grind [open_lc_aux e 0 (fvar x) (k+1) t]
  | _ => grind

/-- Substitution distributes through `openRec` when the substitute is LC. -/
@[scoped grind =]
theorem subst_openRec (x : Var) (t : Exp) (k : Nat) (u e : Exp) (hu : IsLocallyClosed t) :
    subst (openRec k u e) x t = openRec k (subst u x t) (subst e x t) := by
  induction e generalizing k with grind

/-- Substitution commutes with opening the outermost binder. -/
theorem subst_open (x : Var) (t : Exp) (u e : Exp) (hu : IsLocallyClosed t) :
    subst (open' e u) x t = open' (subst e x t) (subst u x t) := by grind

/-- When opening at a fresh free variable, substitution pulls through. -/
theorem subst_open_var (x y : Var) (u e : Exp) (hne : y ≠ x) (hu : IsLocallyClosed u) :
    subst (open' e (fvar x)) y u = open' (subst e y u) (fvar x) := by grind

/-- Substitution of LC terms into LC terms is LC. -/
@[scoped grind ←]
theorem subst_lc {x : Var} {e u : Exp} (he : IsLocallyClosed e) (hu : IsLocallyClosed u) : IsLocallyClosed (subst e x u) := by
  induction he with
  | lam L e _ ih =>
      apply IsLocallyClosed.lam (free_union Var)
      intro y hy
      have hyL : y ∉ L := by
        have := hy
        grind
      have hyx : y ≠ x := by
        intro h; subst h
        have := hy
        grind
      grind [subst_open_var]
  | fix L e _ ih =>
      apply IsLocallyClosed.fix (free_union Var)
      intro y hy
      have hyL : y ∉ L := by
        have := hy
        grind
      have hyx : y ≠ x := by
        intro h; subst h
        have := hy
        grind
      grind [subst_open_var]
  | _ => grind

/-- Opening at a term is equivalent to opening at a free variable and substituting. -/
theorem subst_intro (x : Var) (t e : Exp) (mem : x ∉ e.fv) (t_lc : IsLocallyClosed t) :
    open' e t = subst (open' e (fvar x)) x t := by
  grind

/-- β-style: opening an LC `lam` body with an LC argument is LC. -/
theorem beta_lc (L : Finset Var) (e u : Exp)
    (he : ∀ x ∉ L, IsLocallyClosed (open' e (fvar x))) (hu : IsLocallyClosed u) : IsLocallyClosed (open' e u) := by
  obtain ⟨x, hx⟩ := HasFresh.fresh_exists (L ∪ e.fv)
  have hxL : x ∉ L := fun h => hx (Finset.mem_union_left _ h)
  have hxfv : x ∉ e.fv := fun h => hx (Finset.mem_union_right _ h)
  grind [subst_intro x u e hxfv hu, subst_lc (he x hxL) hu]

/-- The "open ∘ close = subst" lemma for LC terms.
    Mirrors `Cslib...Untyped.Properties.open_close_to_subst`. -/
@[scoped grind =]
theorem open_close_to_subst (e : Exp) (x y : Var) (k : Nat) (he : IsLocallyClosed e) :
    openRec k (fvar y) (closeRec k x e) = subst e x (fvar y) := by
  induction he generalizing k with
  | lam L t _ ih =>
      simp only [closeRec, openRec, subst]
      congr 1
      have ⟨x', hx'⟩ := HasFresh.fresh_exists (L ∪ t.fv ∪ {x, y})
      have hx'L : x' ∉ L := fun h => hx' (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      have hx'fv : x' ∉ t.fv := fun h => hx'
        (Finset.mem_union_left _ (Finset.mem_union_right _ h))
      have hx'x : x' ≠ x := fun h => hx' (by
        rw [h]; exact Finset.mem_union_right _ (by simp))
      have hx'y : x' ≠ y := fun h => hx' (by
        rw [h]; exact Finset.mem_union_right _ (by simp))
      have hih := ih x' hx'L (k+1)
      have hLfv : x' ∉ (openRec (k+1) (fvar y) (closeRec (k+1) x t)).fv :=
        open_fresh_preserve_not_fvar _ (close_preserve_not_fvar _ hx'fv) hx'y
      have hRfv : x' ∉ (subst t x (fvar y)).fv := by
        apply subst_preserve_not_fvar
        simp only [Finset.mem_union, fv, not_or]
        refine ⟨hx'fv, ?_⟩
        intro h
        rw [Finset.mem_singleton] at h
        exact hx'y h
      have hLHS :
          open' (openRec (k+1) (fvar y) (closeRec (k+1) x t)) (fvar x')
            = openRec (k+1) (fvar y) (closeRec (k+1) x (open' t (fvar x'))) := by
        simp only [open']
        rw [swap_open_fvars 0 (k+1) x' y _ (by omega)]
        rw [swap_open_fvar_close (k+1) 0 x x' t (by omega) hx'x.symm]
      have hIH := ih x' hx'L (k+1)
      have hRHS :
          open' (subst t x (fvar y)) (fvar x')
            = subst (open' t (fvar x')) x (fvar y) := by
        rw [subst_open_var x' x (fvar y) t hx'x.symm (.fvar y)]
      have heq : open' (openRec (k+1) (fvar y) (closeRec (k+1) x t)) (fvar x')
            = open' (subst t x (fvar y)) (fvar x') := by
        rw [hLHS, hIH, hRHS]
      exact open_injective x' _ _ hLfv hRfv heq
  | fix L t _ ih =>
      simp only [closeRec, openRec, subst]
      congr 1
      have ⟨x', hx'⟩ := HasFresh.fresh_exists (L ∪ t.fv ∪ {x, y})
      have hx'L : x' ∉ L := fun h => hx' (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      have hx'fv : x' ∉ t.fv := fun h => hx'
        (Finset.mem_union_left _ (Finset.mem_union_right _ h))
      have hx'x : x' ≠ x := fun h => hx' (by
        rw [h]; exact Finset.mem_union_right _ (by simp))
      have hx'y : x' ≠ y := fun h => hx' (by
        rw [h]; exact Finset.mem_union_right _ (by simp))
      have hLfv : x' ∉ (openRec (k+1) (fvar y) (closeRec (k+1) x t)).fv :=
        open_fresh_preserve_not_fvar _ (close_preserve_not_fvar _ hx'fv) hx'y
      have hRfv : x' ∉ (subst t x (fvar y)).fv := by
        apply subst_preserve_not_fvar
        simp only [Finset.mem_union, fv, not_or]
        refine ⟨hx'fv, ?_⟩
        intro h; rw [Finset.mem_singleton] at h; exact hx'y h
      have hLHS :
          open' (openRec (k+1) (fvar y) (closeRec (k+1) x t)) (fvar x')
            = openRec (k+1) (fvar y) (closeRec (k+1) x (open' t (fvar x'))) := by
        simp only [open']
        rw [swap_open_fvars 0 (k+1) x' y _ (by omega)]
        rw [swap_open_fvar_close (k+1) 0 x x' t (by omega) hx'x.symm]
      have hIH := ih x' hx'L (k+1)
      have hRHS :
          open' (subst t x (fvar y)) (fvar x')
            = subst (open' t (fvar x')) x (fvar y) := by
        rw [subst_open_var x' x (fvar y) t hx'x.symm (.fvar y)]
      have heq : open' (openRec (k+1) (fvar y) (closeRec (k+1) x t)) (fvar x')
            = open' (subst t x (fvar y)) (fvar x') := by
        rw [hLHS, hIH, hRHS]
      exact open_injective x' _ _ hLfv hRfv heq
  | _ => grind

/-- Specialised: outermost open ∘ close equals substitution. -/
theorem open_close_subst_lc (x y : Var) (e : Exp) (he : IsLocallyClosed e) :
    open' (close e x) (fvar y) = subst e x (fvar y) :=
  open_close_to_subst e x y 0 he

/-- Generalised: outermost open ∘ close equals substitution by an arbitrary
    LC value. Proved via `subst_intro` with a fresh atom and the `fvar`-only
    version `open_close_subst_lc`. -/
theorem open_close_subst_lc_gen (x : Var) (e v : Exp)
    (he : IsLocallyClosed e) (hv : IsLocallyClosed v) :
    open' (close e x) v = subst e x v := by
  -- Pick a fresh atom z disjoint from `e.fv ∪ v.fv ∪ {x}`, then use
  -- `subst_intro` to factor `open' (close e x) v` through `subst _ z v`.
  obtain ⟨z, hz⟩ := HasFresh.fresh_exists (insert x (e.fv ∪ v.fv))
  have hzx : z ≠ x := fun h => hz (h ▸ Finset.mem_insert_self _ _)
  have hze : z ∉ e.fv := fun h => hz (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
  have hzv : z ∉ v.fv := fun h => hz (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
  have hzcl : z ∉ (close e x).fv := close_preserve_not_fvar e hze
  rw [subst_intro z v (close e x) hzcl hv]
  rw [open_close_subst_lc x z e he]
  have aux : ∀ (e : Exp), z ∉ e.fv →
      subst (subst e x (fvar z)) z v = subst e x v := by
    intro e hze
    induction e with
    | fvar y =>
        by_cases hxy : x = y
        · subst hxy; simp [subst]
        · -- x ≠ y; inner subst leaves fvar y, outer subst hits z vs y.
          have hzy : z ≠ y := fun h => hze (by rw [h]; simp [fv])
          simp [subst, hxy, hzy]
    | bvar _ | lit _ | fail => simp [subst]
    | lam e ih | fix e ih | unop _ e ih | fst e ih | snd e ih
    | inl e ih | inr e ih | alloc e ih | load e ih | tape e ih | scrut e _ ih =>
        simp only [subst, fv] at hze ⊢
        rw [ih hze]
    | app e1 e2 ih1 ih2 | binop _ e1 e2 ih1 ih2 | pair e1 e2 ih1 ih2
    | store e1 e2 ih1 ih2 | rand e1 e2 ih1 ih2 =>
        simp only [subst, fv, Finset.mem_union, not_or] at hze ⊢
        rw [ih1 hze.1, ih2 hze.2]
    | cond e0 e1 e2 ih0 ih1 ih2 | case e0 e1 e2 ih0 ih1 ih2 =>
        simp only [subst, fv, Finset.mem_union, not_or] at hze ⊢
        rw [ih0 hze.1.1, ih1 hze.1.2, ih2 hze.2]
  exact aux e hze

end Exp
end ProbLang
