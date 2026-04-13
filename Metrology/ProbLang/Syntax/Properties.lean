import Metrology.ProbLang.Syntax.Syntax

/-!
# LN plumbing lemmas for `Exp`

Standard locally-nameless substitution theory, mirroring
`cslib/Cslib/Languages/LambdaCalculus/LocallyNameless/Untyped/Properties.lean`
for our ProbLang `Exp` syntax.

All lemmas here concern `openRec` / `closeRec` / `subst` / `fv` / `LC`.
-/

namespace ProbLang
open Cslib
open Exp

namespace Exp

variable {x y : Var} {e e' u t : Exp}

/-- An opening appearing on both sides of an equality can be removed. -/
lemma open_lc_aux (e : Exp) (j v i u) (neq : i ≠ j)
    (heq : openRec j v e = openRec i u (openRec j v e)) :
    e = openRec i u e := by
  induction e generalizing i j <;> grind

/-- Swap opens at non-clashing depths (both substituting free variables). -/
lemma swap_open_fvars (k n : Nat) (x y : Var) (e : Exp) (neq : k ≠ n) :
    openRec k (fvar x) (openRec n (fvar y) e)
      = openRec n (fvar y) (openRec k (fvar x) e) := by
  induction e generalizing k n <;> grind

/-- Substitution of an absent free variable is the identity. -/
@[scoped grind =]
theorem subst_fresh (x : Var) (e sub : Exp) (h : x ∉ e.fv) :
    subst e x sub = e := by
  induction e <;> grind

/-- Opening then closing at the same depth recovers the term, provided the atom is fresh. -/
lemma open_close (x : Var) (e : Exp) (k : Nat) (h : x ∉ e.fv) :
    e = closeRec k x (openRec k (fvar x) e) := by
  induction e generalizing k <;> grind

/-- Specialisation of `open_close` to the outermost binder. -/
lemma open_close_var (x : Var) (e : Exp) (h : x ∉ e.fv) :
    e = close (open' e (fvar x)) x :=
  open_close x e 0 h

/-- Opening at a free variable is injective on terms not containing that variable. -/
lemma open_injective (x : Var) (e e' : Exp) (hx : x ∉ e.fv) (hx' : x ∉ e'.fv)
    (heq : open' e (fvar x) = open' e' (fvar x)) : e = e' := by
  grind [open_close x e 0 hx, open_close x e' 0 hx']

/-- Opening and closing commute at non-clashing depths / variables. -/
lemma swap_open_fvar_close (k n : Nat) (x y : Var) (e : Exp)
    (hk : k ≠ n) (hxy : x ≠ y) :
    closeRec k x (openRec n (fvar y) e)
      = openRec n (fvar y) (closeRec k x e) := by
  induction e generalizing k n <;> grind

/-- Closing preserves the absence of other free variables. -/
lemma close_preserve_not_fvar {k x y} (e : Exp) (h : x ∉ e.fv) :
    x ∉ (closeRec k y e).fv := by
  induction e generalizing k <;> grind

/-- Opening at a fresh free variable preserves the absence of `x`. -/
lemma open_fresh_preserve_not_fvar {k x y} (e : Exp) (h : x ∉ e.fv) (hne : x ≠ y) :
    x ∉ (openRec k (fvar y) e).fv := by
  induction e generalizing k <;> grind

/-- Opening preserves free-variable absence. -/
lemma open_preserve_not_fvar {k x} (e u : Exp) (he : x ∉ e.fv) (hu : x ∉ u.fv) :
    x ∉ (openRec k u e).fv := by
  induction e generalizing k <;> grind

/-- Substitution cannot introduce `x` if it is absent from both arguments. -/
lemma subst_preserve_not_fvar {x y : Var} (e u : Exp)
    (h : x ∉ e.fv ∪ u.fv) : x ∉ (subst e y u).fv := by
  induction e <;> grind

/-- The free variables after substituting `v` for `x` in `e` are contained in
    `(e.fv \ {x}) ∪ v.fv`. -/
lemma fv_subst_subset (e : Exp) (x : Var) (v : Exp) :
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
lemma close_var_not_fvar_rec (x) (k) (e : Exp) : x ∉ (closeRec k x e).fv := by
  induction e generalizing k <;> grind

/-- Specialisation to the outermost closing. -/
lemma close_var_not_fvar (x : Var) (e : Exp) : x ∉ (close e x).fv :=
  close_var_not_fvar_rec x 0 e

/-- A locally-closed term is unchanged by opening. -/
@[scoped grind =_]
lemma open_lc (k : Nat) (t : Exp) (e : Exp) (he : e.LC) :
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
lemma subst_openRec (x : Var) (t : Exp) (k : Nat) (u e : Exp) (hu : LC t) :
    subst (openRec k u e) x t = openRec k (subst u x t) (subst e x t) := by
  induction e generalizing k with grind

/-- Substitution commutes with opening the outermost binder. -/
lemma subst_open (x : Var) (t : Exp) (u e : Exp) (hu : LC t) :
    subst (open' e u) x t = open' (subst e x t) (subst u x t) := by grind

/-- When opening at a fresh free variable, substitution pulls through. -/
theorem subst_open_var (x y : Var) (u e : Exp) (hne : y ≠ x) (hu : LC u) :
    subst (open' e (fvar x)) y u = open' (subst e y u) (fvar x) := by grind

/-- Substitution of LC terms into LC terms is LC. -/
@[scoped grind ←]
theorem subst_lc {x : Var} {e u : Exp} (he : LC e) (hu : LC u) : LC (subst e x u) := by
  induction he with
  | lam L e _ ih =>
      apply LC.lam (free_union Var)
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
      apply LC.fix (free_union Var)
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
lemma subst_intro (x : Var) (t e : Exp) (mem : x ∉ e.fv) (t_lc : LC t) :
    open' e t = subst (open' e (fvar x)) x t := by
  grind

/-- β-style: opening an LC `lam` body with an LC argument is LC. -/
theorem beta_lc (L : Finset Var) (e u : Exp)
    (he : ∀ x ∉ L, LC (open' e (fvar x))) (hu : LC u) : LC (open' e u) := by
  obtain ⟨x, hx⟩ := HasFresh.fresh_exists (L ∪ e.fv)
  have hxL : x ∉ L := fun h => hx (Finset.mem_union_left _ h)
  have hxfv : x ∉ e.fv := fun h => hx (Finset.mem_union_right _ h)
  grind [subst_intro x u e hxfv hu, subst_lc (he x hxL) hu]

end Exp
end ProbLang
