module

public import Iris.BI.Lib.Fixpoint

@[expose] public section

/-!
# Shared `bi_least_fixpoint` utilities

Helpers used by both the Approxis and TotalEris weakest preconditions.
-/

open Iris Iris.BI OFE

/-- Outer non-expansiveness for `bi_least_fixpoint`: if the pre-functors agree
`≡{n}≡` pointwise and the seed points agree, the fixpoints agree.

Used in both `Metrology/Approxis/AppWeakestpre.lean` and
`Metrology/TotalEris/Weakestpre.lean` to discharge the contractivity
side-condition when fixing the post-functor `Φ` as an outer parameter. -/
theorem least_fixpoint_ne_outer {PROP : Type _} [BI PROP] {A : Type _} [OFE A]
    {F1 F2 : (A → PROP) → (A → PROP)} {n : Nat} (HF : ∀ Φ x, F1 Φ x ≡{n}≡ F2 Φ x)
    {x1 x2 : A} (Hx : x1 ≡{n}≡ x2) : bi_least_fixpoint F1 x1 ≡{n}≡ bi_least_fixpoint F2 x2 := by
  refine forall_ne fun Φ => ?_
  refine wand_ne.ne ?_ (NonExpansive.ne Hx)
  refine intuitionistically_ne.ne ?_
  refine forall_ne fun y => ?_
  exact wand_ne.ne (HF _ _) (.of_eq rfl)

/-- Any function out of a Leibniz-discrete OFE is non-expansive: distance at
level `n` collapses to syntactic equality via the discreteness instance.
Used throughout the TotalEris stack to discharge `NonExpansive Q` for `Q :
Exp → IProp GF` (and similar) postconditions threaded through fixpoint
iteration. -/
theorem nonExpansive_of_discrete_leibniz {T : Type _} [COFE T] [OFE.Discrete T]
     {P : Type _} [OFE P] (f : T → P) : NonExpansive f := by
  constructor
  intro n x y hd
  have : x = y := (OFE.Discrete.discrete hd)
  subst this; exact .of_eq rfl

/-- Distance at level `n` in a Leibniz-discrete OFE collapses to syntactic
equality. Useful for inline use inside `BIMonoPred.mono_pred_ne` and similar
`NonExpansive` field-witness proofs where `nonExpansive_of_discrete_leibniz`
doesn't apply (the function-shape doesn't match). -/
theorem eq_of_dist_discrete_leibniz {T : Type _} [COFE T] [OFE.Discrete T]
    {n : Nat} {x y : T} (hd : x ≡{n}≡ y) : x = y :=
  (OFE.Discrete.discrete hd)
