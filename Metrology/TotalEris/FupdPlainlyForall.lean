module

public import Iris
public import Iris.Instances.Lib.FUpd

@[expose] public section

/-!
# `fupd_plainly_forall_2` for `IProp GF`

iris-Lean's abstract `BIFUpdatePlainly` typeclass ships
`fupd_plainly_sForall_2` (the "remove `■` under fupd from `sForall`" form),
which is strictly weaker than modern iris-Coq's `fupd_plainly_forall_2`
(pull `∀` *into* fupd). The strong form is not derivable from the abstract
class primitives — it is an additional axiom of `BiFUpdPlainly` in
iris-Coq.

However, the `IProp GF` model **does** satisfy the strong form: it is a
direct consequence of the `uPred_fupd` definition and the model-level
meaning of `■` (`UPred.plainly P` holds iff `P` holds at the *unit*
resource — independent of the surrounding wsat/ownE). The proof mirrors
the iris-Lean `fupd_plainly_keep_l` instance: assert `◇ ■ (∀ x, Φ x)` as
intuitionistic (the proof gets a duplicated spatial context because the
asserted proposition is plain), commute `■` past `∀` via `plainly_forall`,
strip the `◇`, then `iframe` back the original resources.

This unblocks `glm_implies_tgl` and `twp_step_fupd_tgl` for the Eris
total-adequacy theorem.
-/

open Iris Iris.Std Iris.BI Iris.ProofMode

namespace ProbLang
namespace TotalEris

/-- **`fupd_plainly_forall_2` for `IProp GF`** (no-LC variant). The
universal moves *inside* the fupd, provided each body is plain. Mirrors
iris-Coq's `fupd_plainly_forall_2` (the standard `BiFUpdPlainly` axiom). -/
theorem iProp_fupd_plainly_forall_2_no_lc
    {GF : BundledGFunctors} [InvGS_gen false GF]
    {E : CoPset} {A : Type _} {Φ : A → IProp GF}
    [∀ x, Plain (Φ x)] :
    (∀ x, iprop(|={E}=> Φ x)) ⊢@{IProp GF} iprop(|={E}=> ∀ x, Φ x) := by
  simp only [fupd, uPred_fupd, le_upd_if, Bool.false_eq_true, ↓reduceIte]
  iintro H ⟨Hwsat, HE⟩
  -- Assert the plain universal as intuitionistic. Because the goal is
  -- plain, `ihave #` duplicates the spatial context for the subproof —
  -- which is what makes the per-`x` resource use legitimate.
  ihave #>HP : ◇ ■ (∀ x, Φ x) $$ [H Hwsat HE]
  · -- Reduce `◇ ■ (∀ x, Φ x)` to `∀ x, ◇ ■ Φ x` via plainly/except0
    -- commutations with `∀`, then introduce `x` and run the per-`x`
    -- `imod` against the duplicated `H, Hwsat, HE`.
    iapply (except0_forall.mpr.trans (except0_mono plainly_forall.mpr) :
      iprop((∀ x, ◇ ■ Φ x)) ⊢@{IProp GF} iprop(◇ ■ ∀ x, Φ x))
    iintro %x
    ihave Hx := H $$ %x
    imod Hx $$ [Hwsat HE] with ⟨_, _, HΦx⟩
    · isplitl [Hwsat]; · iexact Hwsat
      iexact HE
    -- Goal: `◇ ■ Φ x`. `HΦx : ◇ Φ x` (the `imod` destructure leaves the
    -- outer `◇` on each component). Close by mapping `Φ x → ■ Φ x` under
    -- `◇` via `except0_mono Plain.plain`.
    iapply (except0_mono Plain.plain)
    iexact HΦx
  imodintro
  iframe
  -- Goal: `◇ ∀ x, Φ x`. We have `HP : ■ ∀ x, Φ x` (intuitionistic).
  iapply except0_intro
  iapply plainly_elim
  iexact HP

/-- **Pure-implication corollary**: given a per-`x` fupd that's conditional on a
pure premise `⌜R x⌝`, conclude a single fupd of the universally-quantified
pure implication. The shape that matches `glmPrimStep`'s per-outcome
continuation. -/
theorem iProp_fupd_plainly_forall_pure_impl_no_lc
    {GF : BundledGFunctors} [InvGS_gen false GF]
    {E : CoPset} {A : Type _} {R : A → Prop} {P : A → Prop} :
    (∀ x, iprop(⌜R x⌝ -∗ |={E}=> ⌜P x⌝))
      ⊢@{IProp GF} iprop(|={E}=> ⌜∀ x, R x → P x⌝) := by
  iintro H
  -- Stage 1: for each x, push the pure premise inside the fupd as an
  -- implication, yielding `∀ x, |={E}=> ⌜R x → P x⌝`.
  ihave H' : iprop(∀ x, |={E}=> ⌜R x → P x⌝) $$ [H]
  · iintro %x
    -- Classical case-split on `R x` at the Lean level.
    by_cases hR : R x
    · -- Apply the hypothesis at x with the witness `hR`.
      ihave Hx := H $$ %x
      ihave HP : iprop(|={E}=> ⌜P x⌝) $$ [Hx]
      · iapply Hx
        ipure_intro
        exact hR
      imod HP with %hP
      imodintro
      ipure_intro
      intro _
      exact hP
    · -- Vacuously: `¬R x → (R x → P x)`.
      imodintro
      ipure_intro
      intro hRx
      exact absurd hRx hR
  -- Stage 2: apply `fupd_plainly_forall_2` to commute the universal in.
  ihave H'' := iProp_fupd_plainly_forall_2_no_lc $$ H'
  imod H'' with H''
  imodintro
  -- Goal: `⌜∀ x, R x → P x⌝`. Have `H'' : ∀ x, ⌜R x → P x⌝`. Push via
  -- `pure_forall.mpr`.
  ihave Hf := pure_forall.mpr $$ H''
  iexact Hf

end TotalEris
end ProbLang
