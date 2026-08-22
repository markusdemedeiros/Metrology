module

public meta import Metrology.Meta.Discrete
public import Iris
public import Iris.Instances.Lib.FUpd

@[expose] public section

/-!
# Pulling `∀` into a fupd of plain propositions

The abstract `BIFUpdatePlainly` class only provides `fupd_plainly_sForall_2`
(remove `■` under a fupd from an `sForall`), which is strictly weaker than pulling
a `∀` *into* the fupd. The strong form is not derivable from the class primitives.

The `IProp GF` model does satisfy it, as a consequence of the `uPred_fupd`
definition together with the model-level meaning of `■`: `UPred.plainly P` holds
iff `P` holds at the *unit* resource, independent of the surrounding wsat/ownE.
The proof asserts `◇ ■ (∀ x, Φ x)` as intuitionistic — which duplicates the
spatial context, legitimately, because the asserted proposition is plain —
commutes `■` past `∀` via `plainly_forall`, strips the `◇`, then frames the
original resources back.

This is what lets `glm_implies_tgl` and `twp_step_fupd_tgl` go through for total
adequacy.
-/

open Iris Iris.Std Iris.BI Iris.ProofMode

namespace ProbLang
namespace TotalEris

/-- The universal quantifier moves *inside* the fupd, provided each body is plain
(no-LC variant). -/
theorem iProp_fupd_plainly_forall_2_no_lc
    {GF : BundledGFunctors} [InvGS_gen .hasNoLC GF]
    {E : CoPset} {α : Type _} {Φ : α → IProp GF}
    [∀ x, Plain (Φ x)] :
    (∀ x, iprop(|={E}=> Φ x)) ⊢ iprop(|={E}=> ∀ x, Φ x) := by
  -- `le_upd_unfold_no_le` recovers the `|==> ◇` shape from the `IProp` fupd's `le_upd`;
  -- the `[LcGS .hasNoLC GF]` instance comes from `InvGS_gen .hasNoLC`.
  simp only [fupd, uPred_fupd, le_upd_unfold_no_le.to_eq]
  iintro H ⟨Hwsat, HE⟩
  -- The asserted proposition is plain, so `ihave #` duplicates the spatial context,
  -- which is what makes the per-`x` resource use legitimate.
  ihave #>HP : ◇ ■ (∀ x, Φ x) $$ [H Hwsat HE]
  · iapply (except0_forall.mpr.trans (except0_mono plainly_forall.mpr) :
      iprop((∀ x, ◇ ■ Φ x)) ⊢ iprop(◇ ■ ∀ x, Φ x))
    iintro %x
    imod H $$ %x [$Hwsat $HE] with ⟨-, -, HΦx⟩
    iapply (except0_mono Plain.plain) $$ HΦx
  imodintro
  iframe Hwsat HE
  iapply except0_intro
  iapply plainly_elim $$ HP

/-- Given a per-`x` fupd conditional on a pure premise `⌜R x⌝`, conclude a single
fupd of the universally-quantified pure implication. This is the shape
`glmPrimStep'`'s per-outcome continuation has. -/
theorem iProp_fupd_plainly_forall_pure_impl_no_lc
    {GF : BundledGFunctors} [InvGS_gen .hasNoLC GF]
    {E : CoPset} {α : Type _} {R : α → Prop} {P : α → Prop} :
    (∀ x, iprop(⌜R x⌝ -∗ |={E}=> ⌜P x⌝))
      ⊢@{IProp GF} iprop(|={E}=> ⌜∀ x, R x → P x⌝) := by
  iintro H
  ihave H' : iprop(∀ x, |={E}=> ⌜R x → P x⌝) $$ [H]
  · iintro %x
    by_cases hR : R x
    · imod H $$ %x [//] with %hP
      imodintro
      ipureintro
      exact fun _ => hP
    · imodintro
      ipureintro
      exact fun hRx => absurd hRx hR
  imod iProp_fupd_plainly_forall_2_no_lc $$ H' with H''
  imodintro
  iapply pure_forall.mpr $$ H''

end TotalEris
end ProbLang
