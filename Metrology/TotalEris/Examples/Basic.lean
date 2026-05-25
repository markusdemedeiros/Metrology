module

public import Metrology.TotalEris

@[expose] public section

/-!
# Basic TotalEris smoke tests

Tiny examples to validate the API surface:

* values introduce trivially via `twp_value`,
* allocation + load roundtrips via `twp_alloc` and `twp_load`,
* pure beta-reduction via `twp_pure_step_fupd`.

These don't use error credits and don't depend on adequacy. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS

namespace ProbLang
namespace TotalEris

variable {hlc : Bool} {GF : BundledGFunctors} [ErisGS hlc GF]

/-- Trivial value-return: `tglWp E v (fun w => ⌜w = v⌝)`. -/
example (E : CoPset) (v : Val) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) := by
  iapply tglWp_value
  ipure_intro; rfl

/-- Alloc → load roundtrip: `let x = ref v in !x = v`.

Note the result expression is `.load (.lit (.loc l))` post-step. Without
`twp_bind` (not yet ported), we can only test isolated primitive laws. -/
example (E : CoPset) (v : Val) :
    ⊢@{IProp GF} tglWp E (.alloc (.ofVal v))
      (fun w => iprop(∃ l : Loc,
        ⌜w = ⟨.lit (.loc l), IsVal.lit⟩⌝ ∗ appHeapFrag l v)) := by
  iapply twp_alloc
  iintro %l Hl
  iexists l
  isplitr
  · ipure_intro; rfl
  iexact Hl

/-- `twp_rand_tape` round-trip: reading the head of a non-empty tape returns
the stored value and leaves the tape's tail in place. -/
example (E : CoPset) (l : Loc) (z : Int)
    (n : { z' : Int // 0 ≤ z' ∧ z' < z })
    (ns : List { z' : Int // 0 ≤ z' ∧ z' < z }) :
    ⊢@{IProp GF} l ↪ₐ ⟨z, n :: ns⟩ -∗
      tglWp E (.rand (.lit (.int z)) (.lit (.lbl l)))
        (fun w => iprop(⌜w = ⟨.lit (.int n.val), IsVal.lit⟩⌝ ∗ l ↪ₐ ⟨z, ns⟩)) := by
  iintro Hl
  iapply twp_rand_tape
  isplitl [Hl]
  · iexact Hl
  iintro Hl'
  isplitr
  · ipure_intro; rfl
  iexact Hl'

/-- `twp_rand_tape_empty`: rand on an empty tape falls through to uniform
sampling and the empty tape is preserved. -/
example (E : CoPset) (l : Loc) (z : Int) (Hz : 0 < z) :
    ⊢@{IProp GF} l ↪ₐ ⟨z, []⟩ -∗
      tglWp E (.rand (.lit (.int z)) (.lit (.lbl l)))
        (fun w => iprop(∃ n : Int,
          ⌜0 ≤ n ∧ n < z⌝ ∗ ⌜w = ⟨.lit (.int n), IsVal.lit⟩⌝ ∗ l ↪ₐ ⟨z, []⟩)) := by
  iintro Hl
  iapply (twp_rand_tape_empty Hz)
  isplitl [Hl]
  · iexact Hl
  iintro %n Hl' %Hbnd
  iexists n
  isplitr; · ipure_intro; exact Hbnd
  isplitr; · ipure_intro; rfl
  iexact Hl'

/-- `tglWp_mono`: weaken a `Φ`-post into a stronger `Ψ`-post via a Lean-level
pointwise entailment. -/
example (E : CoPset) (v : Val) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝ ∗ ⌜w = v⌝))
      -∗ tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) := by
  iintro HW
  iapply ErisWpGS.tglWp_mono (Φ := fun w => iprop(⌜w = v⌝ ∗ ⌜w = v⌝))
  · intro w
    iintro ⟨H, -⟩; iexact H
  iexact HW

/-- `tglWp_fupd`: a `|={E}=>` in the post is absorbed. -/
example (E : CoPset) (v : Val) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w => iprop(|={E}=> ⌜w = v⌝))
      -∗ tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) := by
  iintro HW
  iapply ErisWpGS.tglWp_fupd
  iexact HW

/-- `tglWp_wand`: combine a WP with a spatial continuation wand. -/
example (E : CoPset) (v : Val) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) -∗
      tglWp E (.ofVal v) (fun w => iprop(⌜w = v ∨ w = v⌝)) := by
  iintro HW
  iapply tglWp_wand
  isplitl [HW]; · iexact HW
  iintro %w %Hw
  ipure_intro
  exact Or.inl Hw

/-- `tglWp_strong_mono`: the fupd-aware variant. -/
example (E : CoPset) (v : Val) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) -∗
      tglWp E (.ofVal v) (fun w => iprop(|={E}=> ⌜w = v⌝)) := by
  iintro HW
  iapply tglWp_strong_mono
  isplitl [HW]; · iexact HW
  iintro %w %Hw
  imodintro
  imodintro
  ipure_intro; exact Hw

/-- `tglWp_bind_value`: the value-only specialization of bind. When the inner
expression is already a value, the bind collapses to running the outer
continuation under the original WP body. -/
example (E : CoPset) (v : Val) (K : Ectx) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w =>
        tglWp E (K.fill (.ofVal w)) (fun w' => iprop(⌜w' = v⌝))) -∗
      tglWp E (K.fill (Exp.ofVal v)) (fun w' => iprop(⌜w' = v⌝)) := by
  iintro HW
  iapply tglWp_bind_value
  iexact HW

/-- `ec_induction`: error-amplification induction (intuitionistic-wand form
re-exported from `ErrorCredit.Induction.increasing`). Demonstrates the
chain that geometric_total uses: from a persistent rule "given a bigger
credit `↯ε'` and the current credit `↯ε`, prove P", get `↯ε ⊢ P`. -/
example (ε : ENNReal) (ε' : NNReal) (P : IProp GF)
    (hε : 0 < ε) (hε' : ε < ε') :
    ⊢@{IProp GF} iprop(□ ((↯(ε' : ENNReal) -∗ P) ∗ ↯ε -∗ P)) -∗ iprop(↯ε -∗ P) := by
  iintro Hamp
  iapply (ec_induction hε hε')
  iexact Hamp

/-- `tglWp_bind`: full evaluation-context bind. -/
example (E : CoPset) (e : Exp) (K : Ectx) (φ : Val → Prop) :
    ⊢@{IProp GF} tglWp E e (fun v =>
        tglWp E (K.fill (.ofVal v)) (fun w => iprop(⌜φ w⌝))) -∗
      tglWp E (K.fill e) (fun w => iprop(⌜φ w⌝)) := by
  iintro HW
  iapply tglWp_bind
  iexact HW

/-- Worked example: `(λ x. !x) (alloc v) ⇓ v`.

Steps:
1. `tglWp_bind` with `K = [appR (λ. !0)]` to focus on the inner `alloc v`.
2. `twp_alloc` allocates and yields `l ↦ v`.
3. Beta-reduce `(λ. !0) #l` to `!#l` (a single pure step).
4. `twp_load` reads `v` from the heap.
5. Conclude `w = v`. -/
example (E : CoPset) (v : Val) :
    ⊢@{IProp GF} tglWp E
      (Exp.app (Exp.lam (Exp.load (Exp.bvar 0))) (Exp.alloc (Exp.ofVal v)))
      (fun w => iprop(⌜w = v⌝)) := by
  -- Rewrite the program as `K.fill (alloc v)` so `tglWp_bind` can fire.
  let K : Ectx := [EctxItem.appR (Exp.lam (Exp.load (Exp.bvar 0)))]
  show ⊢@{IProp GF} tglWp E (K.fill (Exp.alloc (Exp.ofVal v))) _
  iapply tglWp_bind
  iapply twp_alloc
  iintro %l Hl
  -- After `tglWp_bind` + `twp_alloc`, the continuation runs on the filled
  -- expression `K.fill (#l-val) = (λ. !0) #l-val`. Unfold `K.fill`.
  simp only [K, Ectx.fill, List.foldl, flip, EctxItem.fillItem]
  -- Beta-reduce: `(λ. !0) #l ↦ !#l` via the `pureExec_app_lam` instance.
  -- The bare `twp_pure` macro can't fire here (metavariables in φ block
  -- typeclass search); pin args explicitly.
  iapply (ErisWpGS.twp_pure_step_fupd (n := 1)
    (e₁ := Exp.app (Exp.lam (Exp.load (Exp.bvar 0)))
      (Exp.ofVal ⟨.lit (.loc l), IsVal.lit⟩))
    (e₂ := Exp.open' (Exp.load (Exp.bvar 0))
      (Exp.ofVal ⟨.lit (.loc l), IsVal.lit⟩))
    (Exp.ofVal ⟨.lit (.loc l), IsVal.lit⟩).isValue ⟨IsVal.lit⟩)
  -- The opened body `(load 0).open' #l` reduces to `load (loc l)`.
  simp only [Exp.open', Exp.openRec, Exp.ofVal, ↓reduceIte]
  iapply twp_load
  isplitl [Hl]; · iexact Hl
  iintro _
  ipure_intro; rfl

/-- `fupd_tglWp`: a leading `|={E}=>` on a tglWp is absorbed. -/
example (E : CoPset) (v : Val) :
    ⊢@{IProp GF} iprop(|={E}=> tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝))) -∗
      tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) := by
  iintro HW
  iapply fupd_tglWp
  iexact HW

/-- `tglWp_frame_l`: frame a (spatial) resource. -/
example (E : CoPset) (v : Val) (R : Prop) (HR : R) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) -∗
      tglWp E (.ofVal v) (fun w => iprop(⌜R⌝ ∗ ⌜w = v⌝)) := by
  iintro HW
  iapply tglWp_frame_l (R := iprop(⌜R⌝))
  isplitr [HW]; swap; · iexact HW
  ipure_intro; exact HR

end TotalEris
end ProbLang
