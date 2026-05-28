module

public import Metrology.ProbLang.HeadStep
public import Metrology.ProbLang.CtxStep

@[expose] public section

/-!
# Atomic Expressions

An expression `e` is `Atomic` if every primitive step from `e` lands in a value.
This is the syntactic/physical flavor of atomicity — used to discharge the
logical-atomicity predicate `OpenInv` (in `Metrology/Approxis/OpenInv.lean`)
that invariant-opening WP rules actually require.

Mirrors Rocq's `Atomic StronglyAtomic e` from Iris's `program_logic/atomic.v`.

## Design

- `Atomic e` — syntactic predicate: every prim-step reduces to a value.
- Instances for the atomic ops that ProbLang's Compatibility needs:
  `store`, `load`, `alloc`, `rand`.
- Separately (in `OpenInv.lean`), `Atomic e → OpenInv e` lifts to the
  fupd-shift-around-single-step capability needed by `wp_atomic`.

This layering leaves room for `OpenInv` instances coming from logical
atomicity proofs for non-syntactically-atomic programs (a future extension).
-/

namespace ProbLang

set_option linter.unusedSectionVars false

variable {rT : Type _} [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]

/-- `Atomic e` — every primitive step from `e` (at any state) reduces to a
configuration whose expression is a value. This is the strong/physical flavor
of atomicity. -/
def Atomic (e : Exp rT) : Prop :=
  ∀ σ e' σ', 0 < primStep ⟨e, σ⟩ {⟨e', σ'⟩} → e'.isValue

namespace Atomic

/-! ## Helper: primStep-to-headStep bridge for redex-like expressions

For an expression `e` whose `decompItem = none` (i.e., it's a head-redex shape),
`primStep ⟨e, σ⟩ = headStep ⟨e, σ⟩` always, regardless of whether the headStep
is positive. This lets us invert primStep positivity case-by-case via
`HeadStepSupport`. -/
theorem primStep_eq_headStep_of_decomp_nil
    {e : Exp rT} (hd : e.decompItem = none) (σ : State rT) :
    primStep ⟨e, σ⟩ = headStep ⟨e, σ⟩ := by
  have hde : e.decomp = ([], e) := by
    rw [Exp.decomp_unfold, hd]
  simp only [primStep, hde, Ectx.fillCfg_empty, MeasureTheory.Measure.map_id]

/-! ## Instances for the ops used by Compatibility -/

/-- `load (.lit (.loc l))` is atomic: it produces either `0 mass` (lookup fails)
or a dirac at a value. -/
theorem load (l : Loc) : Atomic (rT := rT) (.load (.lit (.loc l))) := by
  intro σ e' σ' hpos
  have hd : (Exp.load (.lit (.loc l)) : Exp rT).decompItem = none := rfl
  rw [primStep_eq_headStep_of_decomp_nil hd, headStep_support_iff] at hpos
  cases hpos with
  | LoadS _ he' =>
    -- he' : e' = Exp.ofVal v. Exp.ofVal v = v.1, which is a value.
    rename_i v _
    subst he'
    exact v.2.toIsValue

/-- `store (.lit (.loc l)) v` is atomic when `v` is a value: result is always
`.lit .unit`. -/
theorem store (l : Loc) (v : Val rT) :
    Atomic (.store (.lit (.loc l)) v.1) := by
  intro σ e' σ' hpos
  have hv : v.1.toVal? = some v := Exp.toVal?_ofVal v
  -- For `.store (.lit (.loc l)) v.1`, decompItem cases on both children's toVal?.
  -- Both are values, so the result is `none`.
  have hd : (Exp.store (.lit (.loc l)) v.1).decompItem = none := by
    show (v.1.toVal?.casesOn _ _ : Option _) = none
    rw [hv]
    rfl
  rw [primStep_eq_headStep_of_decomp_nil hd, headStep_support_iff] at hpos
  cases hpos with
  | StoreS _ _ _ => exact IsVal.lit.toIsValue

/-- `alloc v` is atomic when `v` is a value: result is always `.lit (.loc ℓ)`. -/
theorem alloc (v : Val rT) : Atomic (.alloc v.1) := by
  intro σ e' σ' hpos
  have hv : v.1.toVal? = some v := Exp.toVal?_ofVal v
  have hd : (Exp.alloc v.1).decompItem = none := by
    show (v.1.toVal?.casesOn _ _ : Option _) = none
    rw [hv]
  rw [primStep_eq_headStep_of_decomp_nil hd, headStep_support_iff] at hpos
  cases hpos with
  | AllocS _ _ _ => exact IsVal.lit.toIsValue

/-- `rand z ()` is atomic: result is always `.lit (.int n)`. -/
theorem rand_unit (z : Int) : Atomic (rT := rT) (.rand (.lit (.int z)) (.lit .unit)) := by
  intro σ e' σ' hpos
  have hd : (Exp.rand (.lit (.int z)) (.lit .unit) : Exp rT).decompItem = none := rfl
  rw [primStep_eq_headStep_of_decomp_nil hd, headStep_support_iff] at hpos
  cases hpos with
  | RandNoTapeS _ _ _ => exact IsVal.lit.toIsValue
  | RandNonposS _ => exact IsVal.lit.toIsValue

/-- `rand z (lbl l)` is atomic: result is always `.lit (.int n)`. -/
theorem rand_lbl (z : Int) (l : Loc) :
    Atomic (rT := rT) (.rand (.lit (.int z)) (.lit (.lbl l))) := by
  intro σ e' σ' hpos
  have hd : (Exp.rand (.lit (.int z)) (.lit (.lbl l)) : Exp rT).decompItem = none := rfl
  rw [primStep_eq_headStep_of_decomp_nil hd, headStep_support_iff] at hpos
  cases hpos with
  | RandTapeS _ _ _ _ => exact IsVal.lit.toIsValue
  | RandTapeEmptyS _ _ _ _ _ _ => exact IsVal.lit.toIsValue
  | RandTapeOtherS _ _ _ _ _ _ => exact IsVal.lit.toIsValue
  | RandTapeNonposEmptyS _ _ _ => exact IsVal.lit.toIsValue
  | RandTapeNonposOtherS _ _ _ => exact IsVal.lit.toIsValue

end Atomic

end ProbLang
