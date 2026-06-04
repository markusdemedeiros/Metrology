module

public import Metrology.ProbLang.CoreMeasures.Exp
public import Metrology.ProbLang.CoreMeasures.Val
public import Metrology.ProbLang.CoreMeasures.EctxItem

@[expose] public section

/-!
# Measurability stamps for recursive functions on `Exp`

This file contains real-implementation stamps: applications of the recursive
measurability keystone (`Exp.measurable_struct_rec` / `Exp.measurable_struct_rec_param`,
from `CoreMeasures.Exp`) to actual ProbLang functions defined in `Syntax`.

Each stamp follows a uniform pattern:

```
theorem foo.measurable : Measurable (uncurried foo) := by
  apply measurable_struct_rec_param (g := ...)
    (c_X := ...)  -- 22 combinators, one per Exp constructor
    ...
  all_goals first | (intros; rfl) | fun_prop
```

Only param-dependent combinators (those that genuinely use the threaded `b`)
require manual measurability work. Everything else closes by `fun_prop` using
the `@[fun_prop]`-tagged raw-constructor measurability lemmas in `CoreMeasures.Exp`.
-/

noncomputable section ProbLangMeasures

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace ProbLang.Exp

/-! ### Smoke test: `Exp.height` is measurable.

Discrete codomain (`Nat`); all combinators close by `fun_prop`. -/

theorem height.measurable [MeasurableSpace rT] :
    Measurable (Exp.height : Exp rT → Nat) := by
  apply measurable_struct_rec (f := Exp.height)
    (c_bvar := fun _ => 1)
    (c_fvar := fun _ => 1)
    (c_lit  := fun _ => 1)
    (c_lam  := fun n => 1 + n)
    (c_fix  := fun n => 1 + n)
    (c_app  := fun n1 n2 => 1 + n1 + n2)
    (c_unop := fun _ n => 1 + n)
    (c_binop := fun _ n1 n2 => 1 + n1 + n2)
    (c_cond := fun n0 n1 n2 => 1 + n0 + n1 + n2)
    (c_pair := fun n1 n2 => 1 + n1 + n2)
    (c_fst  := fun n => 1 + n)
    (c_snd  := fun n => 1 + n)
    (c_inl  := fun n => 1 + n)
    (c_inr  := fun n => 1 + n)
    (c_case := fun n0 n1 n2 => 1 + n0 + n1 + n2)
    (c_alloc := fun n => 1 + n)
    (c_load := fun n => 1 + n)
    (c_store := fun n1 n2 => 1 + n1 + n2)
    (c_tape := fun n => 1 + n)
    (c_rand := fun n1 n2 => 1 + n1 + n2)
    (c_fail := 1)
    (c_scrut := fun n _ => 1 + n)
  all_goals first | (intros; rfl) | fun_prop

/-! ### `Exp.subst` — fixed-parameter version.

`Exp.subst e x sub` recurses on `e` with `(x, sub)` carried unchanged. For fixed
`(x, sub)`, this is plain structural recursion — directly applicable to the
non-param keystone with codomain `Exp rT` (non-discrete). -/

theorem subst.measurable_fixed [MeasurableSpace rT] (x : Var) (sub : Exp rT) :
    Measurable (fun e : Exp rT => Exp.subst e x sub) := by
  apply measurable_struct_rec (f := fun e => Exp.subst e x sub)
    (c_bvar  := fun j => Exp.bvar j)
    (c_fvar  := fun y => if x = y then sub else Exp.fvar y)
    (c_lit   := fun b => Exp.lit b)
    (c_lam   := fun e => Exp.lam e)
    (c_fix   := fun e => Exp.fix e)
    (c_app   := fun e1 e2 => Exp.app e1 e2)
    (c_unop  := fun op e => Exp.unop op e)
    (c_binop := fun op e1 e2 => Exp.binop op e1 e2)
    (c_cond  := fun ec et ef => Exp.cond ec et ef)
    (c_pair  := fun e1 e2 => Exp.pair e1 e2)
    (c_fst   := fun e => Exp.fst e)
    (c_snd   := fun e => Exp.snd e)
    (c_inl   := fun e => Exp.inl e)
    (c_inr   := fun e => Exp.inr e)
    (c_case  := fun ec el er => Exp.case ec el er)
    (c_alloc := fun e => Exp.alloc e)
    (c_load  := fun e => Exp.load e)
    (c_store := fun e1 e2 => Exp.store e1 e2)
    (c_tape  := fun e => Exp.tape e)
    (c_rand  := fun e1 e2 => Exp.rand e1 e2)
    (c_fail  := Exp.fail)
    (c_scrut := fun e p => Exp.scrut e p)
  all_goals first | (intros; rfl) | fun_prop

/-! ### `Exp.subst` — joint measurability.

Stamped via `measurable_struct_rec_param` with `β := Var × Exp rT`. The `(x, sub)`
pair is carried through every recursive call. Only `c_fvar` actually uses `b` to
embed `sub`; all other combinators ignore `b` and just rebuild constructors. -/

theorem subst.measurable [MeasurableSpace rT] :
    Measurable (fun (q : (Var × Exp rT) × Exp rT) => Exp.subst q.2 q.1.1 q.1.2) := by
  apply measurable_struct_rec_param (g := fun (b : Var × Exp rT) (e : Exp rT) => Exp.subst e b.1 b.2)
    (c_bvar  := fun _ j => Exp.bvar j)
    (c_fvar  := fun b y => if b.1 = y then b.2 else Exp.fvar y)
    (c_lit   := fun _ l => Exp.lit l)
    (c_lam   := fun _ e' => Exp.lam e')
    (c_fix   := fun _ e' => Exp.fix e')
    (c_app   := fun _ e1' e2' => Exp.app e1' e2')
    (c_unop  := fun _ op e' => Exp.unop op e')
    (c_binop := fun _ op e1' e2' => Exp.binop op e1' e2')
    (c_cond  := fun _ ec' et' ef' => Exp.cond ec' et' ef')
    (c_pair  := fun _ e1' e2' => Exp.pair e1' e2')
    (c_fst   := fun _ e' => Exp.fst e')
    (c_snd   := fun _ e' => Exp.snd e')
    (c_inl   := fun _ e' => Exp.inl e')
    (c_inr   := fun _ e' => Exp.inr e')
    (c_case  := fun _ ec' el' er' => Exp.case ec' el' er')
    (c_alloc := fun _ e' => Exp.alloc e')
    (c_load  := fun _ e' => Exp.load e')
    (c_store := fun _ e1' e2' => Exp.store e1' e2')
    (c_tape  := fun _ e' => Exp.tape e')
    (c_rand  := fun _ e1' e2' => Exp.rand e1' e2')
    (c_fail  := fun _ => Exp.fail)
    (c_scrut := fun _ e' p => Exp.scrut e' p)
  -- All 22 equations close by rfl. All combinator measurabilities close by fun_prop
  -- EXCEPT c_fvar which has a Var-dependent if. We discharge it manually.
  case h_fvar =>
    have : Function.uncurry (fun (b : Var × Exp rT) (y : Var) =>
              if b.1 = y then b.2 else (Exp.fvar y : Exp rT))
        = (fun (q : (Var × Var) × Exp rT) =>
              if q.1.1 = q.1.2 then q.2 else Exp.fvar q.1.2)
            ∘ (fun (p : (Var × Exp rT) × Var) => ((p.1.1, p.2), p.1.2)) := by
      funext ⟨⟨x, sub⟩, y⟩; rfl
    rw [this]
    have h1 : Measurable (fun (q : (Var × Var) × Exp rT) =>
                if q.1.1 = q.1.2 then q.2 else (Exp.fvar q.1.2 : Exp rT)) := by
      apply measurable_from_prod_countable_right
      intro xy
      by_cases hxy : xy.1 = xy.2
      · simp only [hxy, if_true]; exact measurable_id
      · simp only [hxy, if_false]; exact measurable_const
    exact h1.comp (by fun_prop : Measurable
      (fun (p : (Var × Exp rT) × Var) => ((p.1.1, p.2), p.1.2)))
  all_goals first | (intros; rfl) | fun_prop

/-! ### `Exp.isValueR` — Prop-valued recursive value predicate. -/

theorem isValueR.measurable [MeasurableSpace rT] :
    Measurable (Exp.isValueR : Exp rT → Prop) := by
  apply measurable_struct_rec (f := Exp.isValueR)
    (c_bvar  := fun _ => False)
    (c_fvar  := fun _ => False)
    (c_lit   := fun _ => True)
    (c_lam   := fun _ => True)
    (c_fix   := fun _ => True)
    (c_app   := fun _ _ => False)
    (c_unop  := fun _ _ => False)
    (c_binop := fun _ _ _ => False)
    (c_cond  := fun _ _ _ => False)
    (c_pair  := fun b1 b2 => b1 ∧ b2)
    (c_fst   := fun _ => False)
    (c_snd   := fun _ => False)
    (c_inl   := fun b => b)
    (c_inr   := fun b => b)
    (c_case  := fun _ _ _ => False)
    (c_alloc := fun _ => False)
    (c_load  := fun _ => False)
    (c_store := fun _ _ => False)
    (c_tape  := fun _ => False)
    (c_rand  := fun _ _ => False)
    (c_fail  := False)
    (c_scrut := fun _ _ => False)
  all_goals first | (intros; rfl) | fun_prop

/-! ### `Exp.fv` — free variables. Discrete codomain (`Finset Var`). -/

/-- Discrete σ-algebra on `Finset Var` (since `Var` and `Finset` are countable). -/
instance : MeasurableSpace (Finset Var) := ⊤

theorem fv.measurable [MeasurableSpace rT] : Measurable (Exp.fv : Exp rT → Finset Var) := by
  apply measurable_struct_rec (f := Exp.fv)
    (c_bvar  := fun _ => {})
    (c_fvar  := fun x => {x})
    (c_lit   := fun _ => {})
    (c_lam   := fun s => s)
    (c_fix   := fun s => s)
    (c_app   := fun s1 s2 => s1 ∪ s2)
    (c_unop  := fun _ s => s)
    (c_binop := fun _ s1 s2 => s1 ∪ s2)
    (c_cond  := fun s0 s1 s2 => s0 ∪ s1 ∪ s2)
    (c_pair  := fun s1 s2 => s1 ∪ s2)
    (c_fst   := fun s => s)
    (c_snd   := fun s => s)
    (c_inl   := fun s => s)
    (c_inr   := fun s => s)
    (c_case  := fun s0 s1 s2 => s0 ∪ s1 ∪ s2)
    (c_alloc := fun s => s)
    (c_load  := fun s => s)
    (c_store := fun s1 s2 => s1 ∪ s2)
    (c_tape  := fun s => s)
    (c_rand  := fun s1 s2 => s1 ∪ s2)
    (c_fail  := {})
    (c_scrut := fun s _ => s)
  all_goals first | (intros; rfl) | fun_prop

/-! ### `UnOp.eval`, `BinOp.eval` — nested non-recursive pattern matches.

`UnOp` and `BinOp` are discrete (`⊤` σ-algebras), so splitting over them via
`measurable_from_prod_countable_left` is easy. The wrinkle: each fiber is a
function `Exp α → Option (Exp α)` that pattern-matches not just on the outer `Exp`
constructor but ALSO on the inner `BaseLit` constructor (e.g., `neg (Exp.lit
(.bool b)) = some ...`). That's a **chained two-level pattern match** that needs
`Exp.measurable_rec` composed with `BaseLit.measurable_rec` at the `lit` branch.

The composition isn't quite mechanical because the inner `measurable_rec` lives
under a constructor-projection. Doable but real work; left as stub. -/

theorem UnOp_eval.measurable [MeasurableSpace rT] :
    Measurable (Function.uncurry (UnOp.eval (α := rT))) := by
  sorry

theorem BinOp_eval.measurable [ProbLangℝ rT] :
    Measurable (fun (q : BinOp × Exp rT × Exp rT) => BinOp.eval q.1 q.2.1 q.2.2) := by
  sorry

/-! ### `EctxItem.fillItem` — joint measurability over `EctxItem × Exp`.

`EctxItem.fillItem Ki e` does a `casesOn` on `Ki` (one-level), wrapping `e` (and
possibly an existing payload) in a fresh `Exp` constructor. Since `EctxItem`
carries non-discrete payloads (`Val α`, `Exp α`), we cannot split over `EctxItem`
discretely. Instead we'd need a `param`-style joint keystone on `EctxItem` —
analogous to `measurable_struct_rec_param` on `Exp`, but for `EctxItem`'s
non-recursive structure.

**Status**: stubbed pending a joint `EctxItem`-based keystone (or, equivalently,
using `cell_*_param` helpers from `Measure.lean` directly on `EctxItem.shape`). -/

theorem fillItem.measurable [MeasurableSpace rT] :
    Measurable (fun (q : EctxItem rT × Exp rT) => q.1.fillItem q.2) := by
  sorry

/-! ### `Ectx.fill` — `List.foldl` over `EctxItem.fillItem`.

Measurable once `EctxItem.fillItem`'s joint version is. Standard `List.foldl`
measurability argument; mechanical extension once the input is measurable. -/

theorem Ectx_fill.measurable [MeasurableSpace rT] :
    Measurable (fun (q : Ectx rT × Exp rT) => Ectx.fill q.1 q.2) := by
  sorry

/-! ### `Exp.openRec` — binder-shifting recursion.

`Exp.openRec i sub e` recurses on `e` with `(i, sub)` carried through, but the `i`
component is *incremented* at `lam` and `fix` binders. This is **binder-transforming
param-threading**, which the current keystone (`measurable_struct_rec_param`) does
not support — it carries `b` unchanged through every recursive call.

To stamp `openRec`, the keystone needs an extension allowing per-constructor
parameter transformers `t_X : β → β`. The proof structure is identical to the
current keystone with one extra `t_X b`-precomposition at each constructor.

**Status**: stubbed pending the binder-transforming variant. -/

theorem openRec.measurable [MeasurableSpace rT] :
    Measurable (fun (q : (Nat × Exp rT) × Exp rT) => Exp.openRec q.1.1 q.1.2 q.2) := by
  sorry

theorem open'.measurable [MeasurableSpace rT] :
    Measurable (fun (q : Exp rT × Exp rT) => Exp.open' q.1 q.2) := by
  -- open' e sub = openRec 0 sub e. Trivial composition once openRec.measurable lands.
  sorry

theorem closeRec.measurable [MeasurableSpace rT] :
    Measurable (fun (q : (Nat × Var) × Exp rT) => Exp.closeRec q.1.1 q.1.2 q.2) := by
  -- Same shape as openRec: binder-shifting param thread.
  sorry

theorem close.measurable [MeasurableSpace rT] :
    Measurable (fun (q : Exp rT × Var) => Exp.close q.1 q.2) := by
  -- close e x = closeRec 0 x e. Trivial composition once closeRec.measurable lands.
  sorry

-- Local instances for stub statements (these likely already exist downstream;
-- duplicated here to make the stub theorems type-check).
attribute [local instance] Classical.propDecidable

instance instLocalOption [MeasurableSpace α] : MeasurableSpace (Option α) :=
  MeasurableSpace.comap (Equiv.optionEquivSumPUnit.{0, _} α) inferInstance

/-! ### `IsVal.check?` — dependently-typed recursion.

`IsVal.check? : (e : Exp rT) → Option (IsVal e)` has a return type that depends on
the input. The keystone framework requires a fixed codomain `α`, so it doesn't apply.

**Workarounds**: (a) prove `Exp.toVal? : Exp rT → Option (Val rT)` directly via
structural recursion (codomain *is* fixed) without going through `IsVal.check?`;
(b) construct an ad-hoc proof using the fact that `IsVal e` is a subsingleton.

**Status**: stubbed; needs a bespoke argument outside the keystone. -/

/-! ### `Exp.toVal?` — depends on `IsVal.check?`.

Defined as a one-step destruct on `IsVal.check?`'s output, not structurally recursive
on `Exp` itself. Could be re-derived as a structural fold returning `Option (Val rT)`,
which would fit the keystone — but the existing definition routes through
`IsVal.check?`, so its measurability is contingent.

**Status**: stubbed; needs either (a) the re-derivation, or (b) `IsVal.check?` measurable. -/

theorem toVal_question.measurable [MeasurableSpace rT] :
    let _ : MeasurableSpace (Option (Val rT)) := instLocalOption
    Measurable (Exp.toVal? : Exp rT → Option (Val rT)) := by
  intro _; sorry

/-! ### `Exp.decompItem` — depends on `Exp.toVal?`. -/

theorem decompItem.measurable [MeasurableSpace rT] :
    let _ : MeasurableSpace (Option (EctxItem rT × Exp rT)) := instLocalOption
    Measurable (Exp.decompItem : Exp rT → Option (EctxItem rT × Exp rT)) := by
  -- One-level `casesOn` on Exp, but each branch uses `toVal?` on the children.
  -- Measurable once `toVal?.measurable` is established.
  intro _; sorry

/-! ### `Exp.decomp` — well-founded recursion.

`Exp.decomp` uses `decreasing_by Exp.decompItem_height`. Not structural recursion;
outside the keystone's scope. Standard approach: induct on `Exp.height ≤ n` and
take a union over `n`.

**Status**: stubbed pending a well-founded-recursion measurability lemma. -/

theorem decomp.measurable [MeasurableSpace rT] :
    Measurable (Exp.decomp : Exp rT → Ectx rT × Exp rT) := by
  sorry

/-! ### `Pat.tryMatch` — 2D joint recursion.

`Pat.tryMatch p e` recurses on BOTH `p : Pat rT` AND `e : Exp rT` simultaneously
(it matches paired constructors `(.pair p1 p2, .pair e1 e2)` etc.). The keystone
recursesonly on the first inductive; this is a "product-recursion" we don't yet
support.

**Workaround**: define `tryMatch` as recursion on `p` alone with `e` as a parameter,
then it fits the param keystone. The current definition pattern-matches on both
simultaneously, so this would need restating.

**Status**: stubbed pending the restatement or a joint-recursion keystone. -/

theorem tryMatch.measurable [ProbLangℝ rT] :
    Measurable (fun (q : Pat rT × Exp rT) => Pat.tryMatch q.1 q.2) := by
  sorry

end Exp
end ProbLang
end ProbLangMeasures
