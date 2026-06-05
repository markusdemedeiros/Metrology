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

/-- Top σ-algebra trivially has measurable singletons. -/
instance instMeasurableSingletonClassUnOp : MeasurableSingletonClass UnOp where
  measurableSet_singleton _ := trivial

/-- Top σ-algebra trivially has measurable singletons. -/
instance instMeasurableSingletonClassBinOp : MeasurableSingletonClass BinOp where
  measurableSet_singleton _ := trivial

/-- For each fixed `op : UnOp`, the function `v ↦ UnOp.eval op v` is measurable.
This is a nested two-level pattern match: outer on `v : Exp rT` via
`Exp.measurable_rec`, inner on `BaseLit rT` (in the `.lit` branch) via
`BaseLit.measurable_rec`. -/
theorem UnOp.eval_op_measurable [MeasurableSpace rT] [Inhabited rT] (op : UnOp) :
    Measurable (fun v : Exp rT => UnOp.eval op v) := by
  -- Unfold `UnOp.eval op` into `Exp.casesOn` form, then apply `measurable_rec`.
  -- The only non-constant branches are `.lit`, which inner-recurses on `BaseLit`.
  cases op with
  | neg =>
    have heq : (fun v : Exp rT => UnOp.eval .neg v) = fun v : Exp rT =>
        Exp.casesOn (motive := fun _ => Option (Exp rT)) v
          (fun _ => none) (fun _ => none)
          (fun l => BaseLit.casesOn (motive := fun _ => Option (Exp rT)) l
            (fun _ => none) (fun b => some (.lit (.bool ¬b))) none
            (fun _ => none) (fun _ => none) (fun _ => none))
          (fun _ => none) (fun _ => none)
          (fun e1 e2 => (fun _ : Exp rT × Exp rT => none) (e1, e2))
          (fun u e => (fun _ : UnOp × Exp rT => none) (u, e))
          (fun b e1 e2 => (fun _ : BinOp × Exp rT × Exp rT => none) (b, e1, e2))
          (fun ec et ef => (fun _ : Exp rT × Exp rT × Exp rT => none) (ec, et, ef))
          (fun e1 e2 => (fun _ : Exp rT × Exp rT => none) (e1, e2))
          (fun _ => none) (fun _ => none) (fun _ => none) (fun _ => none)
          (fun ec el er => (fun _ : Exp rT × Exp rT × Exp rT => none) (ec, el, er))
          (fun _ => none) (fun _ => none)
          (fun e1 e2 => (fun _ : Exp rT × Exp rT => none) (e1, e2))
          (fun _ => none)
          (fun e1 e2 => (fun _ : Exp rT × Exp rT => none) (e1, e2))
          ((fun _ : Unit => none) ())
          (fun e p => (fun _ : Exp rT × Pat rT => none) (e, p)) := by
      funext v
      cases v <;> simp [UnOp.eval]
      rename_i b; cases b <;> simp [UnOp.eval]
    rw [heq]
    apply Exp.measurable_rec (rT := rT)
      (f_bvar := fun _ => none) (f_fvar := fun _ => none)
      (f_lit := fun l => BaseLit.casesOn (motive := fun _ => Option (Exp rT)) l
        (fun _ => none) (fun b => some (Exp.lit (.bool ¬b))) none
        (fun _ => none) (fun _ => none) (fun _ => none))
      (f_lam := fun _ => none) (f_fix := fun _ => none)
      (f_app := fun _ => none) (f_unop := fun _ => none) (f_binop := fun _ => none)
      (f_cond := fun _ => none) (f_pair := fun _ => none)
      (f_fst := fun _ => none) (f_snd := fun _ => none)
      (f_inl := fun _ => none) (f_inr := fun _ => none)
      (f_case := fun _ => none)
      (f_alloc := fun _ => none) (f_load := fun _ => none) (f_store := fun _ => none)
      (f_tape := fun _ => none) (f_rand := fun _ => none)
      (f_fail := fun _ => none) (f_scrut := fun _ => none)
    · apply BaseLit.measurable_rec
        (f_int := fun _ => none) (f_bool := fun b => some (Exp.lit (.bool ¬b)))
        (f_unit := fun _ => none) (f_loc := fun _ => none) (f_lbl := fun _ => none)
        (f_real := fun _ => none)
      exact measurable_const
    all_goals exact measurable_const
  | minus =>
    have heq : (fun v : Exp rT => UnOp.eval .minus v) = fun v : Exp rT =>
        Exp.casesOn (motive := fun _ => Option (Exp rT)) v
          (fun _ => none) (fun _ => none)
          (fun l => BaseLit.casesOn (motive := fun _ => Option (Exp rT)) l
            (fun z => some (.lit (.int z.neg))) (fun _ => none) none
            (fun _ => none) (fun _ => none) (fun _ => none))
          (fun _ => none) (fun _ => none)
          (fun e1 e2 => (fun _ : Exp rT × Exp rT => none) (e1, e2))
          (fun u e => (fun _ : UnOp × Exp rT => none) (u, e))
          (fun b e1 e2 => (fun _ : BinOp × Exp rT × Exp rT => none) (b, e1, e2))
          (fun ec et ef => (fun _ : Exp rT × Exp rT × Exp rT => none) (ec, et, ef))
          (fun e1 e2 => (fun _ : Exp rT × Exp rT => none) (e1, e2))
          (fun _ => none) (fun _ => none) (fun _ => none) (fun _ => none)
          (fun ec el er => (fun _ : Exp rT × Exp rT × Exp rT => none) (ec, el, er))
          (fun _ => none) (fun _ => none)
          (fun e1 e2 => (fun _ : Exp rT × Exp rT => none) (e1, e2))
          (fun _ => none)
          (fun e1 e2 => (fun _ : Exp rT × Exp rT => none) (e1, e2))
          ((fun _ : Unit => none) ())
          (fun e p => (fun _ : Exp rT × Pat rT => none) (e, p)) := by
      funext v
      cases v <;> simp [UnOp.eval]
      rename_i b; cases b <;> simp [UnOp.eval]
    rw [heq]
    apply Exp.measurable_rec (rT := rT)
      (f_bvar := fun _ => none) (f_fvar := fun _ => none)
      (f_lit := fun l => BaseLit.casesOn (motive := fun _ => Option (Exp rT)) l
        (fun z => some (Exp.lit (.int z.neg))) (fun _ => none) none
        (fun _ => none) (fun _ => none) (fun _ => none))
      (f_lam := fun _ => none) (f_fix := fun _ => none)
      (f_app := fun _ => none) (f_unop := fun _ => none) (f_binop := fun _ => none)
      (f_cond := fun _ => none) (f_pair := fun _ => none)
      (f_fst := fun _ => none) (f_snd := fun _ => none)
      (f_inl := fun _ => none) (f_inr := fun _ => none)
      (f_case := fun _ => none)
      (f_alloc := fun _ => none) (f_load := fun _ => none) (f_store := fun _ => none)
      (f_tape := fun _ => none) (f_rand := fun _ => none)
      (f_fail := fun _ => none) (f_scrut := fun _ => none)
    · apply BaseLit.measurable_rec
        (f_int := fun z => some (Exp.lit (.int z.neg))) (f_bool := fun _ => none)
        (f_unit := fun _ => none) (f_loc := fun _ => none) (f_lbl := fun _ => none)
        (f_real := fun _ => none)
      exact measurable_const
    all_goals exact measurable_const

theorem UnOp_eval.measurable [MeasurableSpace rT] [Inhabited rT] :
    Measurable (Function.uncurry (UnOp.eval (α := rT))) := by
  -- `UnOp × Exp rT → Option (Exp rT)`. `UnOp` is Countable + has `⊤` σ-alg
  -- (hence `MeasurableSingletonClass`). Split over it via `_right` form.
  apply measurable_from_prod_countable_right
  intro op
  exact UnOp.eval_op_measurable op

/-! (`BinOp_eval.measurable` is proved below in this file, after the
`liftII`/`liftBB`/`liftIB`/`liftEq` family is in scope.) -/

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
  -- Apply the joint param keystone with `β := Exp rT`, parameter = `q.2`.
  -- Each `f_<ctor>` is built from measurable Exp constructors + `Val.fst`/`Exp.ofVal`.
  -- First rewrite `fillItem` as the explicit `casesOn` form expected by the keystone.
  have heq : (fun q : EctxItem rT × Exp rT => q.1.fillItem q.2) = fun p : EctxItem rT × Exp rT =>
      EctxItem.casesOn (motive := fun _ => Exp rT) p.1
        (fun v => (fun pp : Exp rT × Val rT => Exp.app pp.1 (Exp.ofVal pp.2)) (p.2, v))
        (fun e => (fun pp : Exp rT × Exp rT => Exp.app pp.2 pp.1) (p.2, e))
        (fun u => (fun pp : Exp rT × UnOp => Exp.unop pp.2 pp.1) (p.2, u))
        (fun op v => (fun pp : Exp rT × BinOp × Val rT => Exp.binop pp.2.1 pp.1 (Exp.ofVal pp.2.2)) (p.2, op, v))
        (fun op e => (fun pp : Exp rT × BinOp × Exp rT => Exp.binop pp.2.1 pp.2.2 pp.1) (p.2, op, e))
        (fun e₁ e₂ => (fun pp : Exp rT × Exp rT × Exp rT => Exp.cond pp.1 pp.2.1 pp.2.2) (p.2, e₁, e₂))
        (fun v => (fun pp : Exp rT × Val rT => Exp.pair pp.1 (Exp.ofVal pp.2)) (p.2, v))
        (fun e => (fun pp : Exp rT × Exp rT => Exp.pair pp.2 pp.1) (p.2, e))
        ((fun pp : Exp rT × Unit => Exp.fst pp.1) (p.2, ()))
        ((fun pp : Exp rT × Unit => Exp.snd pp.1) (p.2, ()))
        ((fun pp : Exp rT × Unit => Exp.inl pp.1) (p.2, ()))
        ((fun pp : Exp rT × Unit => Exp.inr pp.1) (p.2, ()))
        (fun e₁ e₂ => (fun pp : Exp rT × Exp rT × Exp rT => Exp.case pp.1 pp.2.1 pp.2.2) (p.2, e₁, e₂))
        ((fun pp : Exp rT × Unit => Exp.alloc pp.1) (p.2, ()))
        ((fun pp : Exp rT × Unit => Exp.load pp.1) (p.2, ()))
        (fun v => (fun pp : Exp rT × Val rT => Exp.store pp.1 (Exp.ofVal pp.2)) (p.2, v))
        (fun e => (fun pp : Exp rT × Exp rT => Exp.store pp.2 pp.1) (p.2, e))
        ((fun pp : Exp rT × Unit => Exp.tape pp.1) (p.2, ()))
        (fun v => (fun pp : Exp rT × Val rT => Exp.rand pp.1 (Exp.ofVal pp.2)) (p.2, v))
        (fun e => (fun pp : Exp rT × Exp rT => Exp.rand pp.2 pp.1) (p.2, e))
        (fun pat => (fun pp : Exp rT × Pat rT => Exp.scrut pp.1 pp.2) (p.2, pat)) := by
    funext q
    cases q.1 <;> simp [EctxItem.fillItem]
  rw [heq]
  refine EctxItem.measurable_rec_param (α := rT) (β := Exp rT) (γ := Exp rT)
    (f_appL := fun p => Exp.app p.1 (Exp.ofVal p.2))
    (f_appR := fun p => Exp.app p.2 p.1)
    (f_unop := fun p => Exp.unop p.2 p.1)
    (f_binopL := fun p => Exp.binop p.2.1 p.1 (Exp.ofVal p.2.2))
    (f_binopR := fun p => Exp.binop p.2.1 p.2.2 p.1)
    (f_condC := fun p => Exp.cond p.1 p.2.1 p.2.2)
    (f_pairL := fun p => Exp.pair p.1 (Exp.ofVal p.2))
    (f_pairR := fun p => Exp.pair p.2 p.1)
    (f_fst := fun p => Exp.fst p.1)
    (f_snd := fun p => Exp.snd p.1)
    (f_inl := fun p => Exp.inl p.1)
    (f_inr := fun p => Exp.inr p.1)
    (f_case := fun p => Exp.case p.1 p.2.1 p.2.2)
    (f_alloc := fun p => Exp.alloc p.1)
    (f_load := fun p => Exp.load p.1)
    (f_storeL := fun p => Exp.store p.1 (Exp.ofVal p.2))
    (f_storeR := fun p => Exp.store p.2 p.1)
    (f_tape := fun p => Exp.tape p.1)
    (f_randL := fun p => Exp.rand p.1 (Exp.ofVal p.2))
    (f_randR := fun p => Exp.rand p.2 p.1)
    (f_scrut := fun p => Exp.scrut p.1 p.2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  -- appL
  · show Measurable (fun p : Exp rT × Val rT => Function.uncurry Exp.app (p.1, Exp.ofVal p.2))
    refine Exp.app.measurable.comp ?_
    exact measurable_fst.prodMk <| Val.fst.measurable.comp measurable_snd
  -- appR
  · fun_prop
  -- unop
  · fun_prop
  -- binopL
  · show Measurable (fun p : Exp rT × BinOp × Val rT =>
        (fun (q : BinOp × Exp rT × Exp rT) => Exp.binop q.1 q.2.1 q.2.2)
          (p.2.1, p.1, Exp.ofVal p.2.2))
    refine Exp.binop.measurable.comp ?_
    refine (measurable_fst.comp measurable_snd).prodMk ?_
    exact measurable_fst.prodMk <| Val.fst.measurable.comp <| measurable_snd.comp measurable_snd
  -- binopR
  · fun_prop
  -- condC
  · fun_prop
  -- pairL
  · show Measurable (fun p : Exp rT × Val rT => Function.uncurry Exp.pair (p.1, Exp.ofVal p.2))
    refine Exp.pair.measurable.comp ?_
    exact measurable_fst.prodMk <| Val.fst.measurable.comp measurable_snd
  -- pairR
  · fun_prop
  -- fst, snd, inl, inr (all Unit-typed)
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop
  -- case
  · fun_prop
  -- alloc, load
  · fun_prop
  · fun_prop
  -- storeL
  · show Measurable (fun p : Exp rT × Val rT => Function.uncurry Exp.store (p.1, Exp.ofVal p.2))
    refine Exp.store.measurable.comp ?_
    exact measurable_fst.prodMk <| Val.fst.measurable.comp measurable_snd
  -- storeR
  · fun_prop
  -- tape
  · fun_prop
  -- randL
  · show Measurable (fun p : Exp rT × Val rT => Function.uncurry Exp.rand (p.1, Exp.ofVal p.2))
    refine Exp.rand.measurable.comp ?_
    exact measurable_fst.prodMk <| Val.fst.measurable.comp measurable_snd
  -- randR
  · fun_prop
  -- scrut
  · fun_prop

/-! ### `Ectx.fill` — `List.foldl` over `EctxItem.fillItem`.

Measurable once `EctxItem.fillItem`'s joint version is. Standard `List.foldl`
measurability argument; mechanical extension once the input is measurable. -/

theorem Ectx_fill.measurable [MeasurableSpace rT] :
    Measurable (fun (q : Ectx rT × Exp rT) => Ectx.fill q.1 q.2) := by
  -- `Ectx.fill K e = K.foldl (flip EctxItem.fillItem) e`.
  -- Apply the generic `List.measurable_foldl` keystone (stubbed in Measure.lean)
  -- with `f := flip EctxItem.fillItem`. Joint measurability of `f` reduces to
  -- the stubbed `fillItem.measurable` composed with `Prod.swap`.
  have hflip : Measurable (Function.uncurry (flip (EctxItem.fillItem (α := rT)))) := by
    -- Function.uncurry (flip fillItem) (e, Ki) = Ki.fillItem e = Function.uncurry fillItem (Ki, e)
    have hrw : Function.uncurry (flip (EctxItem.fillItem (α := rT)))
        = (fun q : EctxItem rT × Exp rT => q.1.fillItem q.2) ∘ Prod.swap := rfl
    rw [hrw]
    exact Exp.fillItem.measurable.comp measurable_swap
  exact List.measurable_foldl hflip

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
  -- Apply `measurable_struct_rec_param_shift` with β = (Nat × Exp rT) and shift
  -- `t_lam = t_fix = fun b => (b.1 + 1, b.2)` for binders. All other ctors are
  -- rebuild-only (ignore b in the combinator) except c_bvar which uses b for the
  -- if-then-else substitution.
  apply measurable_struct_rec_param_shift
    (g := fun (b : Nat × Exp rT) (e : Exp rT) => Exp.openRec b.1 b.2 e)
    (c_bvar  := fun b j => if b.1 = j then b.2 else (Exp.bvar j : Exp rT))
    (c_fvar  := fun _ x => Exp.fvar x)
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
    (t_lam   := fun b => (b.1 + 1, b.2))
    (t_fix   := fun b => (b.1 + 1, b.2))
  -- All 22 equations close by rfl (openRec's defining equations).
  -- c_bvar has the Nat-dependent if; discharge manually via measurable_from_prod_countable_right.
  case h_bvar =>
    have hrw : Function.uncurry (fun (b : Nat × Exp rT) (j : Nat) =>
              if b.1 = j then b.2 else (Exp.bvar j : Exp rT))
        = (fun (q : (Nat × Nat) × Exp rT) =>
              if q.1.1 = q.1.2 then q.2 else Exp.bvar q.1.2)
            ∘ (fun (p : (Nat × Exp rT) × Nat) => ((p.1.1, p.2), p.1.2)) := by
      funext ⟨⟨i, sub⟩, j⟩; rfl
    rw [hrw]
    have h1 : Measurable (fun (q : (Nat × Nat) × Exp rT) =>
                if q.1.1 = q.1.2 then q.2 else (Exp.bvar q.1.2 : Exp rT)) := by
      apply measurable_from_prod_countable_right
      intro ij
      by_cases h : ij.1 = ij.2
      · simp only [h, if_true]; exact measurable_id
      · simp only [h, if_false]; exact measurable_const
    exact h1.comp (by fun_prop : Measurable
      (fun (p : (Nat × Exp rT) × Nat) => ((p.1.1, p.2), p.1.2)))
  case h_t_lam => fun_prop
  case h_t_fix => fun_prop
  all_goals first | (intros; rfl) | fun_prop

theorem open'.measurable [MeasurableSpace rT] :
    Measurable (fun (q : Exp rT × Exp rT) => Exp.open' q.1 q.2) := by
  -- `open' e sub = openRec 0 sub e`. Compose with the (stubbed) keystone
  -- `openRec.measurable` via the packaging map `q ↦ ((0, q.2), q.1)`.
  have hpack : Measurable (fun q : Exp rT × Exp rT => ((0, q.2), q.1)) := by fun_prop
  exact Exp.openRec.measurable (rT := rT) |>.comp hpack

theorem closeRec.measurable [MeasurableSpace rT] :
    Measurable (fun (q : (Nat × Var) × Exp rT) => Exp.closeRec q.1.1 q.1.2 q.2) := by
  -- Same shape as openRec but with c_fvar carrying the if-then-else instead of c_bvar.
  apply measurable_struct_rec_param_shift
    (g := fun (b : Nat × Var) (e : Exp rT) => Exp.closeRec b.1 b.2 e)
    (c_bvar  := fun _ j => Exp.bvar j)
    (c_fvar  := fun b y => if b.2 = y then (Exp.bvar b.1 : Exp rT) else Exp.fvar y)
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
    (t_lam   := fun b => (b.1 + 1, b.2))
    (t_fix   := fun b => (b.1 + 1, b.2))
  -- c_fvar has the Var-dependent if; discharge manually.
  case h_fvar =>
    have hrw : Function.uncurry (fun (b : Nat × Var) (y : Var) =>
              if b.2 = y then (Exp.bvar b.1 : Exp rT) else Exp.fvar y)
        = (fun (q : (Var × Var) × Nat) =>
              if q.1.1 = q.1.2 then (Exp.bvar q.2 : Exp rT) else Exp.fvar q.1.2)
            ∘ (fun (p : (Nat × Var) × Var) => ((p.1.2, p.2), p.1.1)) := by
      funext ⟨⟨i, x⟩, y⟩; rfl
    rw [hrw]
    have h1 : Measurable (fun (q : (Var × Var) × Nat) =>
                if q.1.1 = q.1.2 then (Exp.bvar q.2 : Exp rT) else Exp.fvar q.1.2) := by
      apply measurable_from_prod_countable_right
      intro xy
      by_cases h : xy.1 = xy.2
      · simp only [h, if_true]; exact Exp.bvar.measurable
      · simp only [h, if_false]; exact measurable_const
    exact h1.comp (by fun_prop : Measurable
      (fun (p : (Nat × Var) × Var) => ((p.1.2, p.2), p.1.1)))
  case h_t_lam => fun_prop
  case h_t_fix => fun_prop
  all_goals first | (intros; rfl) | fun_prop

theorem close.measurable [MeasurableSpace rT] :
    Measurable (fun (q : Exp rT × Var) => Exp.close q.1 q.2) := by
  -- `close e x = closeRec 0 x e`. Compose with the (stubbed) keystone
  -- `closeRec.measurable` via the packaging map `q ↦ ((0, q.2), q.1)`.
  have hpack : Measurable (fun q : Exp rT × Var => ((0, q.2), q.1)) := by fun_prop
  exact Exp.closeRec.measurable (rT := rT) |>.comp hpack

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
  intro mOpt
  -- Step 1: rewrite `toVal?` as a `dite`.
  have hrw : (Exp.toVal? : Exp rT → Option (Val rT)) =
      fun e => if h : e.isValue then some (Val.mk e (Classical.choice h)) else none := by
    funext e
    by_cases h : e.isValue
    · simp only [Exp.toVal?, dif_pos h]
      cases hc : IsVal.check? e with
      | none => exact absurd (IsVal.not_isValue_of_check?_none hc) (not_not.mpr h)
      | some w => exact congrArg some (Val.ext rfl)
    · have hnone : Exp.toVal? e = none := Exp.toVal?_eq_none.mpr h
      simp only [hnone, dif_neg h]
  rw [hrw]
  intro S hS
  -- Step 2: decompose S via `optionEquivSumPUnit`. `S` is measurable in `instLocalOption`
  -- iff `S = (optionEquivSumPUnit) ⁻¹' Ssum` for some sum-measurable `Ssum`. Extract
  -- `Tval : Set (Val rT)` (measurable) and `Tnone : Set PUnit` from `Ssum`.
  obtain ⟨Ssum, hSsum, hSeq⟩ := hS
  -- `Ssum : Set (Val rT ⊕ PUnit)`; measurable iff inl/inr preimages are.
  have hTval_meas : MeasurableSet (Sum.inl ⁻¹' Ssum : Set (Val rT)) :=
    measurable_inl hSsum
  -- Pull back to `Exp rT` via `Val.fst`.
  obtain ⟨Uval, hUval, hUval_eq⟩ : ∃ U : Set (Exp rT), MeasurableSet U ∧
      Val.fst ⁻¹' U = (Sum.inl ⁻¹' Ssum : Set (Val rT)) :=
    MeasurableSpace.measurableSet_comap.mp hTval_meas
  -- Now compute the preimage.
  -- For value `e` (so `h : e.isValue`): the map sends `e` to `some ⟨e, (Classical.choice h)⟩`,
  -- and `some v ∈ S` iff `optionEquivSumPUnit (some v) = .inl v ∈ Ssum` iff
  -- `v ∈ Sum.inl ⁻¹' Ssum = Val.fst ⁻¹' Uval` iff `v.fst ∈ Uval`.
  -- So for value `e`: `e ∈ preimage` iff `e ∈ Uval`.
  -- For non-value `e`: the map sends `e` to `none`; `none ∈ S` iff
  -- `optionEquivSumPUnit none = .inr () ∈ Ssum` iff `() ∈ Sum.inr ⁻¹' Ssum`.
  -- That's a constant boolean depending on `Ssum`, so either `univ` or `∅` for non-values.
  have hMset : MeasurableSet {e : Exp rT | e.isValue} := by
    have heq : {e : Exp rT | e.isValue} = {e | e.isValueR} := by
      ext e; simp [Exp.isValue_iff_isValueR]
    rw [heq]; exact isValueR.measurable.setOf
  set noneIn : Prop := ((⟨⟩ : PUnit) ∈ (Sum.inr ⁻¹' Ssum : Set PUnit)) with hNoneIn
  classical
  have hpreimage_eq :
      (fun e : Exp rT => if h : e.isValue then some (Val.mk e (Classical.choice h)) else none) ⁻¹' S =
        ({e | e.isValue} ∩ Uval) ∪ (if noneIn then {e | ¬e.isValue} else ∅) := by
    ext e
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    by_cases hv : e.isValue
    · simp only [dif_pos hv]
      rw [← hSeq]
      simp only [Set.mem_preimage]
      have heqv : Equiv.optionEquivSumPUnit (Val rT) (some (Val.mk e (Classical.choice hv))) =
          .inl (Val.mk e (Classical.choice hv)) := by
        simp [Equiv.optionEquivSumPUnit]
      rw [heqv]
      have hmem_iff : (Sum.inl (Val.mk e (Classical.choice hv)) : Val rT ⊕ PUnit) ∈ Ssum ↔
          (Val.mk e (Classical.choice hv) : Val rT) ∈ (Sum.inl ⁻¹' Ssum : Set (Val rT)) := Iff.rfl
      rw [hmem_iff, ← hUval_eq]
      have hfeq : (Val.mk e (Classical.choice hv) : Val rT).fst = e := rfl
      simp only [Set.mem_preimage, hfeq]
      constructor
      · intro hUe
        left; exact ⟨hv, hUe⟩
      · rintro (⟨_, hUe⟩ | hcontra)
        · exact hUe
        · split_ifs at hcontra with hni
          · exact absurd hv hcontra
          · exact absurd hcontra (Set.notMem_empty _)
    · simp only [dif_neg hv]
      rw [← hSeq]
      simp only [Set.mem_preimage]
      have heqv : Equiv.optionEquivSumPUnit (Val rT) none = .inr ⟨⟩ := by
        simp [Equiv.optionEquivSumPUnit]
      rw [heqv]
      have hmem_iff : (Sum.inr ⟨⟩ : Val rT ⊕ PUnit) ∈ Ssum ↔ noneIn := Iff.rfl
      rw [hmem_iff]
      constructor
      · intro hni
        right; rw [if_pos hni]; exact hv
      · rintro (⟨hcontra, _⟩ | hcase)
        · exact absurd hcontra hv
        · split_ifs at hcase with hni
          · exact hni
          · exact absurd hcase (Set.notMem_empty _)
  rw [hpreimage_eq]
  refine MeasurableSet.union (hMset.inter hUval) ?_
  split_ifs
  · exact hMset.compl
  · exact MeasurableSet.empty

/-! ### `Exp.decompItem` — depends on `Exp.toVal?`. -/

/-- **Helper: measurability of `Option.elim`-form decomposition.**
For measurable `f : α → Option β` (under `instLocalOption` on the codomain),
measurable `default : α → γ` and `some_branch : α × β → γ`:
`(a ↦ (f a).elim (default a) (fun b => some_branch (a, b)))` is measurable. -/
theorem _root_.Option.measurable_elim_param
    {α β γ : Type _} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {f : α → Option β} (hf : @Measurable _ _ _ instLocalOption f)
    {default : α → γ} (hdef : Measurable default)
    {some_branch : α × β → γ} (hsome : Measurable some_branch) :
    Measurable (fun a => Option.casesOn (motive := fun _ => γ) (f a) (default a) (fun b => some_branch (a, b))) := by
  intro S hS
  have hpre : (fun a => Option.casesOn (motive := fun _ => γ) (f a) (default a) (fun b => some_branch (a, b))) ⁻¹' S
      = ({a | f a = none} ∩ default ⁻¹' S)
      ∪ (fun a => (a, f a)) ⁻¹'
          ((fun q : α × β => (q.1, (some q.2 : Option β))) ''
            ((fun q : α × β => some_branch q) ⁻¹' S)) := by
    ext a
    rcases hfa : f a with _ | b
    · simp [hfa]
    · simp only [hfa, Set.mem_preimage, Set.mem_union, Set.mem_inter_iff,
        Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq]
      constructor
      · intro h; right; exact ⟨(a, b), h, rfl, rfl⟩
      · rintro (⟨hcontra, _⟩ | ⟨⟨a', b'⟩, hab, haeq, hbeq⟩)
        · simp_all
        · subst haeq; exact Option.some_injective _ hbeq ▸ hab
  rw [hpre]
  refine MeasurableSet.union ?_ ?_
  · refine MeasurableSet.inter ?_ (hdef hS)
    have : {a | f a = none} = f ⁻¹' {none} := by ext a; simp
    rw [this]; exact hf MeasurableSet.singleton_none
  · refine MeasurableSet.preimage ?_ (measurable_id.prodMk hf)
    refine MeasurableEmbedding.measurableSet_image' ?_ (hsome hS)
    have heq : (fun q : α × β => (q.1, (some q.2 : Option β)))
        = Prod.map (id : α → α) (some : β → Option β) := rfl
    rw [heq]
    exact MeasurableEmbedding.id.prodMap MeasurableEmbedding.some_mk

/-- **Bind-form variant** of `Option.measurable_elim_param`.
For measurable `f : α → Option β` (under `instLocalOption`) and measurable
`some_branch : α × β → Option γ` (under `instLocalOption`),
`(a ↦ (f a).bind (fun b => some_branch (a, b)))` is measurable.

Use this when the lifter naturally reads as a `bind` chain — avoids the
per-call `funext; cases o <;> rfl` rewrite from `bind` to `casesOn`. -/
theorem _root_.Option.measurable_bind_param
    {α β γ : Type _} [MeasurableSpace α] [MeasurableSpace β]
    [_mγ : MeasurableSpace (Option γ)]
    {f : α → Option β} (hf : @Measurable _ _ _ instLocalOption f)
    {some_branch : α × β → Option γ} (hsome : Measurable some_branch) :
    Measurable (fun a => (f a).bind (fun b => some_branch (a, b))) := by
  have hrw : (fun a => (f a).bind (fun b => some_branch (a, b)))
      = fun a => Option.casesOn (motive := fun _ => Option γ) (f a)
          none (fun b => some_branch (a, b)) := by
    funext a; cases f a <;> rfl
  rw [hrw]
  exact Option.measurable_elim_param hf measurable_const hsome

theorem decompItem.measurable [MeasurableSpace rT] :
    let _ : MeasurableSpace (Option (EctxItem rT × Exp rT)) := instLocalOption
    Measurable (Exp.decompItem : Exp rT → Option (EctxItem rT × Exp rT)) := by
  intro mOpt
  -- Rewrite `decompItem` as a `casesOn` form and apply `Exp.measurable_rec`.
  have hrw : (Exp.decompItem : Exp rT → Option (EctxItem rT × Exp rT)) = fun e =>
      Exp.casesOn (motive := fun _ => Option (EctxItem rT × Exp rT)) e
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ => none) (fun _ => none)
        (fun e1 e2 =>
          e2.toVal?.casesOn (some (.appR e1, e2)) fun v2 =>
          e1.toVal?.casesOn (some (.appL v2, e1)) fun _ => none)
        (fun op e1 =>
          e1.toVal?.casesOn (some (.unop op, e1)) fun _ => none)
        (fun op e1 e2 =>
          e2.toVal?.casesOn (some (.binopR op e1, e2)) fun v2 =>
          e1.toVal?.casesOn (some (.binopL op v2, e1)) fun _ => none)
        (fun ec et ef =>
          ec.toVal?.casesOn (some (.condC et ef, ec)) fun _ => none)
        (fun e1 e2 =>
          e2.toVal?.casesOn (some (.pairR e1, e2)) fun v2 =>
          e1.toVal?.casesOn (some (.pairL v2, e1)) fun _ => none)
        (fun e1 => e1.toVal?.casesOn (some (.fst, e1)) fun _ => none)
        (fun e1 => e1.toVal?.casesOn (some (.snd, e1)) fun _ => none)
        (fun e1 => e1.toVal?.casesOn (some (.inl, e1)) fun _ => none)
        (fun e1 => e1.toVal?.casesOn (some (.inr, e1)) fun _ => none)
        (fun ec el er =>
          ec.toVal?.casesOn (some (.case el er, ec)) fun _ => none)
        (fun e1 => e1.toVal?.casesOn (some (.alloc, e1)) fun _ => none)
        (fun e1 => e1.toVal?.casesOn (some (.load, e1)) fun _ => none)
        (fun e1 e2 =>
          e2.toVal?.casesOn (some (.storeR e1, e2)) fun v2 =>
          e1.toVal?.casesOn (some (.storeL v2, e1)) fun _ => none)
        (fun e1 => e1.toVal?.casesOn (some (.tape, e1)) fun _ => none)
        (fun e1 e2 =>
          e2.toVal?.casesOn (some (.randR e1, e2)) fun v2 =>
          e1.toVal?.casesOn (some (.randL v2, e1)) fun _ => none)
        none
        (fun e1 p => e1.toVal?.casesOn (some (.scrut p, e1)) fun _ => none) := by
    funext e; cases e <;> rfl
  rw [hrw]
  have htv : @Measurable (Exp rT) (Option (Val rT)) _ instLocalOption Exp.toVal? :=
    toVal_question.measurable
  -- Unary helper: for `(b : β)` projecting an Exp rT, the focus-or-none pattern.
  have hunary : ∀ {β : Type _} [MeasurableSpace β] (K : β → EctxItem rT) (proj : β → Exp rT),
      Measurable K → Measurable proj →
      @Measurable β (Option (EctxItem rT × Exp rT)) _ instLocalOption
        (fun b : β => Option.casesOn (motive := fun _ => Option (EctxItem rT × Exp rT))
          (proj b).toVal? (some (K b, proj b)) fun _ => none) := by
    intro β _ K proj hK hproj
    exact Option.measurable_elim_param (f := fun b => (proj b).toVal?)
      (htv.comp hproj)
      (MeasurableEmbedding.some_mk.measurable.comp (hK.prodMk hproj))
      measurable_const
  have hbinary : ∀ {β : Type _} [MeasurableSpace β]
      (KR : β → EctxItem rT) (KL : β × Val rT → EctxItem rT)
      (projL : β → Exp rT) (projR : β → Exp rT),
      Measurable KR → Measurable KL → Measurable projL → Measurable projR →
      @Measurable β (Option (EctxItem rT × Exp rT)) _ instLocalOption
        (fun b : β => Option.casesOn (motive := fun _ => Option (EctxItem rT × Exp rT))
          (projR b).toVal? (some (KR b, projR b)) fun v2 =>
          Option.casesOn (motive := fun _ => Option (EctxItem rT × Exp rT))
            (projL b).toVal? (some (KL (b, v2), projL b)) fun _ => none) := by
    intro β _ KR KL projL projR hKR hKL hprojL hprojR
    have h_default : Measurable (fun b : β => (some (KR b, projR b) : Option (EctxItem rT × Exp rT))) := by
      have : Measurable (fun b : β => ((KR b, projR b) : EctxItem rT × Exp rT)) :=
        hKR.prodMk hprojR
      exact MeasurableEmbedding.some_mk.measurable.comp this
    have h_some_branch : Measurable
        (fun bv : β × Val rT =>
          Option.casesOn (motive := fun _ => Option (EctxItem rT × Exp rT))
            (projL bv.1).toVal? (some (KL bv, projL bv.1)) fun _ => none) := by
      have h_default' : Measurable
          (fun bv : β × Val rT => (some (KL bv, projL bv.1) : Option (EctxItem rT × Exp rT))) := by
        have : Measurable (fun bv : β × Val rT => ((KL bv, projL bv.1) : EctxItem rT × Exp rT)) :=
          hKL.prodMk (hprojL.comp measurable_fst)
        exact MeasurableEmbedding.some_mk.measurable.comp this
      exact Option.measurable_elim_param
        (f := fun bv : β × Val rT => (projL bv.1).toVal?)
        (htv.comp (hprojL.comp measurable_fst))
        h_default' measurable_const
    exact Option.measurable_elim_param (f := fun b => (projR b).toVal?)
      (htv.comp hprojR) h_default h_some_branch
  refine Exp.measurable_rec
    (f_bvar := fun _ => none) (f_fvar := fun _ => none) (f_lit := fun _ => none)
    (f_lam := fun _ => none) (f_fix := fun _ => none)
    (f_app := fun (q : Exp rT × Exp rT) =>
      q.2.toVal?.casesOn (some (EctxItem.appR q.1, q.2)) fun v2 =>
      q.1.toVal?.casesOn (some (EctxItem.appL v2, q.1)) fun _ => none)
    (f_unop := fun (q : UnOp × Exp rT) =>
      q.2.toVal?.casesOn (some (EctxItem.unop q.1, q.2)) fun _ => none)
    (f_binop := fun (q : BinOp × Exp rT × Exp rT) =>
      q.2.2.toVal?.casesOn (some (EctxItem.binopR q.1 q.2.1, q.2.2)) fun v2 =>
      q.2.1.toVal?.casesOn (some (EctxItem.binopL q.1 v2, q.2.1)) fun _ => none)
    (f_cond := fun (q : Exp rT × Exp rT × Exp rT) =>
      q.1.toVal?.casesOn (some (EctxItem.condC q.2.1 q.2.2, q.1)) fun _ => none)
    (f_pair := fun (q : Exp rT × Exp rT) =>
      q.2.toVal?.casesOn (some (EctxItem.pairR q.1, q.2)) fun v2 =>
      q.1.toVal?.casesOn (some (EctxItem.pairL v2, q.1)) fun _ => none)
    (f_fst := fun e1 => e1.toVal?.casesOn (some (EctxItem.fst, e1)) fun _ => none)
    (f_snd := fun e1 => e1.toVal?.casesOn (some (EctxItem.snd, e1)) fun _ => none)
    (f_inl := fun e1 => e1.toVal?.casesOn (some (EctxItem.inl, e1)) fun _ => none)
    (f_inr := fun e1 => e1.toVal?.casesOn (some (EctxItem.inr, e1)) fun _ => none)
    (f_case := fun (q : Exp rT × Exp rT × Exp rT) =>
      q.1.toVal?.casesOn (some (EctxItem.case q.2.1 q.2.2, q.1)) fun _ => none)
    (f_alloc := fun e1 => e1.toVal?.casesOn (some (EctxItem.alloc, e1)) fun _ => none)
    (f_load := fun e1 => e1.toVal?.casesOn (some (EctxItem.load, e1)) fun _ => none)
    (f_store := fun (q : Exp rT × Exp rT) =>
      q.2.toVal?.casesOn (some (EctxItem.storeR q.1, q.2)) fun v2 =>
      q.1.toVal?.casesOn (some (EctxItem.storeL v2, q.1)) fun _ => none)
    (f_tape := fun e1 => e1.toVal?.casesOn (some (EctxItem.tape, e1)) fun _ => none)
    (f_rand := fun (q : Exp rT × Exp rT) =>
      q.2.toVal?.casesOn (some (EctxItem.randR q.1, q.2)) fun v2 =>
      q.1.toVal?.casesOn (some (EctxItem.randL v2, q.1)) fun _ => none)
    (f_fail := fun _ => none)
    (f_scrut := fun (q : Exp rT × Pat rT) =>
      q.1.toVal?.casesOn (some (EctxItem.scrut q.2, q.1)) fun _ => none)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact measurable_const  -- h_lit
  · exact measurable_const  -- h_lam
  · exact measurable_const  -- h_fix
  · -- h_app
    exact hbinary
      (KR := fun q : Exp rT × Exp rT => EctxItem.appR q.1)
      (KL := fun (q : (Exp rT × Exp rT) × Val rT) => EctxItem.appL q.2)
      (projL := fun q => q.1) (projR := fun q => q.2)
      (EctxItem.appR.ι.measurable.comp measurable_fst)
      (EctxItem.appL.ι.measurable.comp measurable_snd)
      measurable_fst measurable_snd
  · -- h_unop
    exact hunary (β := UnOp × Exp rT)
      (K := fun q => EctxItem.unop q.1) (proj := fun q => q.2)
      (EctxItem.unop.ι.measurable.comp measurable_fst) measurable_snd
  · -- h_binop
    exact hbinary
      (KR := fun q : BinOp × Exp rT × Exp rT => EctxItem.binopR q.1 q.2.1)
      (KL := fun (q : (BinOp × Exp rT × Exp rT) × Val rT) => EctxItem.binopL q.1.1 q.2)
      (projL := fun q => q.2.1) (projR := fun q => q.2.2)
      (EctxItem.binopR.ι.measurable.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
      (EctxItem.binopL.ι.measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
  · -- h_cond
    exact hunary (β := Exp rT × Exp rT × Exp rT)
      (K := fun q => EctxItem.condC q.2.1 q.2.2)
      (proj := fun q => q.1)
      (EctxItem.condC.ι.measurable.comp ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)))
      measurable_fst
  · -- h_pair
    exact hbinary
      (KR := fun q : Exp rT × Exp rT => EctxItem.pairR q.1)
      (KL := fun (q : (Exp rT × Exp rT) × Val rT) => EctxItem.pairL q.2)
      (projL := fun q => q.1) (projR := fun q => q.2)
      (EctxItem.pairR.ι.measurable.comp measurable_fst)
      (EctxItem.pairL.ι.measurable.comp measurable_snd)
      measurable_fst measurable_snd
  · -- h_fst
    exact hunary (β := Exp rT) (K := fun _ => EctxItem.fst) (proj := id)
      measurable_const measurable_id
  · -- h_snd
    exact hunary (β := Exp rT) (K := fun _ => EctxItem.snd) (proj := id)
      measurable_const measurable_id
  · -- h_inl
    exact hunary (β := Exp rT) (K := fun _ => EctxItem.inl) (proj := id)
      measurable_const measurable_id
  · -- h_inr
    exact hunary (β := Exp rT) (K := fun _ => EctxItem.inr) (proj := id)
      measurable_const measurable_id
  · -- h_case
    exact hunary (β := Exp rT × Exp rT × Exp rT)
      (K := fun q => EctxItem.case q.2.1 q.2.2) (proj := fun q => q.1)
      (EctxItem.case.ι.measurable.comp ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)))
      measurable_fst
  · -- h_alloc
    exact hunary (β := Exp rT) (K := fun _ => EctxItem.alloc) (proj := id)
      measurable_const measurable_id
  · -- h_load
    exact hunary (β := Exp rT) (K := fun _ => EctxItem.load) (proj := id)
      measurable_const measurable_id
  · -- h_store
    exact hbinary
      (KR := fun q : Exp rT × Exp rT => EctxItem.storeR q.1)
      (KL := fun (q : (Exp rT × Exp rT) × Val rT) => EctxItem.storeL q.2)
      (projL := fun q => q.1) (projR := fun q => q.2)
      (EctxItem.storeR.ι.measurable.comp measurable_fst)
      (EctxItem.storeL.ι.measurable.comp measurable_snd)
      measurable_fst measurable_snd
  · -- h_tape
    exact hunary (β := Exp rT) (K := fun _ => EctxItem.tape) (proj := id)
      measurable_const measurable_id
  · -- h_rand
    exact hbinary
      (KR := fun q : Exp rT × Exp rT => EctxItem.randR q.1)
      (KL := fun (q : (Exp rT × Exp rT) × Val rT) => EctxItem.randL q.2)
      (projL := fun q => q.1) (projR := fun q => q.2)
      (EctxItem.randR.ι.measurable.comp measurable_fst)
      (EctxItem.randL.ι.measurable.comp measurable_snd)
      measurable_fst measurable_snd
  · -- h_scrut
    exact hunary (β := Exp rT × Pat rT)
      (K := fun q => EctxItem.scrut q.2) (proj := fun q => q.1)
      (EctxItem.scrut.ι.measurable.comp measurable_snd)
      measurable_fst

/-! ### `Exp.decomp` — well-founded recursion.

`Exp.decomp` uses `decreasing_by Exp.decompItem_height`. Not structural recursion;
outside the keystone's scope. Standard approach: induct on `Exp.height ≤ n` and
take a union over `n`.

**Status**: stubbed pending a well-founded-recursion measurability lemma. -/

theorem decomp.measurable [MeasurableSpace rT] :
    Measurable (Exp.decomp : Exp rT → Ectx rT × Exp rT) := by
  -- Blocked on the same `List`/`Ectx` measurability infrastructure as `List.measurable_foldl`
  -- (which the user said they'd handle by hand). Outline of proof: define `decompN n` as
  -- iterated `decompItem`, prove `decompN n` measurable by induction on `n` (with the
  -- step case needing `List.cons`-style measurability on `Ectx rT × EctxItem rT → Ectx rT`),
  -- then `decomp e = decompN e.height e` and dispatch via `measurable_from_prod_countable_right`.
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

/-! #### Exp-shape extraction helpers for `tryMatch.measurable`.

`tryMatch` recurses on `p : Pat rT` and at each `pair`/`inl`/`inr`/`lit` case
extracts subterms or a literal from `e : Exp rT`. We need measurability of
these extractions as `Option`-valued maps into `instLocalOption`. -/

/-- Extract the literal from `e = .lit b`, else `none`. -/
def Exp.litExtract (e : Exp rT) : Option (BaseLit rT) :=
  match e with | .lit b => some b | _ => none

/-- Extract the two children from `e = .pair e1 e2`, else `none`. -/
def Exp.pairExtract (e : Exp rT) : Option (Exp rT × Exp rT) :=
  match e with | .pair e1 e2 => some (e1, e2) | _ => none

/-- Extract the child from `e = .inl e'`, else `none`. -/
def Exp.inlExtract (e : Exp rT) : Option (Exp rT) :=
  match e with | .inl e' => some e' | _ => none

/-- Extract the child from `e = .inr e'`, else `none`. -/
def Exp.inrExtract (e : Exp rT) : Option (Exp rT) :=
  match e with | .inr e' => some e' | _ => none

theorem litExtract.measurable [MeasurableSpace rT] :
    let _ : MeasurableSpace (Option (BaseLit rT)) := instLocalOption
    Measurable (Exp.litExtract : Exp rT → Option (BaseLit rT)) := by
  intro _
  have hrw : Exp.litExtract (rT := rT) = fun e =>
      Exp.casesOn (motive := fun _ => Option (BaseLit rT)) e
        (fun _ => none) (fun _ => none) (fun b => some b)
        (fun _ => none) (fun _ => none) (fun _ _ => none)
        (fun _ _ => none) (fun _ _ _ => none) (fun _ _ _ => none)
        (fun _ _ => none) (fun _ => none) (fun _ => none) (fun _ => none) (fun _ => none)
        (fun _ _ _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (fun _ => none) (fun _ _ => none) none (fun _ _ => none) := by
    funext e; cases e <;> rfl
  rw [hrw]
  refine Exp.measurable_rec
    (f_bvar := fun _ => none) (f_fvar := fun _ => none) (f_lit := fun b => some b)
    (f_lam := fun _ => none) (f_fix := fun _ => none) (f_app := fun _ => none)
    (f_unop := fun _ => none) (f_binop := fun _ => none) (f_cond := fun _ => none)
    (f_pair := fun _ => none) (f_fst := fun _ => none) (f_snd := fun _ => none)
    (f_inl := fun _ => none) (f_inr := fun _ => none) (f_case := fun _ => none)
    (f_alloc := fun _ => none) (f_load := fun _ => none) (f_store := fun _ => none)
    (f_tape := fun _ => none) (f_rand := fun _ => none) (f_fail := fun _ => none)
    (f_scrut := fun _ => none)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact MeasurableEmbedding.some_mk.measurable
  all_goals exact measurable_const

theorem pairExtract.measurable [MeasurableSpace rT] :
    let _ : MeasurableSpace (Option (Exp rT × Exp rT)) := instLocalOption
    Measurable (Exp.pairExtract : Exp rT → Option (Exp rT × Exp rT)) := by
  intro _
  have hrw : Exp.pairExtract (rT := rT) = fun e =>
      Exp.casesOn (motive := fun _ => Option (Exp rT × Exp rT)) e
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ => none) (fun _ => none)
        (fun _ _ => none) (fun _ _ => none) (fun _ _ _ => none) (fun _ _ _ => none)
        (fun e1 e2 => some (e1, e2))
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ => none)
        (fun _ _ _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (fun _ => none) (fun _ _ => none) none (fun _ _ => none) := by
    funext e; cases e <;> rfl
  rw [hrw]
  refine Exp.measurable_rec
    (f_bvar := fun _ => none) (f_fvar := fun _ => none) (f_lit := fun _ => none)
    (f_lam := fun _ => none) (f_fix := fun _ => none) (f_app := fun _ => none)
    (f_unop := fun _ => none) (f_binop := fun _ => none) (f_cond := fun _ => none)
    (f_pair := fun q => some q) (f_fst := fun _ => none) (f_snd := fun _ => none)
    (f_inl := fun _ => none) (f_inr := fun _ => none) (f_case := fun _ => none)
    (f_alloc := fun _ => none) (f_load := fun _ => none) (f_store := fun _ => none)
    (f_tape := fun _ => none) (f_rand := fun _ => none) (f_fail := fun _ => none)
    (f_scrut := fun _ => none)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact measurable_const  -- h_lit
  · exact measurable_const  -- h_lam
  · exact measurable_const  -- h_fix
  · exact measurable_const  -- h_app
  · exact measurable_const  -- h_unop
  · exact measurable_const  -- h_binop
  · exact measurable_const  -- h_cond
  · exact MeasurableEmbedding.some_mk.measurable  -- h_pair
  all_goals exact measurable_const

theorem inlExtract.measurable [MeasurableSpace rT] :
    let _ : MeasurableSpace (Option (Exp rT)) := instLocalOption
    Measurable (Exp.inlExtract : Exp rT → Option (Exp rT)) := by
  intro _
  have hrw : Exp.inlExtract (rT := rT) = fun e =>
      Exp.casesOn (motive := fun _ => Option (Exp rT)) e
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ => none) (fun _ => none)
        (fun _ _ => none) (fun _ _ => none) (fun _ _ _ => none) (fun _ _ _ => none)
        (fun _ _ => none) (fun _ => none) (fun _ => none)
        (fun e' => some e') (fun _ => none) (fun _ _ _ => none)
        (fun _ => none) (fun _ => none) (fun _ _ => none) (fun _ => none) (fun _ _ => none)
        none (fun _ _ => none) := by
    funext e; cases e <;> rfl
  rw [hrw]
  refine Exp.measurable_rec
    (f_bvar := fun _ => none) (f_fvar := fun _ => none) (f_lit := fun _ => none)
    (f_lam := fun _ => none) (f_fix := fun _ => none) (f_app := fun _ => none)
    (f_unop := fun _ => none) (f_binop := fun _ => none) (f_cond := fun _ => none)
    (f_pair := fun _ => none) (f_fst := fun _ => none) (f_snd := fun _ => none)
    (f_inl := fun e' => some e') (f_inr := fun _ => none) (f_case := fun _ => none)
    (f_alloc := fun _ => none) (f_load := fun _ => none) (f_store := fun _ => none)
    (f_tape := fun _ => none) (f_rand := fun _ => none) (f_fail := fun _ => none)
    (f_scrut := fun _ => none)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact measurable_const  -- h_lit
  · exact measurable_const  -- h_lam
  · exact measurable_const  -- h_fix
  · exact measurable_const  -- h_app
  · exact measurable_const  -- h_unop
  · exact measurable_const  -- h_binop
  · exact measurable_const  -- h_cond
  · exact measurable_const  -- h_pair
  · exact measurable_const  -- h_fst
  · exact measurable_const  -- h_snd
  · exact MeasurableEmbedding.some_mk.measurable  -- h_inl
  all_goals exact measurable_const

theorem inrExtract.measurable [MeasurableSpace rT] :
    let _ : MeasurableSpace (Option (Exp rT)) := instLocalOption
    Measurable (Exp.inrExtract : Exp rT → Option (Exp rT)) := by
  intro _
  have hrw : Exp.inrExtract (rT := rT) = fun e =>
      Exp.casesOn (motive := fun _ => Option (Exp rT)) e
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ => none) (fun _ => none)
        (fun _ _ => none) (fun _ _ => none) (fun _ _ _ => none) (fun _ _ _ => none)
        (fun _ _ => none) (fun _ => none) (fun _ => none)
        (fun _ => none) (fun e' => some e') (fun _ _ _ => none)
        (fun _ => none) (fun _ => none) (fun _ _ => none) (fun _ => none) (fun _ _ => none)
        none (fun _ _ => none) := by
    funext e; cases e <;> rfl
  rw [hrw]
  refine Exp.measurable_rec
    (f_bvar := fun _ => none) (f_fvar := fun _ => none) (f_lit := fun _ => none)
    (f_lam := fun _ => none) (f_fix := fun _ => none) (f_app := fun _ => none)
    (f_unop := fun _ => none) (f_binop := fun _ => none) (f_cond := fun _ => none)
    (f_pair := fun _ => none) (f_fst := fun _ => none) (f_snd := fun _ => none)
    (f_inl := fun _ => none) (f_inr := fun e' => some e') (f_case := fun _ => none)
    (f_alloc := fun _ => none) (f_load := fun _ => none) (f_store := fun _ => none)
    (f_tape := fun _ => none) (f_rand := fun _ => none) (f_fail := fun _ => none)
    (f_scrut := fun _ => none)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact measurable_const  -- h_lit
  · exact measurable_const  -- h_lam
  · exact measurable_const  -- h_fix
  · exact measurable_const  -- h_app
  · exact measurable_const  -- h_unop
  · exact measurable_const  -- h_binop
  · exact measurable_const  -- h_cond
  · exact measurable_const  -- h_pair
  · exact measurable_const  -- h_fst
  · exact measurable_const  -- h_snd
  · exact measurable_const  -- h_inl
  · exact MeasurableEmbedding.some_mk.measurable  -- h_inr
  all_goals exact measurable_const

/-! ### `BaseLit` extractors for `liftXY`-style measurability.

Direct analogues of `Exp.litExtract` etc.: project an `Int` (resp. `Bool`) out of
`BaseLit.int` (resp. `.bool`), returning `none` on any other constructor. -/

/-- Extract the `Int` from `.int z`, else `none`. -/
def _root_.ProbLang.BaseLit.intExtract (l : BaseLit rT) : Option Int :=
  match l with | .int z => some z | _ => none

/-- Extract the `Bool` from `.bool b`, else `none`. -/
def _root_.ProbLang.BaseLit.boolExtract (l : BaseLit rT) : Option Bool :=
  match l with | .bool b => some b | _ => none

theorem _root_.ProbLang.BaseLit.intExtract.measurable
    [MeasurableSpace rT] [Inhabited rT] :
    let _ : MeasurableSpace (Option Int) := instLocalOption
    Measurable (BaseLit.intExtract : BaseLit rT → Option Int) := by
  intro _
  have hrw : BaseLit.intExtract (rT := rT) = fun l =>
      BaseLit.casesOn (motive := fun _ => Option Int) l
        (fun z => some z) (fun _ => none) none (fun _ => none) (fun _ => none) (fun _ => none) := by
    funext l; cases l <;> rfl
  rw [hrw]
  refine BaseLit.measurable_rec (rT := rT)
    (f_int := fun z => some z) (f_bool := fun _ => none) (f_unit := fun _ => none)
    (f_loc := fun _ => none) (f_lbl := fun _ => none) (f_real := fun _ => none)
    ?_
  exact measurable_const

theorem _root_.ProbLang.BaseLit.boolExtract.measurable
    [MeasurableSpace rT] [Inhabited rT] :
    let _ : MeasurableSpace (Option Bool) := instLocalOption
    Measurable (BaseLit.boolExtract : BaseLit rT → Option Bool) := by
  intro _
  have hrw : BaseLit.boolExtract (rT := rT) = fun l =>
      BaseLit.casesOn (motive := fun _ => Option Bool) l
        (fun _ => none) (fun b => some b) none (fun _ => none) (fun _ => none) (fun _ => none) := by
    funext l; cases l <;> rfl
  rw [hrw]
  refine BaseLit.measurable_rec (rT := rT)
    (f_int := fun _ => none) (f_bool := fun b => some b) (f_unit := fun _ => none)
    (f_loc := fun _ => none) (f_lbl := fun _ => none) (f_real := fun _ => none)
    ?_
  exact measurable_const

/-! ### `liftBin` — generic homogeneous binary lifter.

Most `BinOp.eval` arms have the same shape: extract a literal from each side,
extract a payload via a discrete extractor (`intExtract` or `boolExtract`), and
wrap the result as a `BaseLit`. We capture this once and instantiate per op. -/

/-- Lift a binary op on a discrete payload (`Int` or `Bool`) to operate on a
pair of `Exp` values via literal extraction. -/
def liftBin {β : Type _} (extr : BaseLit rT → Option β)
    (mkResult : β → β → BaseLit rT) (p : Exp rT × Exp rT) : Option (Exp rT) :=
  ((Exp.litExtract p.1).bind extr).bind fun x1 =>
    ((Exp.litExtract p.2).bind extr).bind fun x2 =>
      some (Exp.lit (mkResult x1 x2))

theorem liftBin.measurable [MeasurableSpace rT] [Inhabited rT]
    {β : Type _} [MeasurableSpace β]
    (extr : BaseLit rT → Option β) (mkResult : β → β → BaseLit rT)
    (hextr : @Measurable _ _ _ instLocalOption extr)
    (hmk : Measurable (Function.uncurry mkResult)) :
    Measurable (liftBin (rT := rT) extr mkResult) := by
  let _ : MeasurableSpace (Option β) := instLocalOption
  let _ : MeasurableSpace (Option (BaseLit rT)) := instLocalOption
  let _ : MeasurableSpace (Option (Exp rT)) := instLocalOption
  unfold liftBin
  refine Option.measurable_bind_param (β := β) (γ := Exp rT)
    (f := fun p : Exp rT × Exp rT => (Exp.litExtract p.1).bind extr)
    (some_branch := fun q : (Exp rT × Exp rT) × β =>
      (Exp.litExtract q.1.2).bind extr |>.bind fun x2 =>
        some (Exp.lit (mkResult q.2 x2))) ?_ ?_
  · refine Option.measurable_bind_param (β := BaseLit rT) (γ := β)
      (f := fun p : Exp rT × Exp rT => Exp.litExtract p.1)
      (some_branch := fun q : (Exp rT × Exp rT) × BaseLit rT => extr q.2) ?_ ?_
    · exact litExtract.measurable.comp measurable_fst
    · exact hextr.comp measurable_snd
  · refine Option.measurable_bind_param (β := β) (γ := Exp rT)
      (f := fun q : (Exp rT × Exp rT) × β => (Exp.litExtract q.1.2).bind extr)
      (some_branch := fun r : ((Exp rT × Exp rT) × β) × β =>
        some (Exp.lit (mkResult r.1.2 r.2))) ?_ ?_
    · refine Option.measurable_bind_param (β := BaseLit rT) (γ := β)
        (f := fun q : (Exp rT × Exp rT) × β => Exp.litExtract q.1.2)
        (some_branch := fun r : ((Exp rT × Exp rT) × β) × BaseLit rT => extr r.2)
        ?_ ?_
      · exact litExtract.measurable.comp (measurable_snd.comp measurable_fst)
      · exact hextr.comp measurable_snd
    · show Measurable fun r : ((Exp rT × Exp rT) × β) × β =>
        (some (Exp.lit (mkResult r.1.2 r.2)) : Option (Exp rT))
      refine MeasurableEmbedding.some_mk.measurable.comp ?_
      refine Exp.lit.measurable.comp ?_
      exact hmk.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

/-- Lift `Int → Int → Int` ops (`plus`, `minus`, …): both inputs integer literals,
output integer literal. -/
@[reducible] def liftII (f : Int → Int → Int) : Exp rT × Exp rT → Option (Exp rT) :=
  liftBin BaseLit.intExtract (fun z1 z2 => .int (f z1 z2))

/-- Lift `Bool → Bool → Bool` ops (`and`, `or`, `xor`): both inputs boolean
literals, output boolean literal. -/
@[reducible] def liftBB (f : Bool → Bool → Bool) : Exp rT × Exp rT → Option (Exp rT) :=
  liftBin BaseLit.boolExtract (fun b1 b2 => .bool (f b1 b2))

/-- Lift `Int → Int → Bool` ops (`lt`, `le`): both inputs integer literals,
output boolean literal. -/
@[reducible] def liftIB (f : Int → Int → Bool) : Exp rT × Exp rT → Option (Exp rT) :=
  liftBin BaseLit.intExtract (fun z1 z2 => .bool (f z1 z2))

theorem liftII.measurable [MeasurableSpace rT] [Inhabited rT] (f : Int → Int → Int) :
    Measurable (liftII (rT := rT) f) :=
  liftBin.measurable _ _ BaseLit.intExtract.measurable
    (Measurable.of_discrete.comp (Measurable.of_discrete (α := Int × Int) (β := Int)
      (f := Function.uncurry f)))

theorem liftBB.measurable [MeasurableSpace rT] [Inhabited rT] (f : Bool → Bool → Bool) :
    Measurable (liftBB (rT := rT) f) :=
  liftBin.measurable _ _ BaseLit.boolExtract.measurable
    (Measurable.of_discrete.comp (Measurable.of_discrete (α := Bool × Bool) (β := Bool)
      (f := Function.uncurry f)))

theorem liftIB.measurable [MeasurableSpace rT] [Inhabited rT] (f : Int → Int → Bool) :
    Measurable (liftIB (rT := rT) f) :=
  liftBin.measurable _ _ BaseLit.intExtract.measurable
    (Measurable.of_discrete.comp (Measurable.of_discrete (α := Int × Int) (β := Bool)
      (f := Function.uncurry f)))

/-! ### `liftEq` — bespoke lifter for `.eq` (5 patterns). -/

/-- The `eq` op fires on five `(v1, v2)` shapes: `(lit, lit)`, `(inl-lit, inl-lit)`,
`(inr-lit, inr-lit)`, `(inl-lit, inr-lit)`, `(inr-lit, inl-lit)`. We decompose
via `litExtract` directly, then `inlExtract`/`inrExtract` chained with
`litExtract` on each side. -/
def liftEq (p : Exp rT × Exp rT) : Option (Exp rT) :=
  match p.1, p.2 with
  | .lit l1, .lit l2 => some (Exp.lit (.bool (decide (l1 = l2))))
  | .inl (.lit l1), .inl (.lit l2) => some (Exp.lit (.bool (decide (l1 = l2))))
  | .inr (.lit l1), .inr (.lit l2) => some (Exp.lit (.bool (decide (l1 = l2))))
  | .inl (.lit _), .inr (.lit _) => some (Exp.lit (.bool false))
  | .inr (.lit _), .inl (.lit _) => some (Exp.lit (.bool false))
  | _, _ => none

/-! ### `liftEq.measurable` infrastructure.

`liftEq` has 5 live patterns; raw `cases` explosion is infeasible. We decompose
via three helpers (one per live outer shape: `lit`, `inl (lit _)`, `inr (lit _)`)
that consume `(l1 : BaseLit, v2 : Exp)` and emit `Option Exp`, then prove
`liftEq` measurable as a single `Exp.measurable_rec_param` with `v2` as the param. -/

/-- For `v1 = .lit l1`, `liftEq` is `match v2 with | .lit l2 => some (.bool (l1=l2)) | _ => none`.
We expose this as a function of `(v2, l1) : Exp × BaseLit` for joint measurability. -/
def liftEq_litK [DecidableEq (BaseLit rT)] (p : Exp rT × BaseLit rT) : Option (Exp rT) :=
  match p.1 with
  | .lit l2 => some (Exp.lit (.bool (decide (p.2 = l2))))
  | _ => none

/-- For `v1 = .inl e1'`, `liftEq` is `match e1', v2 with | .lit l1, .lit l2 => ... | .lit _, .inr (.lit _) => false | _ => none`.
Treat as a function of `(e1', v2)` and split on `e1'`'s `.lit` shape via `litExtract`. -/
def liftEq_inlK [DecidableEq (BaseLit rT)] (p : Exp rT × Exp rT) : Option (Exp rT) :=
  match p.1, p.2 with
  | .lit l1, .inl (.lit l2) => some (Exp.lit (.bool (decide (l1 = l2))))
  | .lit _, .inr (.lit _) => some (Exp.lit (.bool false))
  | _, _ => none

def liftEq_inrK [DecidableEq (BaseLit rT)] (p : Exp rT × Exp rT) : Option (Exp rT) :=
  match p.1, p.2 with
  | .lit l1, .inr (.lit l2) => some (Exp.lit (.bool (decide (l1 = l2))))
  | .lit _, .inl (.lit _) => some (Exp.lit (.bool false))
  | _, _ => none

/-- Instance: `MeasurableEq (BaseLit rT)` lifted from `MeasurableEq rT`.

`MeasurableEq α` is the typeclass `MeasurableSet (Set.diagonal α)` — the diagonal
`{(a,a) | a : α}` is measurable in `α × α`. It's the natural condition under
which `decide`-equality `α × α → Bool` is measurable.

`BaseLit rT`'s diagonal is a disjoint union of 6 pieces, one per constructor:
the `.int`/`.bool`/`.unit`/`.loc`/`.lbl` pieces use discrete σ-algebras
(singletons measurable; diagonal trivially measurable), and the `.real` piece
needs `MeasurableEq rT`. So the BaseLit-diagonal is measurable iff
`MeasurableEq rT` holds.

This instance lets us prove `BinOp_eval.measurable` (which has a `.eq` arm
doing literal-equality on BaseLits) without requiring discrete `rT`. -/
instance _root_.ProbLang.BaseLit.instMeasurableEq
    {rT : Type _} [MeasurableSpace rT] [Inhabited rT] [MeasurableEq rT] :
    MeasurableEq (BaseLit rT) := by
  refine MeasurableEq.mk ?_
  -- The diagonal is `{(b, b) | b : BaseLit rT}`. Decompose by constructor: each
  -- piece `Pᵢ = {(ctor x, ctor x) | x : Xᵢ}` is the image of the `Xᵢ`-diagonal under
  -- a product of `ctor` embeddings. Union of 6 measurable sets is measurable.
  let Pi (z : Int) : BaseLit rT × BaseLit rT := (.int z, .int z)
  let Pb (b : Bool) : BaseLit rT × BaseLit rT := (.bool b, .bool b)
  let Pl (l : Loc) : BaseLit rT × BaseLit rT := (.loc l, .loc l)
  let Pll (l : Lbl) : BaseLit rT × BaseLit rT := (.lbl l, .lbl l)
  let Pr (r : rT) : BaseLit rT × BaseLit rT := (.real r, .real r)
  have hdecomp : Set.diagonal (BaseLit rT)
      = Set.range Pi ∪ Set.range Pb ∪ {(BaseLit.unit, BaseLit.unit)}
      ∪ Set.range Pl ∪ Set.range Pll ∪ Set.range Pr := by
    ext ⟨a, b⟩
    simp only [Set.mem_diagonal_iff, Set.mem_union, Set.mem_range, Set.mem_singleton_iff,
      Pi, Pb, Pl, Pll, Pr]
    constructor
    · rintro rfl
      cases a with
      | int z => exact .inl (.inl (.inl (.inl (.inl ⟨z, rfl⟩))))
      | bool b => exact .inl (.inl (.inl (.inl (.inr ⟨b, rfl⟩))))
      | unit => exact .inl (.inl (.inl (.inr rfl)))
      | loc l => exact .inl (.inl (.inr ⟨l, rfl⟩))
      | lbl l => exact .inl (.inr ⟨l, rfl⟩)
      | real r => exact .inr ⟨r, rfl⟩
    · rintro ((((((⟨_, h⟩) | ⟨_, h⟩) | h) | ⟨_, h⟩) | ⟨_, h⟩) | ⟨_, h⟩) <;> cases h <;> rfl
  rw [hdecomp]
  -- Each `Set.range Pᵢ` is the image of `Set.diagonal Xᵢ` under a product-of-ctors map.
  -- Per-arm: each `Set.range fun x => (ι x, ι x)` rewrites to `Prod.map ι ι '' Set.diagonal X`,
  -- then is measurable as the image of a measurable set under a measurable embedding.
  have hrw_int : Set.range Pi = (Prod.map BaseLit.int BaseLit.int) '' Set.diagonal Int := by
    ext ⟨a, b⟩; constructor
    · rintro ⟨x, hx⟩; refine ⟨(x, x), rfl, ?_⟩; simp only [Prod.map_apply, ← hx, Pi]
    · rintro ⟨⟨x1, x2⟩, hdiag, himg⟩
      simp only [Set.mem_diagonal_iff] at hdiag
      simp only [Prod.map_apply, Prod.mk.injEq] at himg
      refine ⟨x1, ?_⟩; simp only [Pi]; simp only [← himg.1, ← himg.2, hdiag]
  have hrw_bool : Set.range Pb = (Prod.map BaseLit.bool BaseLit.bool) '' Set.diagonal Bool := by
    ext ⟨a, b⟩; constructor
    · rintro ⟨x, hx⟩; refine ⟨(x, x), rfl, ?_⟩; simp only [Prod.map_apply, ← hx, Pb]
    · rintro ⟨⟨x1, x2⟩, hdiag, himg⟩
      simp only [Set.mem_diagonal_iff] at hdiag
      simp only [Prod.map_apply, Prod.mk.injEq] at himg
      refine ⟨x1, ?_⟩; simp only [Pb]; simp only [← himg.1, ← himg.2, hdiag]
  have hrw_loc : Set.range Pl = (Prod.map BaseLit.loc BaseLit.loc) '' Set.diagonal Loc := by
    ext ⟨a, b⟩; constructor
    · rintro ⟨x, hx⟩; refine ⟨(x, x), rfl, ?_⟩; simp only [Prod.map_apply, ← hx, Pl]
    · rintro ⟨⟨x1, x2⟩, hdiag, himg⟩
      simp only [Set.mem_diagonal_iff] at hdiag
      simp only [Prod.map_apply, Prod.mk.injEq] at himg
      refine ⟨x1, ?_⟩; simp only [Pl]; simp only [← himg.1, ← himg.2, hdiag]
  have hrw_lbl : Set.range Pll = (Prod.map BaseLit.lbl BaseLit.lbl) '' Set.diagonal Lbl := by
    ext ⟨a, b⟩; constructor
    · rintro ⟨x, hx⟩; refine ⟨(x, x), rfl, ?_⟩; simp only [Prod.map_apply, ← hx, Pll]
    · rintro ⟨⟨x1, x2⟩, hdiag, himg⟩
      simp only [Set.mem_diagonal_iff] at hdiag
      simp only [Prod.map_apply, Prod.mk.injEq] at himg
      refine ⟨x1, ?_⟩; simp only [Pll]; simp only [← himg.1, ← himg.2, hdiag]
  have hrw_real : Set.range Pr = (Prod.map BaseLit.real BaseLit.real) '' Set.diagonal rT := by
    ext ⟨a, b⟩; constructor
    · rintro ⟨x, hx⟩; refine ⟨(x, x), rfl, ?_⟩; simp only [Prod.map_apply, ← hx, Pr]
    · rintro ⟨⟨x1, x2⟩, hdiag, himg⟩
      simp only [Set.mem_diagonal_iff] at hdiag
      simp only [Prod.map_apply, Prod.mk.injEq] at himg
      refine ⟨x1, ?_⟩; simp only [Pr]; simp only [← himg.1, ← himg.2, hdiag]
  refine ((((MeasurableSet.union ?_ ?_).union ?_).union ?_).union ?_).union ?_
  · rw [hrw_int]; exact (BaseLit.int.measurableEmbedding.prodMap
      BaseLit.int.measurableEmbedding).measurableSet_image'
      MeasurableEq.measurableSet_diagonal
  · rw [hrw_bool]; exact (BaseLit.bool.measurableEmbedding.prodMap
      BaseLit.bool.measurableEmbedding).measurableSet_image'
      MeasurableEq.measurableSet_diagonal
  · exact MeasurableSet.singleton _
  · rw [hrw_loc]; exact (BaseLit.loc.measurableEmbedding.prodMap
      BaseLit.loc.measurableEmbedding).measurableSet_image'
      MeasurableEq.measurableSet_diagonal
  · rw [hrw_lbl]; exact (BaseLit.lbl.measurableEmbedding.prodMap
      BaseLit.lbl.measurableEmbedding).measurableSet_image'
      MeasurableEq.measurableSet_diagonal
  · rw [hrw_real]; exact (BaseLit.real.measurableEmbedding.prodMap
      BaseLit.real.measurableEmbedding).measurableSet_image'
      MeasurableEq.measurableSet_diagonal

/-- Measurability of `decide`-equality on `BaseLit rT` under `[MeasurableEq rT]`.
Follows directly from `MeasurableEq (BaseLit rT)` (derived above) and the
general `Measurable.eq` lemma. -/
private theorem decide_eq_BaseLit_measurable
    [MeasurableSpace rT] [Inhabited rT] [DecidableEq (BaseLit rT)]
    [MeasurableEq rT] :
    Measurable (fun p : BaseLit rT × BaseLit rT => decide (p.1 = p.2)) := by
  refine measurable_to_bool ?_
  have hpre : (fun p : BaseLit rT × BaseLit rT => decide (p.1 = p.2)) ⁻¹' {true}
      = Set.diagonal (BaseLit rT) := by ext p; simp [Set.diagonal]
  rw [hpre]
  exact MeasurableEq.measurableSet_diagonal

/-- `liftEq_litK.measurable` — outer split on `p.1` (the `v2`); only `.lit` live.
Requires `[MeasurableEq rT]` because the innermost
`decide (l1 = l2)` over `BaseLit rT` factors through the diagonal of `rT × rT`. -/
theorem liftEq_litK.measurable [MeasurableSpace rT] [Inhabited rT]
    [DecidableEq (BaseLit rT)] [MeasurableEq rT] :
    Measurable (liftEq_litK (rT := rT)) := by
  let _ : MeasurableSpace (Option Int) := instLocalOption
  let _ : MeasurableSpace (Option (BaseLit rT)) := instLocalOption
  let _ : MeasurableSpace (Option (Exp rT)) := instLocalOption
  -- Reshape: liftEq_litK p = (Exp.litExtract p.1).bind (fun l2 => some (Exp.lit (.bool (decide (p.2 = l2)))))
  have hrw : liftEq_litK (rT := rT) = fun p : Exp rT × BaseLit rT =>
      (Exp.litExtract p.1).bind fun l2 => some (Exp.lit (.bool (decide (p.2 = l2)))) := by
    funext p; obtain ⟨v2, l1⟩ := p
    cases v2 <;> simp [liftEq_litK, Exp.litExtract, Option.bind]
  rw [hrw]
  refine Option.measurable_bind_param (β := BaseLit rT) (γ := Exp rT)
    (f := fun p : Exp rT × BaseLit rT => Exp.litExtract p.1)
    (some_branch := fun r : (Exp rT × BaseLit rT) × BaseLit rT =>
      some (Exp.lit (BaseLit.bool (decide (r.1.2 = r.2))))) ?_ ?_
  · exact litExtract.measurable.comp measurable_fst
  · -- `r ↦ some (.lit (.bool (decide (r.1.2 = r.2))))`.
    refine MeasurableEmbedding.some_mk.measurable.comp ?_
    refine Exp.lit.measurable.comp ?_
    refine BaseLit.bool.measurable.comp ?_
    -- Show through explicit composition.
    have : (fun r : (Exp rT × BaseLit rT) × BaseLit rT => decide (r.1.2 = r.2))
         = (fun p : BaseLit rT × BaseLit rT => decide (p.1 = p.2)) ∘
           (fun r : (Exp rT × BaseLit rT) × BaseLit rT => (r.1.2, r.2)) := rfl
    rw [this]
    exact (decide_eq_BaseLit_measurable (rT := rT)).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

/-- `liftEq_inlK.measurable` — joint over `(e1', v2)`; live shapes: `(lit l1, inl (lit l2))`
and `(lit _, inr (lit _))`. Reshape via `Exp.litExtract` on `e1'` first, then a
2-arm decision on `v2`. -/
theorem liftEq_inlK.measurable [MeasurableSpace rT] [Inhabited rT]
    [DecidableEq (BaseLit rT)] [MeasurableEq rT] :
    Measurable (liftEq_inlK (rT := rT)) := by
  let _ : MeasurableSpace (Option (BaseLit rT)) := instLocalOption
  let _ : MeasurableSpace (Option (Exp rT)) := instLocalOption
  -- liftEq_inlK p = (litExtract p.1).bind (fun l1 =>
  --   match p.2 with
  --   | .inl (.lit l2) => some (.bool (l1 = l2))
  --   | .inr (.lit _)  => some (.bool false)
  --   | _ => none)
  -- The inner function of `(l1, p.2)` factors as: `inlExtract p.2 >>= litExtract >>= λ l2 => some...`
  --                                              ∪ `inrExtract p.2 >>= litExtract >>= λ _ => some false`
  -- Both branches are measurable bind chains; their `union via first-some` is what `match` does.
  -- We rewrite directly to a unified bind form.
  have hrw : liftEq_inlK (rT := rT) = fun p : Exp rT × Exp rT =>
      (Exp.litExtract p.1).bind fun l1 =>
        (Exp.inlExtract p.2).casesOn
          ((Exp.inrExtract p.2).casesOn none (fun e2 => (Exp.litExtract e2).bind fun _ =>
            some (Exp.lit (.bool false))))
          (fun e1 => (Exp.litExtract e1).bind fun l2 =>
            some (Exp.lit (.bool (decide (l1 = l2))))) := by
    funext p; obtain ⟨v1, v2⟩ := p
    cases v1 <;> simp [liftEq_inlK, Exp.litExtract, Exp.inlExtract, Exp.inrExtract, Option.bind] <;>
      cases v2 <;> simp [liftEq_inlK, Exp.litExtract, Exp.inlExtract, Exp.inrExtract, Option.bind] <;>
      rename_i e2 <;> cases e2 <;>
      simp [liftEq_inlK, Exp.litExtract, Exp.inlExtract, Exp.inrExtract, Option.bind]
  rw [hrw]
  refine Option.measurable_bind_param (β := BaseLit rT) (γ := Exp rT)
    (f := fun p : Exp rT × Exp rT => Exp.litExtract p.1)
    (some_branch := fun r : (Exp rT × Exp rT) × BaseLit rT =>
      (Exp.inlExtract r.1.2).casesOn
        ((Exp.inrExtract r.1.2).casesOn none (fun e2 => (Exp.litExtract e2).bind fun _ =>
          some (Exp.lit (BaseLit.bool false))))
        (fun e1 => (Exp.litExtract e1).bind fun l2 =>
          some (Exp.lit (BaseLit.bool (decide (r.2 = l2)))))) ?_ ?_
  · exact litExtract.measurable.comp measurable_fst
  · -- Inner: split on `inlExtract r.1.2`.
    apply Option.measurable_elim_param (β := Exp rT) (γ := Option (Exp rT))
      (f := fun r : (Exp rT × Exp rT) × BaseLit rT => Exp.inlExtract r.1.2)
      (default := fun r : (Exp rT × Exp rT) × BaseLit rT =>
        (Exp.inrExtract r.1.2).casesOn none (fun e2 =>
          (Exp.litExtract e2).bind fun _ => some (Exp.lit (BaseLit.bool false))))
      (some_branch := fun s : ((Exp rT × Exp rT) × BaseLit rT) × Exp rT =>
        (Exp.litExtract s.2).bind fun l2 =>
          some (Exp.lit (BaseLit.bool (decide (s.1.2 = l2)))))
    · exact inlExtract.measurable.comp (measurable_snd.comp measurable_fst)
    · -- default: split on `inrExtract r.1.2`.
      apply Option.measurable_elim_param (β := Exp rT) (γ := Option (Exp rT))
        (f := fun r : (Exp rT × Exp rT) × BaseLit rT => Exp.inrExtract r.1.2)
        (default := fun _ => none)
        (some_branch := fun s : ((Exp rT × Exp rT) × BaseLit rT) × Exp rT =>
          (Exp.litExtract s.2).bind fun _ => some (Exp.lit (BaseLit.bool false)))
      · exact inrExtract.measurable.comp (measurable_snd.comp measurable_fst)
      · exact measurable_const
      · refine Option.measurable_bind_param (β := BaseLit rT) (γ := Exp rT)
          (f := fun s : ((Exp rT × Exp rT) × BaseLit rT) × Exp rT => Exp.litExtract s.2)
          (some_branch := fun _ : (((Exp rT × Exp rT) × BaseLit rT) × Exp rT) × BaseLit rT =>
            some (Exp.lit (BaseLit.bool false))) ?_ ?_
        · exact litExtract.measurable.comp measurable_snd
        · exact measurable_const
    · -- some-branch on `(s, e1)`: `(litExtract e1).bind (λ l2 => some (.bool (decide (s.1.2 = l2))))`.
      refine Option.measurable_bind_param (β := BaseLit rT) (γ := Exp rT)
        (f := fun s : ((Exp rT × Exp rT) × BaseLit rT) × Exp rT => Exp.litExtract s.2)
        (some_branch := fun t : (((Exp rT × Exp rT) × BaseLit rT) × Exp rT) × BaseLit rT =>
          some (Exp.lit (BaseLit.bool (decide (t.1.1.2 = t.2))))) ?_ ?_
      · exact litExtract.measurable.comp measurable_snd
      · refine MeasurableEmbedding.some_mk.measurable.comp ?_
        refine Exp.lit.measurable.comp ?_
        refine BaseLit.bool.measurable.comp ?_
        exact decide_eq_BaseLit_measurable.comp
          ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)

/-- `liftEq_inrK.measurable` — symmetric to `inlK`. -/
theorem liftEq_inrK.measurable [MeasurableSpace rT] [Inhabited rT]
    [DecidableEq (BaseLit rT)] [MeasurableEq rT] :
    Measurable (liftEq_inrK (rT := rT)) := by
  let _ : MeasurableSpace (Option (BaseLit rT)) := instLocalOption
  let _ : MeasurableSpace (Option (Exp rT)) := instLocalOption
  have hrw : liftEq_inrK (rT := rT) = fun p : Exp rT × Exp rT =>
      (Exp.litExtract p.1).bind fun l1 =>
        (Exp.inrExtract p.2).casesOn
          ((Exp.inlExtract p.2).casesOn none (fun e2 => (Exp.litExtract e2).bind fun _ =>
            some (Exp.lit (.bool false))))
          (fun e1 => (Exp.litExtract e1).bind fun l2 =>
            some (Exp.lit (.bool (decide (l1 = l2))))) := by
    funext p; obtain ⟨v1, v2⟩ := p
    cases v1 <;> simp [liftEq_inrK, Exp.litExtract, Exp.inlExtract, Exp.inrExtract, Option.bind] <;>
      cases v2 <;> simp [liftEq_inrK, Exp.litExtract, Exp.inlExtract, Exp.inrExtract, Option.bind] <;>
      rename_i e2 <;> cases e2 <;>
      simp [liftEq_inrK, Exp.litExtract, Exp.inlExtract, Exp.inrExtract, Option.bind]
  rw [hrw]
  refine Option.measurable_bind_param (β := BaseLit rT) (γ := Exp rT)
    (f := fun p : Exp rT × Exp rT => Exp.litExtract p.1)
    (some_branch := fun r : (Exp rT × Exp rT) × BaseLit rT =>
      (Exp.inrExtract r.1.2).casesOn
        ((Exp.inlExtract r.1.2).casesOn none (fun e2 => (Exp.litExtract e2).bind fun _ =>
          some (Exp.lit (BaseLit.bool false))))
        (fun e1 => (Exp.litExtract e1).bind fun l2 =>
          some (Exp.lit (BaseLit.bool (decide (r.2 = l2)))))) ?_ ?_
  · exact litExtract.measurable.comp measurable_fst
  · apply Option.measurable_elim_param (β := Exp rT) (γ := Option (Exp rT))
      (f := fun r : (Exp rT × Exp rT) × BaseLit rT => Exp.inrExtract r.1.2)
      (default := fun r : (Exp rT × Exp rT) × BaseLit rT =>
        (Exp.inlExtract r.1.2).casesOn none (fun e2 =>
          (Exp.litExtract e2).bind fun _ => some (Exp.lit (BaseLit.bool false))))
      (some_branch := fun s : ((Exp rT × Exp rT) × BaseLit rT) × Exp rT =>
        (Exp.litExtract s.2).bind fun l2 =>
          some (Exp.lit (BaseLit.bool (decide (s.1.2 = l2)))))
    · exact inrExtract.measurable.comp (measurable_snd.comp measurable_fst)
    · apply Option.measurable_elim_param (β := Exp rT) (γ := Option (Exp rT))
        (f := fun r : (Exp rT × Exp rT) × BaseLit rT => Exp.inlExtract r.1.2)
        (default := fun _ => none)
        (some_branch := fun s : ((Exp rT × Exp rT) × BaseLit rT) × Exp rT =>
          (Exp.litExtract s.2).bind fun _ => some (Exp.lit (BaseLit.bool false)))
      · exact inlExtract.measurable.comp (measurable_snd.comp measurable_fst)
      · exact measurable_const
      · refine Option.measurable_bind_param (β := BaseLit rT) (γ := Exp rT)
          (f := fun s : ((Exp rT × Exp rT) × BaseLit rT) × Exp rT => Exp.litExtract s.2)
          (some_branch := fun _ : (((Exp rT × Exp rT) × BaseLit rT) × Exp rT) × BaseLit rT =>
            some (Exp.lit (BaseLit.bool false))) ?_ ?_
        · exact litExtract.measurable.comp measurable_snd
        · exact measurable_const
    · refine Option.measurable_bind_param (β := BaseLit rT) (γ := Exp rT)
        (f := fun s : ((Exp rT × Exp rT) × BaseLit rT) × Exp rT => Exp.litExtract s.2)
        (some_branch := fun t : (((Exp rT × Exp rT) × BaseLit rT) × Exp rT) × BaseLit rT =>
          some (Exp.lit (BaseLit.bool (decide (t.1.1.2 = t.2))))) ?_ ?_
      · exact litExtract.measurable.comp measurable_snd
      · refine MeasurableEmbedding.some_mk.measurable.comp ?_
        refine Exp.lit.measurable.comp ?_
        refine BaseLit.bool.measurable.comp ?_
        exact decide_eq_BaseLit_measurable.comp
          ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)

/-- Helper for `liftEq.measurable`: `liftEq` dispatched through per-shape helpers
on the outer Exp constructor. Separate lemma so its proof time is bounded. -/
private theorem liftEq_dispatch [MeasurableSpace rT] [Inhabited rT]
    [DecidableEq (BaseLit rT)] (p : Exp rT × Exp rT) :
    liftEq p =
      Exp.casesOn (motive := fun _ => Option (Exp rT)) p.1
        (fun _ => none) (fun _ => none)
        (fun l1 => liftEq_litK (p.2, l1))
        (fun _ => none) (fun _ => none)
        (fun _ _ => none) (fun _ _ => none) (fun _ _ _ => none) (fun _ _ _ => none)
        (fun _ _ => none) (fun _ => none) (fun _ => none)
        (fun e1' => liftEq_inlK (e1', p.2))
        (fun e1' => liftEq_inrK (e1', p.2))
        (fun _ _ _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (fun _ => none) (fun _ _ => none) none (fun _ _ => none) := by
  obtain ⟨v1, v2⟩ := p
  cases v1 with
  | lit l1 =>
    show liftEq (.lit l1, v2) = liftEq_litK (v2, l1)
    cases v2 <;> simp [liftEq, liftEq_litK]
  | inl e1' =>
    show liftEq (.inl e1', v2) = liftEq_inlK (e1', v2)
    cases e1' <;> cases v2 <;> simp [liftEq, liftEq_inlK] <;>
      (rename_i e2'; cases e2' <;> simp [liftEq, liftEq_inlK])
  | inr e1' =>
    show liftEq (.inr e1', v2) = liftEq_inrK (e1', v2)
    cases e1' <;> cases v2 <;> simp [liftEq, liftEq_inrK] <;>
      (rename_i e2'; cases e2' <;> simp [liftEq, liftEq_inrK])
  | _ => rfl

/-- `liftEq.measurable` — bespoke 5-pattern lifter for `BinOp.eval .eq`. Decomposed via
three per-shape helpers: `litK` (when `v1 = .lit _`), `inlK` (when `v1 = .inl _`),
`inrK` (when `v1 = .inr _`). The outer split on `v1` uses `Exp.measurable_rec`. -/
theorem liftEq.measurable [MeasurableSpace rT] [Inhabited rT]
    [DecidableEq (BaseLit rT)] [MeasurableEq rT] :
    Measurable (liftEq (rT := rT)) := by
  have hrw : liftEq (rT := rT) = fun p : Exp rT × Exp rT =>
      Exp.casesOn (motive := fun _ => Option (Exp rT)) p.1
        (fun _ => none) (fun _ => none)
        (fun l1 => liftEq_litK (p.2, l1))
        (fun _ => none) (fun _ => none)
        (fun _ _ => none) (fun _ _ => none) (fun _ _ _ => none) (fun _ _ _ => none)
        (fun _ _ => none) (fun _ => none) (fun _ => none)
        (fun e1' => liftEq_inlK (e1', p.2))
        (fun e1' => liftEq_inrK (e1', p.2))
        (fun _ _ _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (fun _ => none) (fun _ _ => none) none (fun _ _ => none) := by
    funext p; exact liftEq_dispatch p
  rw [hrw]
  -- Joint `Exp.measurable_rec_param` over (p.1, p.2): split on p.1, with p.2 as param.
  refine Exp.measurable_rec_param (rT := rT) (α := Option (Exp rT)) (β := Exp rT)
    (c_bvar := fun _ => none) (c_fvar := fun _ => none)
    (c_lit := fun q : Exp rT × BaseLit rT => liftEq_litK q)
    (c_lam := fun _ => none) (c_fix := fun _ => none)
    (c_app := fun _ => none) (c_unop := fun _ => none) (c_binop := fun _ => none)
    (c_cond := fun _ => none) (c_pair := fun _ => none)
    (c_fst := fun _ => none) (c_snd := fun _ => none)
    (c_inl := fun q : Exp rT × Exp rT => liftEq_inlK (q.2, q.1))
    (c_inr := fun q : Exp rT × Exp rT => liftEq_inrK (q.2, q.1))
    (c_case := fun _ => none) (c_alloc := fun _ => none) (c_load := fun _ => none)
    (c_store := fun _ => none) (c_tape := fun _ => none) (c_rand := fun _ => none)
    (c_fail := fun _ => none) (c_scrut := fun _ => none)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  -- 22 measurability obligations, only 3 nontrivial.
  · exact measurable_const  -- c_bvar
  · exact measurable_const  -- c_fvar
  · -- c_lit: `q ↦ liftEq_litK q`. Just apply the helper.
    exact liftEq_litK.measurable
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · -- c_inl: `q ↦ liftEq_inlK (q.2, q.1)`. Swap then apply.
    show Measurable fun q : Exp rT × Exp rT => liftEq_inlK (q.2, q.1)
    exact liftEq_inlK.measurable.comp (measurable_snd.prodMk measurable_fst)
  · show Measurable fun q : Exp rT × Exp rT => liftEq_inrK (q.2, q.1)
    exact liftEq_inrK.measurable.comp (measurable_snd.prodMk measurable_fst)
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const

/-! ### `BinOp.eval` rewritten as lifter dispatch + measurability assembly. -/

/-- Helper: `liftII f (v1, v2)` matches the structural pattern of `BinOp.eval`'s
int-int arms — only int-literal-pairs produce `some`, anything else `none`. -/
private theorem liftII_def_eq (f : Int → Int → Int) (v1 v2 : Exp rT) :
    liftII f (v1, v2) =
      (match v1, v2 with
       | .lit (.int z1), .lit (.int z2) => some (Exp.lit (.int (f z1 z2)))
       | _, _ => none) := by
  unfold liftII liftBin
  cases v1 <;> simp [Exp.litExtract, BaseLit.intExtract, Option.bind]
  rename_i l1
  cases l1 <;> simp [BaseLit.intExtract, Option.bind] <;> cases v2 <;>
    simp [Exp.litExtract, BaseLit.intExtract, Option.bind]
  rename_i l2
  cases l2 <;> simp [BaseLit.intExtract, Option.bind]

private theorem liftBB_def_eq (f : Bool → Bool → Bool) (v1 v2 : Exp rT) :
    liftBB f (v1, v2) =
      (match v1, v2 with
       | .lit (.bool b1), .lit (.bool b2) => some (Exp.lit (.bool (f b1 b2)))
       | _, _ => none) := by
  unfold liftBB liftBin
  cases v1 <;> simp [Exp.litExtract, BaseLit.boolExtract, Option.bind]
  rename_i l1
  cases l1 <;> simp [BaseLit.boolExtract, Option.bind] <;> cases v2 <;>
    simp [Exp.litExtract, BaseLit.boolExtract, Option.bind]
  rename_i l2
  cases l2 <;> simp [BaseLit.boolExtract, Option.bind]

private theorem liftIB_def_eq (f : Int → Int → Bool) (v1 v2 : Exp rT) :
    liftIB f (v1, v2) =
      (match v1, v2 with
       | .lit (.int z1), .lit (.int z2) => some (Exp.lit (.bool (f z1 z2)))
       | _, _ => none) := by
  unfold liftIB liftBin
  cases v1 <;> simp [Exp.litExtract, BaseLit.intExtract, Option.bind]
  rename_i l1
  cases l1 <;> simp [BaseLit.intExtract, Option.bind] <;> cases v2 <;>
    simp [Exp.litExtract, BaseLit.intExtract, Option.bind]
  rename_i l2
  cases l2 <;> simp [BaseLit.intExtract, Option.bind]

/-- Helper for the `eq` arm of `BinOp.eval_eq_lift`: `BinOp.eval .eq v1 v2 = liftEq (v1, v2)`.
Split as a separate lemma so its proof time is bounded and doesn't blow the
parent's heartbeat budget. -/
private theorem BinOp.eval_eq_eq_liftEq [ProbLangℝ rT] (v1 v2 : Exp rT) :
    BinOp.eval .eq v1 v2 = liftEq (v1, v2) := by
  cases v1 <;> cases v2 <;> (try simp [BinOp.eval, liftEq]) <;>
    -- For `.inl _, .inl _`, `.inl _, .inr _`, `.inr _, .inl _`, `.inr _, .inr _`:
    -- inner Exp may or may not be a `.lit`; recurse one more level.
    (rename_i ein1 ein2; cases ein1 <;> cases ein2 <;> simp [BinOp.eval, liftEq])

/-- `BinOp.eval` is equal to a per-op dispatch through `liftII`/`liftBB`/`liftIB`/`liftEq`.
The proof is per-op: discrete `cases op` then unfold each side to the same
nested-`match` form via the `liftXY_def_eq` helpers (`rfl` for `liftEq`). -/
theorem BinOp.eval_eq_lift [ProbLangℝ rT] (op : BinOp) (v1 v2 : Exp rT) :
    BinOp.eval op v1 v2 =
      (match op with
       | .plus  => liftII (· + ·)
       | .minus => liftII (· - ·)
       | .mult  => liftII (· * ·)
       | .div   => liftII (· / ·)
       | .mod   => liftII (· % ·)
       | .shl   => liftII (fun z1 z2 => z1 * 2 ^ z2.toNat)
       | .shr   => liftII (fun z1 z2 => z1 / 2 ^ z2.toNat)
       | .and   => liftBB (· && ·)
       | .or    => liftBB (· || ·)
       | .xor   => liftBB (· ^^ ·)
       | .lt    => liftIB (decide <| · < ·)
       | .le    => liftIB (decide <| · ≤ ·)
       | .eq    => liftEq) (v1, v2) := by
  cases op
  all_goals
    dsimp only []
    first
      | (rw [liftII_def_eq]; cases v1 <;> first
          | rfl
          | (rename_i l1; cases l1 <;> first
              | rfl
              | (cases v2 <;> first
                  | rfl
                  | (rename_i l2; cases l2 <;> rfl))))
      | (rw [liftBB_def_eq]; cases v1 <;> first
          | rfl
          | (rename_i l1; cases l1 <;> first
              | rfl
              | (cases v2 <;> first
                  | rfl
                  | (rename_i l2; cases l2 <;> rfl))))
      | (rw [liftIB_def_eq]; cases v1 <;> first
          | rfl
          | (rename_i l1; cases l1 <;> first
              | rfl
              | (cases v2 <;> first
                  | rfl
                  | (rename_i l2; cases l2 <;> rfl))))
      | exact BinOp.eval_eq_eq_liftEq v1 v2

theorem BinOp_eval.measurable [ProbLangℝ rT] :
    Measurable (fun (q : BinOp × Exp rT × Exp rT) => BinOp.eval q.1 q.2.1 q.2.2) := by
  have hrw : (fun (q : BinOp × Exp rT × Exp rT) => BinOp.eval q.1 q.2.1 q.2.2)
      = fun q : BinOp × Exp rT × Exp rT =>
          (match q.1 with
           | .plus  => liftII (· + ·)
           | .minus => liftII (· - ·)
           | .mult  => liftII (· * ·)
           | .div   => liftII (· / ·)
           | .mod   => liftII (· % ·)
           | .shl   => liftII (fun z1 z2 => z1 * 2 ^ z2.toNat)
           | .shr   => liftII (fun z1 z2 => z1 / 2 ^ z2.toNat)
           | .and   => liftBB (· && ·)
           | .or    => liftBB (· || ·)
           | .xor   => liftBB (· ^^ ·)
           | .lt    => liftIB (decide <| · < ·)
           | .le    => liftIB (decide <| · ≤ ·)
           | .eq    => liftEq) (q.2.1, q.2.2) := by
    funext q; exact BinOp.eval_eq_lift q.1 q.2.1 q.2.2
  rw [hrw]
  apply measurable_from_prod_countable_right
  intro op
  cases op
  all_goals dsimp only
  · exact liftII.measurable _
  · exact liftII.measurable _
  · exact liftII.measurable _
  · exact liftII.measurable _
  · exact liftII.measurable _
  · exact liftBB.measurable _
  · exact liftBB.measurable _
  · exact liftBB.measurable _
  · exact liftEq.measurable
  · exact liftIB.measurable _
  · exact liftIB.measurable _
  · exact liftII.measurable _
  · exact liftII.measurable _

theorem tryMatch.measurable [ProbLangℝ rT] :
    Measurable (fun (q : Pat rT × Exp rT) => Pat.tryMatch q.1 q.2) := by
  -- Bounded-iteration approach attempted. `Pat.tryMatchN` (bounded recurse-at-most-n version)
  -- and its measurability are designed; the extraction helpers `litExtract`, `pairExtract`,
  -- `inlExtract`, `inrExtract` are proven (see above). What remains:
  -- (1) `tryMatchN_eq_tryMatch` (n > patDepth p → tryMatchN n = tryMatch) — tactical friction
  --     on the `Pat.lit` case (rfl claims types differ but goal is X = X syntactically).
  -- (2) `tryMatchN.measurable` (induction on n, using Pat.measurable_struct_rec_param with
  --     β = Exp rT and each branch built from extraction + Option.measurable_elim_param + ih).
  -- (3) Conclude via `measurable_from_prod_countable_right` over Nat.
  -- Deferred.
  sorry

end Exp
end ProbLang
end ProbLangMeasures
