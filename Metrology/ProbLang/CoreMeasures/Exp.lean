module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.Pat
public import Metrology.ProbLang.CoreMeasures.Stamp

meta import Metrology.Meta

@[expose] public section


noncomputable section ProbLangMeasures

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

/-# Measure space on expressions.

Follows the same `BaseLit`/`Pat` template. `Exp` has:
- two syntax-leaf constructors (`bvar : Nat`, `fvar : Var`)
- one data-leaf constructor (`lit : BaseLit rT`)
- two nullary constructors (`fail`, `urand`)
- many recursive constructors of arities 1–3 (`lam`, `fix`, `fst`, `snd`, `inl`, `inr`,
  `alloc`, `load`, `tape`; `app`, `pair`, `store`, `rand`; `cond`, `case`)
- mixed constructors:
  - `unop : UnOp + 1 rec` (UnOp is a syntax-leaf-style discrete tag retained in the shape)
  - `binop : BinOp + 2 rec`
  - `scrut : 1 rec + Pat rT` (Pat is a data leaf)
-/

namespace ProbLang.Exp

theorem bvar.ι.inj  {rT : Type _} : Function.Injective (@Exp.bvar.ι  rT) := by solve_ι_inj
theorem fvar.ι.inj  {rT : Type _} : Function.Injective (@Exp.fvar.ι  rT) := by solve_ι_inj
theorem lit.ι.inj   {rT : Type _} : Function.Injective (@Exp.lit.ι   rT) := by solve_ι_inj
theorem lam.ι.inj   {rT : Type _} : Function.Injective (@Exp.lam.ι   rT) := by solve_ι_inj
theorem fix.ι.inj   {rT : Type _} : Function.Injective (@Exp.fix.ι   rT) := by solve_ι_inj
theorem app.ι.inj   {rT : Type _} : Function.Injective (@Exp.app.ι   rT) := by solve_ι_inj
theorem unop.ι.inj  {rT : Type _} : Function.Injective (@Exp.unop.ι  rT) := by solve_ι_inj
theorem binop.ι.inj {rT : Type _} : Function.Injective (@Exp.binop.ι rT) := by solve_ι_inj
theorem cond.ι.inj  {rT : Type _} : Function.Injective (@Exp.cond.ι  rT) := by solve_ι_inj
theorem pair.ι.inj  {rT : Type _} : Function.Injective (@Exp.pair.ι  rT) := by solve_ι_inj
theorem fst.ι.inj   {rT : Type _} : Function.Injective (@Exp.fst.ι   rT) := by solve_ι_inj
theorem snd.ι.inj   {rT : Type _} : Function.Injective (@Exp.snd.ι   rT) := by solve_ι_inj
theorem inl.ι.inj   {rT : Type _} : Function.Injective (@Exp.inl.ι   rT) := by solve_ι_inj
theorem inr.ι.inj   {rT : Type _} : Function.Injective (@Exp.inr.ι   rT) := by solve_ι_inj
theorem case.ι.inj  {rT : Type _} : Function.Injective (@Exp.case.ι  rT) := by solve_ι_inj
theorem alloc.ι.inj {rT : Type _} : Function.Injective (@Exp.alloc.ι rT) := by solve_ι_inj
theorem load.ι.inj  {rT : Type _} : Function.Injective (@Exp.load.ι  rT) := by solve_ι_inj
theorem store.ι.inj {rT : Type _} : Function.Injective (@Exp.store.ι rT) := by solve_ι_inj
theorem tape.ι.inj  {rT : Type _} : Function.Injective (@Exp.tape.ι  rT) := by solve_ι_inj
theorem rand.ι.inj  {rT : Type _} : Function.Injective (@Exp.rand.ι  rT) := by solve_ι_inj
theorem scrut.ι.inj {rT : Type _} : Function.Injective (@Exp.scrut.ι rT) := by solve_ι_inj

/-- A cylinder is an `Exp`-shaped tree whose data-leaf payloads (`BaseLit rT` in `lit`,
`Pat rT` in `scrut`) have been replaced by measurable sets of those types. Syntax-leaf args
(`bvar`'s `Nat`, `fvar`'s `Var`, `unop`'s `UnOp`, `binop`'s `BinOp`) are kept as-is. -/
inductive Cylinder (rT : Type _)
  | bvar (n : Nat)
  | fvar (x : Var)
  | lit (S : Set (BaseLit rT))
  | lam (c : Cylinder rT)
  | fix (c : Cylinder rT)
  | app (c1 c2 : Cylinder rT)
  | unop (u : UnOp) (c : Cylinder rT)
  | binop (b : BinOp) (c1 c2 : Cylinder rT)
  | cond (cc ct cf : Cylinder rT)
  | pair (c1 c2 : Cylinder rT)
  | fst (c : Cylinder rT)
  | snd (c : Cylinder rT)
  | inl (c : Cylinder rT)
  | inr (c : Cylinder rT)
  | case (cc cl cr : Cylinder rT)
  | alloc (c : Cylinder rT)
  | load (c : Cylinder rT)
  | store (c1 c2 : Cylinder rT)
  | tape (c : Cylinder rT)
  | rand (c1 c2 : Cylinder rT)
  | fail
  | urand
  | scrut (c : Cylinder rT) (S : Set (Pat rT))

/-- An expression with all data-leaf payloads forgotten. Syntax-leaf args are kept. -/
inductive Shape
  | bvar (n : Nat)
  | fvar (x : Var)
  | lit
  | lam (s : Shape)
  | fix (s : Shape)
  | app (s1 s2 : Shape)
  | unop (u : UnOp) (s : Shape)
  | binop (b : BinOp) (s1 s2 : Shape)
  | cond (sc st sf : Shape)
  | pair (s1 s2 : Shape)
  | fst (s : Shape)
  | snd (s : Shape)
  | inl (s : Shape)
  | inr (s : Shape)
  | case (sc sl sr : Shape)
  | alloc (s : Shape)
  | load (s : Shape)
  | store (s1 s2 : Shape)
  | tape (s : Shape)
  | rand (s1 s2 : Shape)
  | fail
  | urand
  | scrut (s : Shape)
  deriving Countable

/-- Interpret a cylinder as the set of `Exp rT` it describes. -/
@[simp, stamp_simp] def Cylinder.flatten {rT : Type _} : Cylinder rT → Set (Exp rT)
  | .bvar n        => {Exp.bvar n}
  | .fvar x        => {Exp.fvar x}
  | .lit S         => Exp.lit '' S
  | .lam c         => Exp.lam '' flatten c
  | .fix c         => Exp.fix '' flatten c
  | .app c1 c2     => (fun p => Exp.app p.1 p.2) '' (flatten c1 ×ˢ flatten c2)
  | .unop u c      => Exp.unop u '' flatten c
  | .binop b c1 c2 => (fun p => Exp.binop b p.1 p.2) '' (flatten c1 ×ˢ flatten c2)
  | .cond cc ct cf =>
      (fun p : Exp rT × Exp rT × Exp rT => Exp.cond p.1 p.2.1 p.2.2) ''
        (flatten cc ×ˢ flatten ct ×ˢ flatten cf)
  | .pair c1 c2    => (fun p => Exp.pair p.1 p.2) '' (flatten c1 ×ˢ flatten c2)
  | .fst c         => Exp.fst '' flatten c
  | .snd c         => Exp.snd '' flatten c
  | .inl c         => Exp.inl '' flatten c
  | .inr c         => Exp.inr '' flatten c
  | .case cc cl cr =>
      (fun p : Exp rT × Exp rT × Exp rT => Exp.case p.1 p.2.1 p.2.2) ''
        (flatten cc ×ˢ flatten cl ×ˢ flatten cr)
  | .alloc c       => Exp.alloc '' flatten c
  | .load c        => Exp.load '' flatten c
  | .store c1 c2   => (fun p => Exp.store p.1 p.2) '' (flatten c1 ×ˢ flatten c2)
  | .tape c        => Exp.tape '' flatten c
  | .rand c1 c2    => (fun p => Exp.rand p.1 p.2) '' (flatten c1 ×ˢ flatten c2)
  | .fail          => {Exp.fail}
  | .urand         => {Exp.urand}
  | .scrut c S     => (fun p => Exp.scrut p.1 p.2) '' (flatten c ×ˢ S)

/-- A cylinder has measurable leaves if every data-leaf set it carries is measurable. -/
inductive Cylinder.HasMeasurableLeaves {rT : Type _} [MeasurableSpace rT] :
    Cylinder rT → Prop where
  | bvar  : HasMeasurableLeaves (.bvar n)
  | fvar  : HasMeasurableLeaves (.fvar x)
  | lit S : MeasurableSet S → HasMeasurableLeaves (.lit S)
  | lam   : HasMeasurableLeaves c → HasMeasurableLeaves (.lam c)
  | fix   : HasMeasurableLeaves c → HasMeasurableLeaves (.fix c)
  | app   : HasMeasurableLeaves c1 → HasMeasurableLeaves c2 → HasMeasurableLeaves (.app c1 c2)
  | unop  : HasMeasurableLeaves c → HasMeasurableLeaves (.unop u c)
  | binop : HasMeasurableLeaves c1 → HasMeasurableLeaves c2 → HasMeasurableLeaves (.binop b c1 c2)
  | cond  : HasMeasurableLeaves cc → HasMeasurableLeaves ct → HasMeasurableLeaves cf →
            HasMeasurableLeaves (.cond cc ct cf)
  | pair  : HasMeasurableLeaves c1 → HasMeasurableLeaves c2 → HasMeasurableLeaves (.pair c1 c2)
  | fst   : HasMeasurableLeaves c → HasMeasurableLeaves (.fst c)
  | snd   : HasMeasurableLeaves c → HasMeasurableLeaves (.snd c)
  | inl   : HasMeasurableLeaves c → HasMeasurableLeaves (.inl c)
  | inr   : HasMeasurableLeaves c → HasMeasurableLeaves (.inr c)
  | case  : HasMeasurableLeaves cc → HasMeasurableLeaves cl → HasMeasurableLeaves cr →
            HasMeasurableLeaves (.case cc cl cr)
  | alloc : HasMeasurableLeaves c → HasMeasurableLeaves (.alloc c)
  | load  : HasMeasurableLeaves c → HasMeasurableLeaves (.load c)
  | store : HasMeasurableLeaves c1 → HasMeasurableLeaves c2 → HasMeasurableLeaves (.store c1 c2)
  | tape  : HasMeasurableLeaves c → HasMeasurableLeaves (.tape c)
  | rand  : HasMeasurableLeaves c1 → HasMeasurableLeaves c2 → HasMeasurableLeaves (.rand c1 c2)
  | fail  : HasMeasurableLeaves .fail
  | urand : HasMeasurableLeaves .urand
  | scrut S : HasMeasurableLeaves c → MeasurableSet S → HasMeasurableLeaves (.scrut c S)

instance instMeasurableSpaceExp [MeasurableSpace rT] : MeasurableSpace (Exp rT) :=
  .generateFrom <| Cylinder.flatten '' { c : Cylinder rT | c.HasMeasurableLeaves }

@[simp, stamp_simp] def shape : Exp rT → Shape
  | .bvar n        => .bvar n
  | .fvar x        => .fvar x
  | .lit _         => .lit
  | .lam e         => .lam (shape e)
  | .fix e         => .fix (shape e)
  | .app e1 e2     => .app (shape e1) (shape e2)
  | .unop u e      => .unop u (shape e)
  | .binop b e1 e2 => .binop b (shape e1) (shape e2)
  | .cond ec et ef => .cond (shape ec) (shape et) (shape ef)
  | .pair e1 e2    => .pair (shape e1) (shape e2)
  | .fst e         => .fst (shape e)
  | .snd e         => .snd (shape e)
  | .inl e         => .inl (shape e)
  | .inr e         => .inr (shape e)
  | .case ec el er => .case (shape ec) (shape el) (shape er)
  | .alloc e       => .alloc (shape e)
  | .load e        => .load (shape e)
  | .store e1 e2   => .store (shape e1) (shape e2)
  | .tape e        => .tape (shape e)
  | .rand e1 e2    => .rand (shape e1) (shape e2)
  | .fail          => .fail
  | .urand         => .urand
  | .scrut e _     => .scrut (shape e)

/-- Shape of a cylinder (forgets data leaves). -/
@[simp, stamp_simp] def Cylinder.shape {rT : Type _} : Cylinder rT → Shape
  | .bvar n        => .bvar n
  | .fvar x        => .fvar x
  | .lit _         => .lit
  | .lam c         => .lam (shape c)
  | .fix c         => .fix (shape c)
  | .app c1 c2     => .app (shape c1) (shape c2)
  | .unop u c      => .unop u (shape c)
  | .binop b c1 c2 => .binop b (shape c1) (shape c2)
  | .cond cc ct cf => .cond (shape cc) (shape ct) (shape cf)
  | .pair c1 c2    => .pair (shape c1) (shape c2)
  | .fst c         => .fst (shape c)
  | .snd c         => .snd (shape c)
  | .inl c         => .inl (shape c)
  | .inr c         => .inr (shape c)
  | .case cc cl cr => .case (shape cc) (shape cl) (shape cr)
  | .alloc c       => .alloc (shape c)
  | .load c        => .load (shape c)
  | .store c1 c2   => .store (shape c1) (shape c2)
  | .tape c        => .tape (shape c)
  | .rand c1 c2    => .rand (shape c1) (shape c2)
  | .fail          => .fail
  | .urand         => .urand
  | .scrut c _     => .scrut (shape c)

/-- The "universe cylinder" for a given shape: `univ` at every data leaf, same skeleton. -/
@[simp, stamp_simp] def Shape.cylinder {rT : Type _} : Shape → Cylinder rT
  | .bvar n        => .bvar n
  | .fvar x        => .fvar x
  | .lit           => .lit Set.univ
  | .lam s         => .lam (cylinder s)
  | .fix s         => .fix (cylinder s)
  | .app s1 s2     => .app (cylinder s1) (cylinder s2)
  | .unop u s      => .unop u (cylinder s)
  | .binop b s1 s2 => .binop b (cylinder s1) (cylinder s2)
  | .cond sc st sf => .cond (cylinder sc) (cylinder st) (cylinder sf)
  | .pair s1 s2    => .pair (cylinder s1) (cylinder s2)
  | .fst s         => .fst (cylinder s)
  | .snd s         => .snd (cylinder s)
  | .inl s         => .inl (cylinder s)
  | .inr s         => .inr (cylinder s)
  | .case sc sl sr => .case (cylinder sc) (cylinder sl) (cylinder sr)
  | .alloc s       => .alloc (cylinder s)
  | .load s        => .load (cylinder s)
  | .store s1 s2   => .store (cylinder s1) (cylinder s2)
  | .tape s        => .tape (cylinder s)
  | .rand s1 s2    => .rand (cylinder s1) (cylinder s2)
  | .fail          => .fail
  | .urand         => .urand
  | .scrut s       => .scrut (cylinder s) Set.univ

/-! ### Cylinder intersection. -/

/-- Partial intersection of cylinders. -/
def Cylinder.inter? {rT : Type _} : Cylinder rT → Cylinder rT → Option (Cylinder rT)
  | .bvar n₁, .bvar n₂ => if n₁ = n₂ then some (.bvar n₁) else none
  | .fvar x₁, .fvar x₂ => if x₁ = x₂ then some (.fvar x₁) else none
  | .lit S₁, .lit S₂ => some (.lit (S₁ ∩ S₂))
  | .lam c, .lam c' =>
      match Cylinder.inter? c c' with
      | some r => some (.lam r)
      | none => none
  | .fix c, .fix c' =>
      match Cylinder.inter? c c' with
      | some r => some (.fix r)
      | none => none
  | .app c₁ c₂, .app c₁' c₂' =>
      match Cylinder.inter? c₁ c₁', Cylinder.inter? c₂ c₂' with
      | some r₁, some r₂ => some (.app r₁ r₂)
      | _, _ => none
  | .unop u₁ c, .unop u₂ c' =>
      if u₁ = u₂ then
        match Cylinder.inter? c c' with
        | some r => some (.unop u₁ r)
        | none => none
      else none
  | .binop b₁ c₁ c₂, .binop b₂ c₁' c₂' =>
      if b₁ = b₂ then
        match Cylinder.inter? c₁ c₁', Cylinder.inter? c₂ c₂' with
        | some r₁, some r₂ => some (.binop b₁ r₁ r₂)
        | _, _ => none
      else none
  | .cond cc ct cf, .cond cc' ct' cf' =>
      match Cylinder.inter? cc cc', Cylinder.inter? ct ct', Cylinder.inter? cf cf' with
      | some rc, some rt, some rf => some (.cond rc rt rf)
      | _, _, _ => none
  | .pair c₁ c₂, .pair c₁' c₂' =>
      match Cylinder.inter? c₁ c₁', Cylinder.inter? c₂ c₂' with
      | some r₁, some r₂ => some (.pair r₁ r₂)
      | _, _ => none
  | .fst c, .fst c' =>
      match Cylinder.inter? c c' with
      | some r => some (.fst r)
      | none => none
  | .snd c, .snd c' =>
      match Cylinder.inter? c c' with
      | some r => some (.snd r)
      | none => none
  | .inl c, .inl c' =>
      match Cylinder.inter? c c' with
      | some r => some (.inl r)
      | none => none
  | .inr c, .inr c' =>
      match Cylinder.inter? c c' with
      | some r => some (.inr r)
      | none => none
  | .case cc cl cr, .case cc' cl' cr' =>
      match Cylinder.inter? cc cc', Cylinder.inter? cl cl', Cylinder.inter? cr cr' with
      | some rc, some rl, some rr => some (.case rc rl rr)
      | _, _, _ => none
  | .alloc c, .alloc c' =>
      match Cylinder.inter? c c' with
      | some r => some (.alloc r)
      | none => none
  | .load c, .load c' =>
      match Cylinder.inter? c c' with
      | some r => some (.load r)
      | none => none
  | .store c₁ c₂, .store c₁' c₂' =>
      match Cylinder.inter? c₁ c₁', Cylinder.inter? c₂ c₂' with
      | some r₁, some r₂ => some (.store r₁ r₂)
      | _, _ => none
  | .tape c, .tape c' =>
      match Cylinder.inter? c c' with
      | some r => some (.tape r)
      | none => none
  | .rand c₁ c₂, .rand c₁' c₂' =>
      match Cylinder.inter? c₁ c₁', Cylinder.inter? c₂ c₂' with
      | some r₁, some r₂ => some (.rand r₁ r₂)
      | _, _ => none
  | .fail, .fail => some .fail
  | .urand, .urand => some .urand
  | .scrut c S, .scrut c' S' =>
      match Cylinder.inter? c c' with
      | some r => some (.scrut r (S ∩ S'))
      | none => none
  | _, _ => none

/-- Every element of a cylinder's flatten has that cylinder's shape. -/
theorem Cylinder.shape_of_mem_flatten {rT : Type _} {c : Cylinder rT} {e : Exp rT}
    (h : e ∈ Cylinder.flatten c) : Exp.shape e = Cylinder.shape c := by
  induction c generalizing e with
  | bvar _ | fvar _ | fail | urand => simp_all
  | lit _ => obtain ⟨_, _, rfl⟩ := h; rfl
  | lam _ ih | fix _ ih | fst _ ih | snd _ ih | inl _ ih | inr _ ih
  | alloc _ ih | load _ ih | tape _ ih =>
    obtain ⟨x, hx, rfl⟩ := h
    simp [Exp.shape, ih hx]
  | unop _ _ ih =>
    obtain ⟨x, hx, rfl⟩ := h
    simp [Exp.shape, ih hx]
  | app _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ | store _ _ ih₁ ih₂ | rand _ _ ih₁ ih₂ =>
    obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩ := h
    simp [Exp.shape, ih₁ hx, ih₂ hy]
  | binop _ _ _ ih₁ ih₂ =>
    obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩ := h
    simp [Exp.shape, ih₁ hx, ih₂ hy]
  | cond _ _ _ ih₁ ih₂ ih₃ | case _ _ _ ih₁ ih₂ ih₃ =>
    obtain ⟨⟨x, y, z⟩, ⟨hx, hy, hz⟩, rfl⟩ := h
    simp [Exp.shape, ih₁ hx, ih₂ hy, ih₃ hz]
  | scrut _ _ ih =>
    obtain ⟨⟨x, y⟩, ⟨hx, _⟩, rfl⟩ := h
    simp [Exp.shape, ih hx]

/-- Flattens of cylinders with different shapes are disjoint. -/
theorem Cylinder.flatten_disjoint_of_shape_ne {rT : Type _} {c₁ c₂ : Cylinder rT}
    (h : Cylinder.shape c₁ ≠ Cylinder.shape c₂) : Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ = ∅ :=
  Stamp.flatten_disjoint_of_shape_ne (cShape := Cylinder.shape)
    (fun {_ _} h => Cylinder.shape_of_mem_flatten h) h

/-- The cylinder flatten of the intersection equals the intersection of the flattens. -/
theorem Cylinder.flatten_inter {rT : Type _} (c₁ c₂ : Cylinder rT) :
    Cylinder.flatten c₁ ∩ Cylinder.flatten c₂
      = (Cylinder.inter? c₁ c₂).elim ∅ Cylinder.flatten := by
  induction c₁ generalizing c₂ with
  | bvar n₁ =>
    cases c₂
    case bvar n₂ => simp [Cylinder.inter?]; split_ifs <;> simp_all
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | fvar x₁ =>
    cases c₂
    case fvar x₂ => simp [Cylinder.inter?]; split_ifs <;> simp_all
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | lit S₁ =>
    cases c₂
    case lit S₂ =>
      simp only [Cylinder.flatten, Cylinder.inter?, Option.elim]
      exact Stamp.flatten_inter_data Exp.lit.ι.inj
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | lam c ih =>
    cases c₂
    case lam c' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_image₁ Exp.lam.ι.inj Cylinder.lam (fun _ => rfl) (ih c')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? c c' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | fix c ih =>
    cases c₂
    case fix c' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_image₁ Exp.fix.ι.inj Cylinder.fix (fun _ => rfl) (ih c')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? c c' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | app a b ih₁ ih₂ =>
    cases c₂
    case app a' b' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_image₂ Exp.app.ι.inj Cylinder.app (fun _ _ => rfl) (ih₁ a') (ih₂ b')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? a a' <;> cases Cylinder.inter? b b' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | unop u c ih =>
    cases c₂
    case unop u' c' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_mixed₁ (fun _ _ _ h => by injection h)
        (fun h => by injection h) Cylinder.unop (fun _ _ => rfl) (ih c')
        (by rw [Cylinder.inter?]; split <;> [cases Cylinder.inter? c c'; skip] <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | binop b a₁ a₂ ih₁ ih₂ =>
    cases c₂
    case binop b' a₁' a₂' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_mixed₂ (fun _ _ _ h => by injection h with _ h1 h2; exact Prod.ext h1 h2)
        (fun h => by injection h) Cylinder.binop (fun _ _ _ => rfl) (ih₁ a₁') (ih₂ a₂')
        (by rw [Cylinder.inter?]; split <;>
          [cases Cylinder.inter? a₁ a₁' <;> cases Cylinder.inter? a₂ a₂'; skip] <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | cond cc ct cf ihc iht ihf =>
    cases c₂
    case cond cc' ct' cf' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_image₃ Exp.cond.ι.inj Cylinder.cond (fun _ _ _ => rfl)
        (ihc cc') (iht ct') (ihf cf')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? cc cc' <;> cases Cylinder.inter? ct ct' <;>
          cases Cylinder.inter? cf cf' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | pair a b ih₁ ih₂ =>
    cases c₂
    case pair a' b' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_image₂ Exp.pair.ι.inj Cylinder.pair (fun _ _ => rfl) (ih₁ a') (ih₂ b')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? a a' <;> cases Cylinder.inter? b b' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | fst c ih =>
    cases c₂
    case fst c' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_image₁ Exp.fst.ι.inj Cylinder.fst (fun _ => rfl) (ih c')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? c c' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | snd c ih =>
    cases c₂
    case snd c' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_image₁ Exp.snd.ι.inj Cylinder.snd (fun _ => rfl) (ih c')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? c c' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | inl c ih =>
    cases c₂
    case inl c' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_image₁ Exp.inl.ι.inj Cylinder.inl (fun _ => rfl) (ih c')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? c c' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | inr c ih =>
    cases c₂
    case inr c' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_image₁ Exp.inr.ι.inj Cylinder.inr (fun _ => rfl) (ih c')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? c c' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | case cc cl cr ihc ihl ihr =>
    cases c₂
    case case cc' cl' cr' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_image₃ Exp.case.ι.inj Cylinder.case (fun _ _ _ => rfl)
        (ihc cc') (ihl cl') (ihr cr')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? cc cc' <;> cases Cylinder.inter? cl cl' <;>
          cases Cylinder.inter? cr cr' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | alloc c ih =>
    cases c₂
    case alloc c' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_image₁ Exp.alloc.ι.inj Cylinder.alloc (fun _ => rfl) (ih c')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? c c' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | load c ih =>
    cases c₂
    case load c' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_image₁ Exp.load.ι.inj Cylinder.load (fun _ => rfl) (ih c')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? c c' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | store a b ih₁ ih₂ =>
    cases c₂
    case store a' b' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_image₂ Exp.store.ι.inj Cylinder.store (fun _ _ => rfl) (ih₁ a') (ih₂ b')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? a a' <;> cases Cylinder.inter? b b' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | tape c ih =>
    cases c₂
    case tape c' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_image₁ Exp.tape.ι.inj Cylinder.tape (fun _ => rfl) (ih c')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? c c' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | rand a b ih₁ ih₂ =>
    cases c₂
    case rand a' b' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_image₂ Exp.rand.ι.inj Cylinder.rand (fun _ _ => rfl) (ih₁ a') (ih₂ b')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? a a' <;> cases Cylinder.inter? b b' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | fail =>
    cases c₂
    case fail => simp [Cylinder.inter?]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | urand =>
    cases c₂
    case urand => simp [Cylinder.inter?]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | scrut c S ih =>
    cases c₂
    case scrut c' S' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_scrut Exp.scrut.ι.inj Cylinder.scrut (fun _ _ => rfl) (ih c')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? c c' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)

theorem Cylinder.flatten_inter_some {rT : Type _} {c₁ c₂ c : Cylinder rT}
    (h : Cylinder.inter? c₁ c₂ = some c) :
    Cylinder.flatten c = Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ :=
  Stamp.flatten_inter_some Cylinder.flatten_inter h

/-- Inheritance of `HasMeasurableLeaves` under `Cylinder.inter?`.

Same per-constructor-linear shape as for `Pat` (`Pat.lean`): `induction c₁`, then for
each constructor `cases c₂` (off-diagonal dies on `inter? = none ≠ some c`), and the
diagonal `revert h; split <;> rintro ⟨rfl⟩` reduces the `inter?` `match`/`if` and
applies the constructor with the children's leaves from the IHs. No `grind`, no
heartbeat bump. -/
theorem Cylinder.hasMeasurableLeaves_inter [MeasurableSpace rT]
    {c₁ c₂ c : Cylinder rT}
    (h₁ : c₁.HasMeasurableLeaves) (h₂ : c₂.HasMeasurableLeaves)
    (h : Cylinder.inter? c₁ c₂ = some c) : c.HasMeasurableLeaves := by
  induction c₁ generalizing c₂ c with
  | bvar | fvar | fail | urand =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    all_goals first | (split at h <;> simp_all) | simp_all
  | lit S₁ =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    cases h₁; cases h₂; injection h with h; subst h; exact .lit _ (MeasurableSet.inter ‹_› ‹_›)
  | lam c ih | fix c ih | fst c ih | snd c ih | inl c ih | inr c ih
  | alloc c ih | load c ih | tape c ih =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    all_goals (
      cases h₁; cases h₂
      revert h; split <;> rintro ⟨rfl⟩; rename_i ha
      first
      | exact .lam (ih ‹_› ‹_› ha) | exact .fix (ih ‹_› ‹_› ha) | exact .fst (ih ‹_› ‹_› ha)
      | exact .snd (ih ‹_› ‹_› ha) | exact .inl (ih ‹_› ‹_› ha) | exact .inr (ih ‹_› ‹_› ha)
      | exact .alloc (ih ‹_› ‹_› ha) | exact .load (ih ‹_› ‹_› ha) | exact .tape (ih ‹_› ‹_› ha))
  | app a b iha ihb | pair a b iha ihb | store a b iha ihb | rand a b iha ihb =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    all_goals (
      cases h₁; cases h₂
      revert h; split <;> rintro ⟨rfl⟩; rename_i ha hb
      first
      | exact .app (iha ‹_› ‹_› ha) (ihb ‹_› ‹_› hb)
      | exact .pair (iha ‹_› ‹_› ha) (ihb ‹_› ‹_› hb)
      | exact .store (iha ‹_› ‹_› ha) (ihb ‹_› ‹_› hb)
      | exact .rand (iha ‹_› ‹_› ha) (ihb ‹_› ‹_› hb))
  | unop u c ih =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    cases h₁; cases h₂
    revert h; split <;> [split; skip] <;> rintro ⟨rfl⟩
    rename_i ha
    exact .unop (ih ‹_› ‹_› ha)
  | binop bo a b iha ihb =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    cases h₁; cases h₂
    revert h; split <;> [split; skip] <;> rintro ⟨rfl⟩
    rename_i ha hb
    exact .binop (iha ‹_› ‹_› ha) (ihb ‹_› ‹_› hb)
  | cond cc ct cf ihc iht ihf | case cc ct cf ihc iht ihf =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    all_goals (
      cases h₁; cases h₂
      revert h; split <;> rintro ⟨rfl⟩; rename_i hc ht hf
      first
      | exact .cond (ihc ‹_› ‹_› hc) (iht ‹_› ‹_› ht) (ihf ‹_› ‹_› hf)
      | exact .case (ihc ‹_› ‹_› hc) (iht ‹_› ‹_› ht) (ihf ‹_› ‹_› hf))
  | scrut c S ih =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    cases h₁; cases h₂
    revert h; split <;> rintro ⟨rfl⟩; rename_i ha
    exact .scrut _ (ih ‹_› ‹_› ha) (MeasurableSet.inter ‹_› ‹_›)

/-! ### Per-constructor covers. -/

@[stamp_simp] def cover.bvar (S : Set Nat) : Set (Exp rT) :=
  ⋃ n ∈ S, Cylinder.flatten (.bvar n)

@[stamp_simp] def cover.fvar (S : Set Var) : Set (Exp rT) :=
  ⋃ x ∈ S, Cylinder.flatten (.fvar x)

@[stamp_simp] def cover.lit (S : Set (BaseLit rT)) : Set (Exp rT) :=
  Cylinder.flatten (.lit S)

@[stamp_simp] def cover.lam (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.lam s.cylinder)

@[stamp_simp] def cover.fix (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.fix s.cylinder)

@[stamp_simp] def cover.app (S : Set (Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.app p.1.cylinder p.2.cylinder)

@[stamp_simp] def cover.unop (S : Set (UnOp × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.unop p.1 p.2.cylinder)

@[stamp_simp] def cover.binop (S : Set (BinOp × Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.binop p.1 p.2.1.cylinder p.2.2.cylinder)

@[stamp_simp] def cover.cond (S : Set (Shape × Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.cond p.1.cylinder p.2.1.cylinder p.2.2.cylinder)

@[stamp_simp] def cover.pair (S : Set (Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.pair p.1.cylinder p.2.cylinder)

@[stamp_simp] def cover.fst (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.fst s.cylinder)

@[stamp_simp] def cover.snd (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.snd s.cylinder)

@[stamp_simp] def cover.inl (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.inl s.cylinder)

@[stamp_simp] def cover.inr (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.inr s.cylinder)

@[stamp_simp] def cover.case (S : Set (Shape × Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.case p.1.cylinder p.2.1.cylinder p.2.2.cylinder)

@[stamp_simp] def cover.alloc (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.alloc s.cylinder)

@[stamp_simp] def cover.load (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.load s.cylinder)

@[stamp_simp] def cover.store (S : Set (Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.store p.1.cylinder p.2.cylinder)

@[stamp_simp] def cover.tape (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.tape s.cylinder)

@[stamp_simp] def cover.rand (S : Set (Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.rand p.1.cylinder p.2.cylinder)

@[stamp_simp] def cover.fail (S : Set Unit) : Set (Exp rT) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.fail : Cylinder rT)

@[stamp_simp] def cover.urand (S : Set Unit) : Set (Exp rT) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.urand : Cylinder rT)

@[stamp_simp] def cover.scrut (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.scrut s.cylinder Set.univ)

/-- Cylinder of a given shape has measurable leaves. -/
theorem Shape.cylinder_hasMeasurableLeaves [MeasurableSpace rT] (s : Shape) :
    (s.cylinder (rT := rT)).HasMeasurableLeaves := by
  induction s <;> constructor <;> measurability

/-- Flattening a cylinder of a shape equals set of terms with a given shape. -/
@[simp] theorem Shape.cylinder_preimage_shape (s : Shape) :
    (s.cylinder (rT := rT)).flatten = Exp.shape ⁻¹' {s} :=
  Stamp.cylinder_preimage_shape (cShape := Cylinder.shape)
    (fun {_ _} h => Cylinder.shape_of_mem_flatten h)
    (fun s => by induction s <;> simp_all)
    (fun p => by induction p <;> simp_all) s

/-- Flattening a cylinder gives a measurable set. -/
@[measurability]
theorem flatten_measurable [MeasurableSpace rT] {c : Cylinder rT}
    (hc : c.HasMeasurableLeaves) : MeasurableSet c.flatten :=
  Stamp.flatten_measurable rfl hc

attribute [aesop safe constructors (rule_sets := [Measurable])]
  ProbLang.Exp.Cylinder.HasMeasurableLeaves

attribute [aesop safe apply (rule_sets := [Measurable])]
  Shape.cylinder_hasMeasurableLeaves

/-! ### The cylinder flatten family is a π-system that spans `Exp rT`. -/

theorem Cylinder.flatten_isPiSystem [MeasurableSpace rT] :
    IsPiSystem
      ({S : Set (Exp rT) | ∃ c : Cylinder rT, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S}) :=
  Stamp.flatten_isPiSystem Cylinder.flatten_inter
    (fun {_ _ _} => Cylinder.hasMeasurableLeaves_inter)

theorem Cylinder.flatten_isCountablySpanning [MeasurableSpace rT] :
    IsCountablySpanning
      ({S : Set (Exp rT) | ∃ c : Cylinder rT, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S}) :=
  Stamp.flatten_isCountablySpanning Shape.cylinder_hasMeasurableLeaves
    Shape.cylinder_preimage_shape .fail .fail

/-! ### Measurability of the per-constructor covers. -/

@[measurability]
theorem cover.bvar.measurable [MeasurableSpace rT] (S : Set Nat) :
    MeasurableSet (bvar (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.fvar.measurable [MeasurableSpace rT] (S : Set Var) :
    MeasurableSet (fvar (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.lit.measurable [MeasurableSpace rT] {S : Set (BaseLit rT)} (hS : MeasurableSet S) :
    MeasurableSet (lit (rT := rT) S) :=
  flatten_measurable (.lit _ hS)

@[measurability]
theorem cover.lam.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (lam (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.fix.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (fix (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.app.measurable [MeasurableSpace rT] (S : Set (Shape × Shape)) :
    MeasurableSet (app (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.unop.measurable [MeasurableSpace rT] (S : Set (UnOp × Shape)) :
    MeasurableSet (unop (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.binop.measurable [MeasurableSpace rT] (S : Set (BinOp × Shape × Shape)) :
    MeasurableSet (binop (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.cond.measurable [MeasurableSpace rT] (S : Set (Shape × Shape × Shape)) :
    MeasurableSet (cond (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.pair.measurable [MeasurableSpace rT] (S : Set (Shape × Shape)) :
    MeasurableSet (pair (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.fst.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (fst (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.snd.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (snd (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.inl.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (inl (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.inr.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (inr (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.case.measurable [MeasurableSpace rT] (S : Set (Shape × Shape × Shape)) :
    MeasurableSet (case (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.alloc.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (alloc (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.load.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (load (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.store.measurable [MeasurableSpace rT] (S : Set (Shape × Shape)) :
    MeasurableSet (store (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.tape.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (tape (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.rand.measurable [MeasurableSpace rT] (S : Set (Shape × Shape)) :
    MeasurableSet (rand (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.fail.measurable [MeasurableSpace rT] (S : Set Unit) :
    MeasurableSet (fail (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.urand.measurable [MeasurableSpace rT] (S : Set Unit) :
    MeasurableSet (urand (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.scrut.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (scrut (rT := rT) S) := by solve_cover_measurable

theorem cover.bvar_eq_image (S : Set Nat) :
    cover.bvar (rT := rT) S = Exp.bvar '' S := by solve_cover_eq_image cover.bvar

theorem cover.fvar_eq_image (S : Set Var) :
    cover.fvar (rT := rT) S = Exp.fvar '' S := by solve_cover_eq_image cover.fvar

theorem cover.lit_eq_image (S : Set (BaseLit rT)) :
    cover.lit (rT := rT) S = Exp.lit '' S := by solve_cover_eq_image cover.lit

theorem cover.lam_univ_eq_range :
    cover.lam (rT := rT) Set.univ = .range (Exp.lam : Exp rT → Exp rT) := by
  solve_cover_eq_image cover.lam

theorem cover.fix_univ_eq_range :
    cover.fix (rT := rT) Set.univ = .range (Exp.fix : Exp rT → Exp rT) := by
  solve_cover_eq_image cover.fix

theorem cover.app_univ_eq_range :
    cover.app (rT := rT) Set.univ = .range (Function.uncurry Exp.app) := by
  solve_cover_eq_image cover.app

theorem cover.unop_univ_eq_range :
    cover.unop (rT := rT) Set.univ = .range (Function.uncurry Exp.unop) := by
  solve_cover_eq_image cover.unop

theorem cover.binop_univ_eq_range :
    cover.binop (rT := rT) Set.univ
      = .range (fun (p : BinOp × Exp rT × Exp rT) => Exp.binop p.1 p.2.1 p.2.2) := by
  solve_cover_eq_image cover.binop

theorem cover.cond_univ_eq_range :
    cover.cond (rT := rT) Set.univ
      = .range (fun (p : Exp rT × Exp rT × Exp rT) => Exp.cond p.1 p.2.1 p.2.2) := by
  solve_cover_eq_image cover.cond

theorem cover.pair_univ_eq_range :
    cover.pair (rT := rT) Set.univ = .range (Function.uncurry Exp.pair) := by
  solve_cover_eq_image cover.pair

theorem cover.fst_univ_eq_range :
    cover.fst (rT := rT) Set.univ = .range (Exp.fst : Exp rT → Exp rT) := by
  solve_cover_eq_image cover.fst

theorem cover.snd_univ_eq_range :
    cover.snd (rT := rT) Set.univ = .range (Exp.snd : Exp rT → Exp rT) := by
  solve_cover_eq_image cover.snd

theorem cover.inl_univ_eq_range :
    cover.inl (rT := rT) Set.univ = .range (Exp.inl : Exp rT → Exp rT) := by
  solve_cover_eq_image cover.inl

theorem cover.inr_univ_eq_range :
    cover.inr (rT := rT) Set.univ = .range (Exp.inr : Exp rT → Exp rT) := by
  solve_cover_eq_image cover.inr

theorem cover.case_univ_eq_range :
    cover.case (rT := rT) Set.univ
      = .range (fun (p : Exp rT × Exp rT × Exp rT) => Exp.case p.1 p.2.1 p.2.2) := by
  solve_cover_eq_image cover.case

theorem cover.alloc_univ_eq_range :
    cover.alloc (rT := rT) Set.univ = .range (Exp.alloc : Exp rT → Exp rT) := by
  solve_cover_eq_image cover.alloc

theorem cover.load_univ_eq_range :
    cover.load (rT := rT) Set.univ = .range (Exp.load : Exp rT → Exp rT) := by
  solve_cover_eq_image cover.load

theorem cover.store_univ_eq_range :
    cover.store (rT := rT) Set.univ = .range (Function.uncurry Exp.store) := by
  solve_cover_eq_image cover.store

theorem cover.tape_univ_eq_range :
    cover.tape (rT := rT) Set.univ = .range (Exp.tape : Exp rT → Exp rT) := by
  solve_cover_eq_image cover.tape

theorem cover.rand_univ_eq_range :
    cover.rand (rT := rT) Set.univ = .range (Function.uncurry Exp.rand) := by
  solve_cover_eq_image cover.rand

theorem cover.fail_eq_image (S : Set Unit) :
    cover.fail (rT := rT) S = (fun _ : Unit => (Exp.fail : Exp rT)) '' S := by
  solve_cover_eq_image cover.fail

theorem cover.urand_eq_image (S : Set Unit) :
    cover.urand (rT := rT) S = (fun _ : Unit => (Exp.urand : Exp rT)) '' S := by
  solve_cover_eq_image cover.urand

theorem cover.scrut_univ_eq_range :
    cover.scrut (rT := rT) Set.univ = .range (Function.uncurry Exp.scrut) := by
  solve_cover_eq_image cover.scrut

/-! ### Measurable constructors. -/

@[fun_prop]
theorem bvar.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (Exp.bvar.ι (rT := rT)) := (by measurability)

@[fun_prop]
theorem fvar.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (Exp.fvar.ι (rT := rT)) := (by measurability)

@[fun_prop]
theorem fail.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (Exp.fail.ι (rT := rT)) := (by measurability)

@[fun_prop]
theorem urand.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (Exp.urand.ι (rT := rT)) := (by measurability)

@[fun_prop]
theorem lit.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (Exp.lit.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @lit S hS =>
    suffices h : Exp.lit.ι ⁻¹' Cylinder.flatten (.lit S) = S by rw [h]; exact hS
    ext b; simp
  | _ => convert MeasurableSet.empty; ext b; simp

@[fun_prop]
theorem lam.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.lam.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @lam c h =>
    suffices heq : Exp.lam.ι ⁻¹' Cylinder.flatten (.lam c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem fix.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.fix.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @fix c h =>
    suffices heq : Exp.fix.ι ⁻¹' Cylinder.flatten (.fix c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem app.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.app.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @app c₁ c₂ h₁ h₂ =>
    suffices h : Exp.app.ι ⁻¹' Cylinder.flatten (.app c₁ c₂)
                = Cylinder.flatten c₁ ×ˢ Cylinder.flatten c₂ by rw [h]; measurability
    ext ⟨_, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop]
theorem fst.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.fst.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @fst c h =>
    suffices heq : Exp.fst.ι ⁻¹' Cylinder.flatten (.fst c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem snd.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.snd.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @snd c h =>
    suffices heq : Exp.snd.ι ⁻¹' Cylinder.flatten (.snd c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem inl.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.inl.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @inl c h =>
    suffices heq : Exp.inl.ι ⁻¹' Cylinder.flatten (.inl c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem inr.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.inr.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @inr c h =>
    suffices heq : Exp.inr.ι ⁻¹' Cylinder.flatten (.inr c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem alloc.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.alloc.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @alloc c h =>
    suffices heq : Exp.alloc.ι ⁻¹' Cylinder.flatten (.alloc c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem load.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.load.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @load c h =>
    suffices heq : Exp.load.ι ⁻¹' Cylinder.flatten (.load c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem tape.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.tape.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @tape c h =>
    suffices heq : Exp.tape.ι ⁻¹' Cylinder.flatten (.tape c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem pair.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.pair.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @pair c₁ c₂ h₁ h₂ =>
    suffices h : Exp.pair.ι ⁻¹' Cylinder.flatten (.pair c₁ c₂)
                = Cylinder.flatten c₁ ×ˢ Cylinder.flatten c₂ by rw [h]; measurability
    ext ⟨_, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop]
theorem store.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.store.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @store c₁ c₂ h₁ h₂ =>
    suffices h : Exp.store.ι ⁻¹' Cylinder.flatten (.store c₁ c₂)
                = Cylinder.flatten c₁ ×ˢ Cylinder.flatten c₂ by rw [h]; measurability
    ext ⟨_, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop]
theorem rand.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.rand.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @rand c₁ c₂ h₁ h₂ =>
    suffices h : Exp.rand.ι ⁻¹' Cylinder.flatten (.rand c₁ c₂)
                = Cylinder.flatten c₁ ×ˢ Cylinder.flatten c₂ by rw [h]; measurability
    ext ⟨_, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop]
theorem cond.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.cond.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @cond cc ct cf hc' ht hf =>
    suffices h : Exp.cond.ι ⁻¹' Cylinder.flatten (.cond cc ct cf)
                = Cylinder.flatten cc ×ˢ Cylinder.flatten ct ×ˢ Cylinder.flatten cf by
      rw [h]; measurability
    ext ⟨_, _, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _, _⟩; simp

@[fun_prop]
theorem case.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.case.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @case cc cl cr hc' hl hr =>
    suffices h : Exp.case.ι ⁻¹' Cylinder.flatten (.case cc cl cr)
                = Cylinder.flatten cc ×ˢ Cylinder.flatten cl ×ˢ Cylinder.flatten cr by
      rw [h]; measurability
    ext ⟨_, _, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _, _⟩; simp

@[fun_prop]
theorem unop.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.unop.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @unop c u h =>
    suffices heq : Exp.unop.ι ⁻¹' Cylinder.flatten (.unop u c)
                = ({u} : Set UnOp) ×ˢ Cylinder.flatten c by rw [heq]; measurability
    ext ⟨_, _⟩; simp; tauto
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop]
theorem binop.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.binop.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @binop c₁ c₂ b h₁ h₂ =>
    suffices heq : Exp.binop.ι ⁻¹' Cylinder.flatten (.binop b c₁ c₂)
                = ({b} : Set BinOp) ×ˢ Cylinder.flatten c₁ ×ˢ Cylinder.flatten c₂ by
      rw [heq]; measurability
    ext ⟨_, _, _⟩; simp; tauto
  | _ => convert MeasurableSet.empty; ext ⟨_, _, _⟩; simp

@[fun_prop]
theorem scrut.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.scrut.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @scrut c S h hS =>
    suffices heq : Exp.scrut.ι ⁻¹' Cylinder.flatten (.scrut c S)
                = Cylinder.flatten c ×ˢ S by rw [heq]; measurability
    ext ⟨_, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

/-! ### Raw-constructor `fun_prop` lemmas.

`.ι` is the auto-generated η-expanded uncurried form. The `fun_prop`-tagged lemmas
above target `.ι` as the head symbol, so they don't fire when the user writes the
raw constructor. We re-tag for the raw form. -/

@[fun_prop]
theorem bvar.measurable [MeasurableSpace rT] :
    Measurable (Exp.bvar : Nat → Exp rT) := bvar.ι.measurable

@[fun_prop]
theorem fvar.measurable [MeasurableSpace rT] :
    Measurable (Exp.fvar : Var → Exp rT) := fvar.ι.measurable

@[fun_prop]
theorem lit.measurable [MeasurableSpace rT] :
    Measurable (Exp.lit : BaseLit rT → Exp rT) := lit.ι.measurable

@[fun_prop]
theorem lam.measurable [MeasurableSpace rT] :
    Measurable (Exp.lam : Exp rT → Exp rT) := lam.ι.measurable

@[fun_prop]
theorem fix.measurable [MeasurableSpace rT] :
    Measurable (Exp.fix : Exp rT → Exp rT) := fix.ι.measurable

@[fun_prop]
theorem app.measurable [MeasurableSpace rT] :
    Measurable (Function.uncurry (Exp.app : Exp rT → Exp rT → Exp rT)) := app.ι.measurable

@[fun_prop]
theorem fst.measurable [MeasurableSpace rT] :
    Measurable (Exp.fst : Exp rT → Exp rT) := fst.ι.measurable

@[fun_prop]
theorem snd.measurable [MeasurableSpace rT] :
    Measurable (Exp.snd : Exp rT → Exp rT) := snd.ι.measurable

@[fun_prop]
theorem inl.measurable [MeasurableSpace rT] :
    Measurable (Exp.inl : Exp rT → Exp rT) := inl.ι.measurable

@[fun_prop]
theorem inr.measurable [MeasurableSpace rT] :
    Measurable (Exp.inr : Exp rT → Exp rT) := inr.ι.measurable

@[fun_prop]
theorem alloc.measurable [MeasurableSpace rT] :
    Measurable (Exp.alloc : Exp rT → Exp rT) := alloc.ι.measurable

@[fun_prop]
theorem load.measurable [MeasurableSpace rT] :
    Measurable (Exp.load : Exp rT → Exp rT) := load.ι.measurable

@[fun_prop]
theorem tape.measurable [MeasurableSpace rT] :
    Measurable (Exp.tape : Exp rT → Exp rT) := tape.ι.measurable

@[fun_prop]
theorem pair.measurable [MeasurableSpace rT] :
    Measurable (Function.uncurry (Exp.pair : Exp rT → Exp rT → Exp rT)) := pair.ι.measurable

@[fun_prop]
theorem store.measurable [MeasurableSpace rT] :
    Measurable (Function.uncurry (Exp.store : Exp rT → Exp rT → Exp rT)) := store.ι.measurable

@[fun_prop]
theorem rand.measurable [MeasurableSpace rT] :
    Measurable (Function.uncurry (Exp.rand : Exp rT → Exp rT → Exp rT)) := rand.ι.measurable

@[fun_prop]
theorem cond.measurable [MeasurableSpace rT] :
    Measurable (fun (p : Exp rT × Exp rT × Exp rT) => Exp.cond p.1 p.2.1 p.2.2) :=
  cond.ι.measurable

@[fun_prop]
theorem case.measurable [MeasurableSpace rT] :
    Measurable (fun (p : Exp rT × Exp rT × Exp rT) => Exp.case p.1 p.2.1 p.2.2) :=
  case.ι.measurable

@[fun_prop]
theorem unop.measurable [MeasurableSpace rT] :
    Measurable (Function.uncurry (Exp.unop : UnOp → Exp rT → Exp rT)) := unop.ι.measurable

@[fun_prop]
theorem binop.measurable [MeasurableSpace rT] :
    Measurable (fun (p : BinOp × Exp rT × Exp rT) => Exp.binop p.1 p.2.1 p.2.2) :=
  binop.ι.measurable

@[fun_prop]
theorem scrut.measurable [MeasurableSpace rT] :
    Measurable (Function.uncurry (Exp.scrut : Exp rT → Pat rT → Exp rT)) := scrut.ι.measurable

/-! ### Measurable embeddings. -/

theorem bvar.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.bvar : Nat → Exp rT) := by
  solve_discrete_ME cover.bvar_eq_image, cover.bvar.measurable

theorem fvar.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.fvar : Var → Exp rT) := by
  solve_discrete_ME cover.fvar_eq_image, cover.fvar.measurable

theorem fail.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (fun _ : Unit => (Exp.fail : Exp rT)) := by
  apply MeasurableEmbedding.of_measurable_inverse (g := fun _ => ())
  · exact measurable_const
  · rw [show Set.range (fun _ : Unit => (Exp.fail : Exp rT)) = cover.fail .univ from by
             rw [cover.fail_eq_image]; ext; simp]
    exact cover.fail.measurable _
  · exact measurable_const
  · intro; rfl

theorem urand.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (fun _ : Unit => (Exp.urand : Exp rT)) := by
  apply MeasurableEmbedding.of_measurable_inverse (g := fun _ => ())
  · exact measurable_const
  · rw [show Set.range (fun _ : Unit => (Exp.urand : Exp rT)) = cover.urand .univ from by
             rw [cover.urand_eq_image]; ext; simp]
    exact cover.urand.measurable _
  · exact measurable_const
  · intro; rfl

theorem lit.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.lit : BaseLit rT → Exp rT) :=
  ⟨fun _ _ h => by injection h, Exp.lit.ι.measurable,
    fun _ hS => flatten_measurable (.lit _ hS)⟩

theorem lam.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.lam : Exp rT → Exp rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Exp.lam.ι.inj) (h_meas := Exp.lam.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.lam hc))
    (h_cov_meas := cover.lam.measurable _) (h_cov_range := cover.lam_univ_eq_range)

theorem fix.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.fix : Exp rT → Exp rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Exp.fix.ι.inj) (h_meas := Exp.fix.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.fix hc))
    (h_cov_meas := cover.fix.measurable _) (h_cov_range := cover.fix_univ_eq_range)

theorem fst.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.fst : Exp rT → Exp rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Exp.fst.ι.inj) (h_meas := Exp.fst.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.fst hc))
    (h_cov_meas := cover.fst.measurable _) (h_cov_range := cover.fst_univ_eq_range)

theorem snd.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.snd : Exp rT → Exp rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Exp.snd.ι.inj) (h_meas := Exp.snd.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.snd hc))
    (h_cov_meas := cover.snd.measurable _) (h_cov_range := cover.snd_univ_eq_range)

theorem inl.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.inl : Exp rT → Exp rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Exp.inl.ι.inj) (h_meas := Exp.inl.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.inl hc))
    (h_cov_meas := cover.inl.measurable _) (h_cov_range := cover.inl_univ_eq_range)

theorem inr.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.inr : Exp rT → Exp rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Exp.inr.ι.inj) (h_meas := Exp.inr.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.inr hc))
    (h_cov_meas := cover.inr.measurable _) (h_cov_range := cover.inr_univ_eq_range)

theorem alloc.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.alloc : Exp rT → Exp rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Exp.alloc.ι.inj) (h_meas := Exp.alloc.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.alloc hc))
    (h_cov_meas := cover.alloc.measurable _) (h_cov_range := cover.alloc_univ_eq_range)

theorem load.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.load : Exp rT → Exp rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Exp.load.ι.inj) (h_meas := Exp.load.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.load hc))
    (h_cov_meas := cover.load.measurable _) (h_cov_range := cover.load_univ_eq_range)

theorem tape.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.tape : Exp rT → Exp rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Exp.tape.ι.inj) (h_meas := Exp.tape.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.tape hc))
    (h_cov_meas := cover.tape.measurable _) (h_cov_range := cover.tape_univ_eq_range)

theorem app.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Function.uncurry (Exp.app : Exp rT → Exp rT → Exp rT)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := Exp.app.ι.inj) (h_meas := Exp.app.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl rfl
                Cylinder.flatten_isCountablySpanning Cylinder.flatten_isCountablySpanning).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩; exact flatten_measurable (.app hc₁ hc₂))
    (h_cov_meas := cover.app.measurable _) (h_cov_range := cover.app_univ_eq_range)

theorem pair.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Function.uncurry (Exp.pair : Exp rT → Exp rT → Exp rT)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := Exp.pair.ι.inj) (h_meas := Exp.pair.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl rfl
                Cylinder.flatten_isCountablySpanning Cylinder.flatten_isCountablySpanning).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩; exact flatten_measurable (.pair hc₁ hc₂))
    (h_cov_meas := cover.pair.measurable _) (h_cov_range := cover.pair_univ_eq_range)

theorem store.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Function.uncurry (Exp.store : Exp rT → Exp rT → Exp rT)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := Exp.store.ι.inj) (h_meas := Exp.store.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl rfl
                Cylinder.flatten_isCountablySpanning Cylinder.flatten_isCountablySpanning).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩; exact flatten_measurable (.store hc₁ hc₂))
    (h_cov_meas := cover.store.measurable _) (h_cov_range := cover.store_univ_eq_range)

theorem rand.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Function.uncurry (Exp.rand : Exp rT → Exp rT → Exp rT)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := Exp.rand.ι.inj) (h_meas := Exp.rand.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl rfl
                Cylinder.flatten_isCountablySpanning Cylinder.flatten_isCountablySpanning).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩; exact flatten_measurable (.rand hc₁ hc₂))
    (h_cov_meas := cover.rand.measurable _) (h_cov_range := cover.rand_univ_eq_range)

theorem cond.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (fun (p : Exp rT × Exp rT × Exp rT) => Exp.cond p.1 p.2.1 p.2.2) :=
  measurableEmbedding_of_piSystem₃
    (h_inj := Exp.cond.ι.inj) (h_meas := Exp.cond.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl
                (generateFrom_eq_prod rfl rfl
                  Cylinder.flatten_isCountablySpanning Cylinder.flatten_isCountablySpanning)
                Cylinder.flatten_isCountablySpanning
                (Cylinder.flatten_isCountablySpanning.prod Cylinder.flatten_isCountablySpanning)).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod
              (Cylinder.flatten_isPiSystem.prod Cylinder.flatten_isPiSystem))
    (h_basic := by
      rintro _ ⟨cc, hcc, rfl⟩ _ ⟨ct, hct, rfl⟩ _ ⟨cf, hcf, rfl⟩
      rw [show ((fun p : Exp rT × Exp rT × Exp rT => Exp.cond p.1 p.2.1 p.2.2)
            '' (Cylinder.flatten cc ×ˢ Cylinder.flatten ct ×ˢ Cylinder.flatten cf))
            = Cylinder.flatten (.cond cc ct cf) from by
          ext e; cases e <;> simp]
      exact flatten_measurable (.cond hcc hct hcf))
    (h_cov_meas := cover.cond.measurable _) (h_cov_range := cover.cond_univ_eq_range)

theorem case.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (fun (p : Exp rT × Exp rT × Exp rT) => Exp.case p.1 p.2.1 p.2.2) :=
  measurableEmbedding_of_piSystem₃
    (h_inj := Exp.case.ι.inj) (h_meas := Exp.case.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl
                (generateFrom_eq_prod rfl rfl
                  Cylinder.flatten_isCountablySpanning Cylinder.flatten_isCountablySpanning)
                Cylinder.flatten_isCountablySpanning
                (Cylinder.flatten_isCountablySpanning.prod Cylinder.flatten_isCountablySpanning)).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod
              (Cylinder.flatten_isPiSystem.prod Cylinder.flatten_isPiSystem))
    (h_basic := by
      rintro _ ⟨cc, hcc, rfl⟩ _ ⟨cl, hcl, rfl⟩ _ ⟨cr, hcr, rfl⟩
      rw [show ((fun p : Exp rT × Exp rT × Exp rT => Exp.case p.1 p.2.1 p.2.2)
            '' (Cylinder.flatten cc ×ˢ Cylinder.flatten cl ×ˢ Cylinder.flatten cr))
            = Cylinder.flatten (.case cc cl cr) from by
          ext e; cases e <;> simp]
      exact flatten_measurable (.case hcc hcl hcr))
    (h_cov_meas := cover.case.measurable _) (h_cov_range := cover.case_univ_eq_range)

theorem unop.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Function.uncurry (Exp.unop : UnOp → Exp rT → Exp rT)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := Exp.unop.ι.inj) (h_meas := Exp.unop.ι.measurable)
    (h_gen := (generateFrom_eq_prod singletonsAndUniv_generateFrom rfl
                singletonsAndUniv_isCountablySpanning Cylinder.flatten_isCountablySpanning).symm)
    (h_pi := singletonsAndUniv_isPiSystem.prod Cylinder.flatten_isPiSystem)
    (h_basic := by
      rintro A hA _ ⟨c, hc, rfl⟩
      rcases hA with rfl | ⟨u, rfl⟩
      · -- A = univ
        rw [show ((Function.uncurry Exp.unop) '' (Set.univ ×ˢ Cylinder.flatten c) : Set (Exp rT))
              = ⋃ u : UnOp, Exp.unop u '' Cylinder.flatten c from by
            ext e; simp [Function.uncurry]]
        exact .iUnion fun u => flatten_measurable (.unop (u := u) hc)
      · -- A = {u}
        rw [show ((Function.uncurry Exp.unop) '' (({u} : Set UnOp) ×ˢ Cylinder.flatten c) : Set (Exp rT))
              = Cylinder.flatten (.unop u c) from by ext e; cases e <;> simp [Function.uncurry]]
        exact flatten_measurable (.unop hc))
    (h_cov_meas := cover.unop.measurable _) (h_cov_range := cover.unop_univ_eq_range)

theorem binop.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (fun (p : BinOp × Exp rT × Exp rT) => Exp.binop p.1 p.2.1 p.2.2) :=
  measurableEmbedding_of_piSystem₃
    (h_inj := Exp.binop.ι.inj) (h_meas := Exp.binop.ι.measurable)
    (h_gen := (generateFrom_eq_prod singletonsAndUniv_generateFrom
                (generateFrom_eq_prod rfl rfl
                  Cylinder.flatten_isCountablySpanning Cylinder.flatten_isCountablySpanning)
                singletonsAndUniv_isCountablySpanning
                (Cylinder.flatten_isCountablySpanning.prod Cylinder.flatten_isCountablySpanning)).symm)
    (h_pi := singletonsAndUniv_isPiSystem.prod
              (Cylinder.flatten_isPiSystem.prod Cylinder.flatten_isPiSystem))
    (h_basic := by
      rintro A hA _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩
      rcases hA with rfl | ⟨b, rfl⟩
      · rw [show ((fun p : BinOp × Exp rT × Exp rT => Exp.binop p.1 p.2.1 p.2.2)
              '' (Set.univ ×ˢ Cylinder.flatten c₁ ×ˢ Cylinder.flatten c₂))
              = ⋃ b : BinOp, Cylinder.flatten (.binop b c₁ c₂) from by
            ext e; cases e <;> simp]
        exact .iUnion fun b => flatten_measurable (.binop hc₁ hc₂)
      · rw [show ((fun p : BinOp × Exp rT × Exp rT => Exp.binop p.1 p.2.1 p.2.2)
              '' (({b} : Set BinOp) ×ˢ Cylinder.flatten c₁ ×ˢ Cylinder.flatten c₂))
              = Cylinder.flatten (.binop b c₁ c₂) from by
            ext e; cases e <;> simp; tauto]
        exact flatten_measurable (.binop hc₁ hc₂))
    (h_cov_meas := cover.binop.measurable _) (h_cov_range := cover.binop_univ_eq_range)

theorem scrut.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Function.uncurry (Exp.scrut : Exp rT → Pat rT → Exp rT)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := Exp.scrut.ι.inj) (h_meas := Exp.scrut.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl MeasurableSpace.generateFrom_measurableSet
                Cylinder.flatten_isCountablySpanning isCountablySpanning_measurableSet).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod
              (fun S (hS : MeasurableSet S) T (hT : MeasurableSet T) _ => hS.inter hT))
    (h_basic := by
      rintro _ ⟨c, hc, rfl⟩ S (hS : MeasurableSet S)
      rw [show ((Function.uncurry Exp.scrut) '' (Cylinder.flatten c ×ˢ S) : Set (Exp rT))
            = Cylinder.flatten (.scrut c S) from by ext e; cases e <;> simp [Function.uncurry]]
      exact flatten_measurable (.scrut _ hc hS))
    (h_cov_meas := cover.scrut.measurable _) (h_cov_range := cover.scrut_univ_eq_range)

/-- Per-constructor cell family for the `casesOn` preimage decomposition. -/
def decompCell
    {rT : Type _} {α : Type _} (S : Set α)
    (f_bvar : Nat → α) (f_fvar : Var → α) (f_lit : BaseLit rT → α)
    (f_lam : Exp rT → α) (f_fix : Exp rT → α)
    (f_app : Exp rT × Exp rT → α)
    (f_unop : UnOp × Exp rT → α) (f_binop : BinOp × Exp rT × Exp rT → α)
    (f_cond : Exp rT × Exp rT × Exp rT → α)
    (f_pair : Exp rT × Exp rT → α)
    (f_fst : Exp rT → α) (f_snd : Exp rT → α)
    (f_inl : Exp rT → α) (f_inr : Exp rT → α)
    (f_case : Exp rT × Exp rT × Exp rT → α)
    (f_alloc : Exp rT → α) (f_load : Exp rT → α) (f_store : Exp rT × Exp rT → α)
    (f_tape : Exp rT → α) (f_rand : Exp rT × Exp rT → α)
    (f_fail : Unit → α) (f_urand : Unit → α)
    (f_scrut : Exp rT × Pat rT → α) : Fin 23 → Set (Exp rT) :=
  ![ Exp.bvar.ι  '' (f_bvar  ⁻¹' S)
   , Exp.fvar.ι  '' (f_fvar  ⁻¹' S)
   , Exp.lit.ι   '' (f_lit   ⁻¹' S)
   , Exp.lam.ι   '' (f_lam   ⁻¹' S)
   , Exp.fix.ι   '' (f_fix   ⁻¹' S)
   , Exp.app.ι   '' (f_app   ⁻¹' S)
   , Exp.unop.ι  '' (f_unop  ⁻¹' S)
   , Exp.binop.ι '' (f_binop ⁻¹' S)
   , Exp.cond.ι  '' (f_cond  ⁻¹' S)
   , Exp.pair.ι  '' (f_pair  ⁻¹' S)
   , Exp.fst.ι   '' (f_fst   ⁻¹' S)
   , Exp.snd.ι   '' (f_snd   ⁻¹' S)
   , Exp.inl.ι   '' (f_inl   ⁻¹' S)
   , Exp.inr.ι   '' (f_inr   ⁻¹' S)
   , Exp.case.ι  '' (f_case  ⁻¹' S)
   , Exp.alloc.ι '' (f_alloc ⁻¹' S)
   , Exp.load.ι  '' (f_load  ⁻¹' S)
   , Exp.store.ι '' (f_store ⁻¹' S)
   , Exp.tape.ι  '' (f_tape  ⁻¹' S)
   , Exp.rand.ι  '' (f_rand  ⁻¹' S)
   , Exp.fail.ι  '' (f_fail  ⁻¹' S)
   , Exp.urand.ι '' (f_urand ⁻¹' S)
   , Exp.scrut.ι '' (f_scrut ⁻¹' S) ]

theorem casesOn_preimage_decomp
    {rT : Type _} {α : Type _} (S : Set α)
    (f_bvar : Nat → α) (f_fvar : Var → α) (f_lit : BaseLit rT → α)
    (f_lam : Exp rT → α) (f_fix : Exp rT → α)
    (f_app : Exp rT × Exp rT → α)
    (f_unop : UnOp × Exp rT → α) (f_binop : BinOp × Exp rT × Exp rT → α)
    (f_cond : Exp rT × Exp rT × Exp rT → α)
    (f_pair : Exp rT × Exp rT → α)
    (f_fst : Exp rT → α) (f_snd : Exp rT → α)
    (f_inl : Exp rT → α) (f_inr : Exp rT → α)
    (f_case : Exp rT × Exp rT × Exp rT → α)
    (f_alloc : Exp rT → α) (f_load : Exp rT → α) (f_store : Exp rT × Exp rT → α)
    (f_tape : Exp rT → α) (f_rand : Exp rT × Exp rT → α)
    (f_fail : Unit → α) (f_urand : Unit → α)
    (f_scrut : Exp rT × Pat rT → α) :
    (fun e : Exp rT => Exp.casesOn (motive := fun _ => α) e
        f_bvar f_fvar f_lit f_lam f_fix
        (fun e1 e2 => f_app (e1, e2))
        (fun u e => f_unop (u, e))
        (fun b e1 e2 => f_binop (b, e1, e2))
        (fun ec et ef => f_cond (ec, et, ef))
        (fun e1 e2 => f_pair (e1, e2))
        f_fst f_snd f_inl f_inr
        (fun ec el er => f_case (ec, el, er))
        f_alloc f_load
        (fun e1 e2 => f_store (e1, e2))
        f_tape
        (fun e1 e2 => f_rand (e1, e2))
        (f_fail ())
        (f_urand ())
        (fun e p => f_scrut (e, p))) ⁻¹' S
      = ⋃ i, decompCell S f_bvar f_fvar f_lit f_lam f_fix f_app f_unop f_binop
          f_cond f_pair f_fst f_snd f_inl f_inr f_case f_alloc f_load f_store
          f_tape f_rand f_fail f_urand f_scrut i := by
  ext e
  simp only [Set.mem_preimage, Set.mem_iUnion, decompCell]
  constructor
  · intro he; cases e
    · exact ⟨0, _, he, rfl⟩
    · exact ⟨1, _, he, rfl⟩
    · exact ⟨2, _, he, rfl⟩
    · exact ⟨3, _, he, rfl⟩
    · exact ⟨4, _, he, rfl⟩
    · exact ⟨5, ⟨_, _⟩, he, rfl⟩
    · exact ⟨6, ⟨_, _⟩, he, rfl⟩
    · exact ⟨7, ⟨_, _, _⟩, he, rfl⟩
    · exact ⟨8, ⟨_, _, _⟩, he, rfl⟩
    · exact ⟨9, ⟨_, _⟩, he, rfl⟩
    · exact ⟨10, _, he, rfl⟩
    · exact ⟨11, _, he, rfl⟩
    · exact ⟨12, _, he, rfl⟩
    · exact ⟨13, _, he, rfl⟩
    · exact ⟨14, ⟨_, _, _⟩, he, rfl⟩
    · exact ⟨15, _, he, rfl⟩
    · exact ⟨16, _, he, rfl⟩
    · exact ⟨17, ⟨_, _⟩, he, rfl⟩
    · exact ⟨18, _, he, rfl⟩
    · exact ⟨19, ⟨_, _⟩, he, rfl⟩
    · exact ⟨20, (), he, rfl⟩
    · exact ⟨21, (), he, rfl⟩
    · exact ⟨22, ⟨_, _⟩, he, rfl⟩
  · rintro ⟨i, hi⟩; fin_cases i <;>
      · obtain ⟨q, hq, hp⟩ := hi; cases hp; simpa using hq

@[fun_prop]
theorem measurable_rec
    {rT : Type _} [MeasurableSpace rT]
    {α : Type _} [MeasurableSpace α]
    (f_bvar : Nat → α) (f_fvar : Var → α) (f_lit : BaseLit rT → α)
    (f_lam : Exp rT → α) (f_fix : Exp rT → α)
    (f_app : Exp rT × Exp rT → α)
    (f_unop : UnOp × Exp rT → α) (f_binop : BinOp × Exp rT × Exp rT → α)
    (f_cond : Exp rT × Exp rT × Exp rT → α)
    (f_pair : Exp rT × Exp rT → α)
    (f_fst : Exp rT → α) (f_snd : Exp rT → α)
    (f_inl : Exp rT → α) (f_inr : Exp rT → α)
    (f_case : Exp rT × Exp rT × Exp rT → α)
    (f_alloc : Exp rT → α) (f_load : Exp rT → α) (f_store : Exp rT × Exp rT → α)
    (f_tape : Exp rT → α) (f_rand : Exp rT × Exp rT → α)
    (f_fail : Unit → α) (f_urand : Unit → α)
    (f_scrut : Exp rT × Pat rT → α)
    (h_lit : Measurable f_lit)
    (h_lam : Measurable f_lam) (h_fix : Measurable f_fix)
    (h_app : Measurable f_app) (h_unop : Measurable f_unop) (h_binop : Measurable f_binop)
    (h_cond : Measurable f_cond)
    (h_pair : Measurable f_pair) (h_fst : Measurable f_fst) (h_snd : Measurable f_snd)
    (h_inl : Measurable f_inl) (h_inr : Measurable f_inr)
    (h_case : Measurable f_case)
    (h_alloc : Measurable f_alloc) (h_load : Measurable f_load) (h_store : Measurable f_store)
    (h_tape : Measurable f_tape) (h_rand : Measurable f_rand)
    (h_scrut : Measurable f_scrut) :
    Measurable (fun e : Exp rT =>
      Exp.casesOn (motive := fun _ => α) e
        f_bvar f_fvar f_lit f_lam f_fix
        (fun e1 e2 => f_app (e1, e2))
        (fun u e => f_unop (u, e))
        (fun b e1 e2 => f_binop (b, e1, e2))
        (fun ec et ef => f_cond (ec, et, ef))
        (fun e1 e2 => f_pair (e1, e2))
        f_fst f_snd f_inl f_inr
        (fun ec el er => f_case (ec, el, er))
        f_alloc f_load
        (fun e1 e2 => f_store (e1, e2))
        f_tape
        (fun e1 e2 => f_rand (e1, e2))
        (f_fail ())
        (f_urand ())
        (fun e p => f_scrut (e, p))) := by
  intro S hS
  rw [Exp.casesOn_preimage_decomp]
  refine .iUnion fun i => ?_
  fin_cases i
  · exact bvar.measurableEmbedding.measurableSet_image'  (by measurability)
  · exact fvar.measurableEmbedding.measurableSet_image'  (by measurability)
  · exact lit.measurableEmbedding.measurableSet_image'   (h_lit hS)
  · exact lam.measurableEmbedding.measurableSet_image'   (h_lam hS)
  · exact fix.measurableEmbedding.measurableSet_image'   (h_fix hS)
  · exact app.measurableEmbedding.measurableSet_image'   (h_app hS)
  · exact unop.measurableEmbedding.measurableSet_image'  (h_unop hS)
  · exact binop.measurableEmbedding.measurableSet_image' (h_binop hS)
  · exact cond.measurableEmbedding.measurableSet_image'  (h_cond hS)
  · exact pair.measurableEmbedding.measurableSet_image'  (h_pair hS)
  · exact fst.measurableEmbedding.measurableSet_image'   (h_fst hS)
  · exact snd.measurableEmbedding.measurableSet_image'   (h_snd hS)
  · exact inl.measurableEmbedding.measurableSet_image'   (h_inl hS)
  · exact inr.measurableEmbedding.measurableSet_image'   (h_inr hS)
  · exact case.measurableEmbedding.measurableSet_image'  (h_case hS)
  · exact alloc.measurableEmbedding.measurableSet_image' (h_alloc hS)
  · exact load.measurableEmbedding.measurableSet_image'  (h_load hS)
  · exact store.measurableEmbedding.measurableSet_image' (h_store hS)
  · exact tape.measurableEmbedding.measurableSet_image'  (h_tape hS)
  · exact rand.measurableEmbedding.measurableSet_image'  (h_rand hS)
  · exact fail.measurableEmbedding.measurableSet_image'  (by measurability)
  · exact urand.measurableEmbedding.measurableSet_image' (by measurability)
  · exact scrut.measurableEmbedding.measurableSet_image' (h_scrut hS)

/-! ### Param-threaded one-level dispatch (no recursion).

`measurable_rec_param` is the joint analogue of `measurable_rec`: continuations
take both the constructor payload AND an external `β` parameter, and the result
is joint-measurable in `(e, b) : Exp rT × β`. Built directly from
`casesOn_preimage_decomp` via `Prod.map`-style embeddings. -/

/-- Per-constructor cell family for the `β`-parameterised decomposition. -/
def decompCell_param
    {rT : Type _} {α β : Type _} (S : Set α)
    (f_bvar : β × Nat → α) (f_fvar : β × Var → α) (f_lit : β × BaseLit rT → α)
    (f_lam : β × Exp rT → α) (f_fix : β × Exp rT → α)
    (f_app : β × Exp rT × Exp rT → α)
    (f_unop : β × UnOp × Exp rT → α) (f_binop : β × BinOp × Exp rT × Exp rT → α)
    (f_cond : β × Exp rT × Exp rT × Exp rT → α)
    (f_pair : β × Exp rT × Exp rT → α)
    (f_fst : β × Exp rT → α) (f_snd : β × Exp rT → α)
    (f_inl : β × Exp rT → α) (f_inr : β × Exp rT → α)
    (f_case : β × Exp rT × Exp rT × Exp rT → α)
    (f_alloc : β × Exp rT → α) (f_load : β × Exp rT → α)
    (f_store : β × Exp rT × Exp rT → α)
    (f_tape : β × Exp rT → α) (f_rand : β × Exp rT × Exp rT → α)
    (f_fail : β × Unit → α) (f_urand : β × Unit → α)
    (f_scrut : β × Exp rT × Pat rT → α) :
    Fin 23 → Set (Exp rT × β) :=
  ![ (fun q : β × Nat => (Exp.bvar q.2, q.1))   '' (f_bvar  ⁻¹' S)
   , (fun q : β × Var => (Exp.fvar q.2, q.1))   '' (f_fvar  ⁻¹' S)
   , (fun q : β × BaseLit rT => (Exp.lit q.2, q.1))   '' (f_lit ⁻¹' S)
   , (fun q : β × Exp rT => (Exp.lam q.2, q.1))   '' (f_lam   ⁻¹' S)
   , (fun q : β × Exp rT => (Exp.fix q.2, q.1))   '' (f_fix   ⁻¹' S)
   , (fun q : β × Exp rT × Exp rT => (Exp.app q.2.1 q.2.2, q.1)) '' (f_app  ⁻¹' S)
   , (fun q : β × UnOp × Exp rT => (Exp.unop q.2.1 q.2.2, q.1)) '' (f_unop ⁻¹' S)
   , (fun q : β × BinOp × Exp rT × Exp rT =>
        (Exp.binop q.2.1 q.2.2.1 q.2.2.2, q.1)) '' (f_binop ⁻¹' S)
   , (fun q : β × Exp rT × Exp rT × Exp rT =>
        (Exp.cond q.2.1 q.2.2.1 q.2.2.2, q.1)) '' (f_cond ⁻¹' S)
   , (fun q : β × Exp rT × Exp rT => (Exp.pair q.2.1 q.2.2, q.1)) '' (f_pair ⁻¹' S)
   , (fun q : β × Exp rT => (Exp.fst q.2, q.1)) '' (f_fst ⁻¹' S)
   , (fun q : β × Exp rT => (Exp.snd q.2, q.1)) '' (f_snd ⁻¹' S)
   , (fun q : β × Exp rT => (Exp.inl q.2, q.1)) '' (f_inl ⁻¹' S)
   , (fun q : β × Exp rT => (Exp.inr q.2, q.1)) '' (f_inr ⁻¹' S)
   , (fun q : β × Exp rT × Exp rT × Exp rT =>
        (Exp.case q.2.1 q.2.2.1 q.2.2.2, q.1)) '' (f_case ⁻¹' S)
   , (fun q : β × Exp rT => (Exp.alloc q.2, q.1)) '' (f_alloc ⁻¹' S)
   , (fun q : β × Exp rT => (Exp.load q.2, q.1)) '' (f_load ⁻¹' S)
   , (fun q : β × Exp rT × Exp rT => (Exp.store q.2.1 q.2.2, q.1)) '' (f_store ⁻¹' S)
   , (fun q : β × Exp rT => (Exp.tape q.2, q.1)) '' (f_tape ⁻¹' S)
   , (fun q : β × Exp rT × Exp rT => (Exp.rand q.2.1 q.2.2, q.1)) '' (f_rand ⁻¹' S)
   , (fun q : β × Unit => (Exp.fail, q.1)) '' (f_fail ⁻¹' S)
   , (fun q : β × Unit => (Exp.urand, q.1)) '' (f_urand ⁻¹' S)
   , (fun q : β × Exp rT × Pat rT => (Exp.scrut q.2.1 q.2.2, q.1)) '' (f_scrut ⁻¹' S) ]

/-- Joint preimage decomposition for `Exp.casesOn` with a `β` parameter. -/
theorem casesOn_preimage_decomp_param
    {rT : Type _} {α β : Type _} (S : Set α)
    (f_bvar : β × Nat → α) (f_fvar : β × Var → α) (f_lit : β × BaseLit rT → α)
    (f_lam : β × Exp rT → α) (f_fix : β × Exp rT → α)
    (f_app : β × Exp rT × Exp rT → α)
    (f_unop : β × UnOp × Exp rT → α) (f_binop : β × BinOp × Exp rT × Exp rT → α)
    (f_cond : β × Exp rT × Exp rT × Exp rT → α)
    (f_pair : β × Exp rT × Exp rT → α)
    (f_fst : β × Exp rT → α) (f_snd : β × Exp rT → α)
    (f_inl : β × Exp rT → α) (f_inr : β × Exp rT → α)
    (f_case : β × Exp rT × Exp rT × Exp rT → α)
    (f_alloc : β × Exp rT → α) (f_load : β × Exp rT → α)
    (f_store : β × Exp rT × Exp rT → α)
    (f_tape : β × Exp rT → α) (f_rand : β × Exp rT × Exp rT → α)
    (f_fail : β × Unit → α) (f_urand : β × Unit → α)
    (f_scrut : β × Exp rT × Pat rT → α) :
    (fun p : Exp rT × β => Exp.casesOn (motive := fun _ => α) p.1
        (fun n => f_bvar (p.2, n)) (fun x => f_fvar (p.2, x))
        (fun l => f_lit (p.2, l))
        (fun e => f_lam (p.2, e)) (fun e => f_fix (p.2, e))
        (fun e1 e2 => f_app (p.2, e1, e2))
        (fun u e => f_unop (p.2, u, e))
        (fun b e1 e2 => f_binop (p.2, b, e1, e2))
        (fun ec et ef => f_cond (p.2, ec, et, ef))
        (fun e1 e2 => f_pair (p.2, e1, e2))
        (fun e => f_fst (p.2, e)) (fun e => f_snd (p.2, e))
        (fun e => f_inl (p.2, e)) (fun e => f_inr (p.2, e))
        (fun ec el er => f_case (p.2, ec, el, er))
        (fun e => f_alloc (p.2, e)) (fun e => f_load (p.2, e))
        (fun e1 e2 => f_store (p.2, e1, e2))
        (fun e => f_tape (p.2, e))
        (fun e1 e2 => f_rand (p.2, e1, e2))
        (f_fail (p.2, ()))
        (f_urand (p.2, ()))
        (fun e pat => f_scrut (p.2, e, pat))) ⁻¹' S
      = ⋃ i, decompCell_param S f_bvar f_fvar f_lit f_lam f_fix f_app f_unop f_binop
          f_cond f_pair f_fst f_snd f_inl f_inr f_case f_alloc f_load f_store
          f_tape f_rand f_fail f_urand f_scrut i := by
  ext ⟨e, b⟩
  simp only [Set.mem_preimage, Set.mem_iUnion, decompCell_param]
  constructor
  · intro he; cases e
    · exact ⟨0, (b, _), he, rfl⟩
    · exact ⟨1, (b, _), he, rfl⟩
    · exact ⟨2, (b, _), he, rfl⟩
    · exact ⟨3, (b, _), he, rfl⟩
    · exact ⟨4, (b, _), he, rfl⟩
    · exact ⟨5, (b, _, _), he, rfl⟩
    · exact ⟨6, (b, _, _), he, rfl⟩
    · exact ⟨7, (b, _, _, _), he, rfl⟩
    · exact ⟨8, (b, _, _, _), he, rfl⟩
    · exact ⟨9, (b, _, _), he, rfl⟩
    · exact ⟨10, (b, _), he, rfl⟩
    · exact ⟨11, (b, _), he, rfl⟩
    · exact ⟨12, (b, _), he, rfl⟩
    · exact ⟨13, (b, _), he, rfl⟩
    · exact ⟨14, (b, _, _, _), he, rfl⟩
    · exact ⟨15, (b, _), he, rfl⟩
    · exact ⟨16, (b, _), he, rfl⟩
    · exact ⟨17, (b, _, _), he, rfl⟩
    · exact ⟨18, (b, _), he, rfl⟩
    · exact ⟨19, (b, _, _), he, rfl⟩
    · exact ⟨20, (b, ()), he, rfl⟩
    · exact ⟨21, (b, ()), he, rfl⟩
    · exact ⟨22, (b, _, _), he, rfl⟩
  · rintro ⟨i, hi⟩; fin_cases i <;>
      · obtain ⟨q, hq, hp⟩ := hi; cases hp; simpa using hq

/-- One-level `Exp.casesOn` with a `β` parameter threaded.

Joint-measurable analogue of `measurable_rec`: each continuation `c_X` takes
`β × Payload → α`. Each branch of `casesOn` is the image of a measurable
embedding `(b, payload) ↦ (ctor payload, b)`, lifted via `MeasurableEmbedding.prodMap`. -/
theorem measurable_rec_param
    {rT : Type _} [MeasurableSpace rT]
    {α : Type _} [MeasurableSpace α]
    {β : Type _} [MeasurableSpace β]
    (c_bvar : β × Nat → α) (c_fvar : β × Var → α) (c_lit : β × BaseLit rT → α)
    (c_lam : β × Exp rT → α) (c_fix : β × Exp rT → α)
    (c_app : β × Exp rT × Exp rT → α)
    (c_unop : β × UnOp × Exp rT → α) (c_binop : β × BinOp × Exp rT × Exp rT → α)
    (c_cond : β × Exp rT × Exp rT × Exp rT → α)
    (c_pair : β × Exp rT × Exp rT → α)
    (c_fst : β × Exp rT → α) (c_snd : β × Exp rT → α)
    (c_inl : β × Exp rT → α) (c_inr : β × Exp rT → α)
    (c_case : β × Exp rT × Exp rT × Exp rT → α)
    (c_alloc : β × Exp rT → α) (c_load : β × Exp rT → α)
    (c_store : β × Exp rT × Exp rT → α)
    (c_tape : β × Exp rT → α) (c_rand : β × Exp rT × Exp rT → α)
    (c_fail : β × Unit → α) (c_urand : β × Unit → α)
    (c_scrut : β × Exp rT × Pat rT → α)
    (h_bvar : Measurable c_bvar) (h_fvar : Measurable c_fvar)
    (h_lit : Measurable c_lit)
    (h_lam : Measurable c_lam) (h_fix : Measurable c_fix)
    (h_app : Measurable c_app) (h_unop : Measurable c_unop)
    (h_binop : Measurable c_binop) (h_cond : Measurable c_cond)
    (h_pair : Measurable c_pair) (h_fst : Measurable c_fst) (h_snd : Measurable c_snd)
    (h_inl : Measurable c_inl) (h_inr : Measurable c_inr)
    (h_case : Measurable c_case)
    (h_alloc : Measurable c_alloc) (h_load : Measurable c_load)
    (h_store : Measurable c_store)
    (h_tape : Measurable c_tape) (h_rand : Measurable c_rand)
    (h_fail : Measurable c_fail) (h_urand : Measurable c_urand)
    (h_scrut : Measurable c_scrut) :
    Measurable (fun p : Exp rT × β => Exp.casesOn (motive := fun _ => α) p.1
        (fun n => c_bvar (p.2, n)) (fun x => c_fvar (p.2, x))
        (fun l => c_lit (p.2, l))
        (fun e => c_lam (p.2, e)) (fun e => c_fix (p.2, e))
        (fun e1 e2 => c_app (p.2, e1, e2))
        (fun u e => c_unop (p.2, u, e))
        (fun b e1 e2 => c_binop (p.2, b, e1, e2))
        (fun ec et ef => c_cond (p.2, ec, et, ef))
        (fun e1 e2 => c_pair (p.2, e1, e2))
        (fun e => c_fst (p.2, e)) (fun e => c_snd (p.2, e))
        (fun e => c_inl (p.2, e)) (fun e => c_inr (p.2, e))
        (fun ec el er => c_case (p.2, ec, el, er))
        (fun e => c_alloc (p.2, e)) (fun e => c_load (p.2, e))
        (fun e1 e2 => c_store (p.2, e1, e2))
        (fun e => c_tape (p.2, e))
        (fun e1 e2 => c_rand (p.2, e1, e2))
        (c_fail (p.2, ()))
        (c_urand (p.2, ()))
        (fun e pat => c_scrut (p.2, e, pat))) := by
  intro S hS
  rw [casesOn_preimage_decomp_param]
  -- Each piece: `(fun q => (ctor q.2, q.1)) '' (c_X ⁻¹' S)`. The cover map is
  -- `Prod.map ctor.ι id ∘ Prod.swap`, a composition of measurable embeddings.
  refine .iUnion fun i => ?_
  fin_cases i
  · exact ((bvar.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_bvar hS)
  · exact ((fvar.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_fvar hS)
  · exact ((lit.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_lit hS)
  · exact ((lam.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_lam hS)
  · exact ((fix.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_fix hS)
  · exact ((app.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_app hS)
  · exact ((unop.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_unop hS)
  · exact ((binop.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_binop hS)
  · exact ((cond.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_cond hS)
  · exact ((pair.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_pair hS)
  · exact ((fst.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_fst hS)
  · exact ((snd.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_snd hS)
  · exact ((inl.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_inl hS)
  · exact ((inr.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_inr hS)
  · exact ((case.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_case hS)
  · exact ((alloc.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_alloc hS)
  · exact ((load.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_load hS)
  · exact ((store.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_store hS)
  · exact ((tape.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_tape hS)
  · exact ((rand.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_rand hS)
  · exact ((fail.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_fail hS)
  · exact ((urand.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_urand hS)
  · exact ((scrut.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_scrut hS)

/-! ### Recursive measurability principle.

Same shape as `Pat.measurable_struct_rec`: one hypothesis per constructor (combinator
+ equation + measurability), the keystone proof dispatches each shape to the
appropriate generic `StructRec.cell_*` helper. -/

section StructRec

variable {rT α : Type _} [MeasurableSpace rT] [MeasurableSpace α]
variable {f : Exp rT → α}

-- Per-constructor combinators
variable {c_bvar : Nat → α} {c_fvar : Var → α} {c_lit : BaseLit rT → α}
variable {c_lam : α → α} {c_fix : α → α}
variable {c_app : α → α → α}
variable {c_unop : UnOp → α → α}
variable {c_binop : BinOp → α → α → α}
variable {c_cond : α → α → α → α}
variable {c_pair : α → α → α} {c_fst : α → α} {c_snd : α → α}
variable {c_inl : α → α} {c_inr : α → α}
variable {c_case : α → α → α → α}
variable {c_alloc : α → α} {c_load : α → α} {c_store : α → α → α}
variable {c_tape : α → α} {c_rand : α → α → α}
variable {c_fail : α}
variable {c_urand : α}
variable {c_scrut : α → Pat rT → α}

-- Per-constructor equations
variable (eq_bvar  : ∀ n,        f (.bvar n)        = c_bvar n)
variable (eq_fvar  : ∀ x,        f (.fvar x)        = c_fvar x)
variable (eq_lit   : ∀ b,        f (.lit b)         = c_lit b)
variable (eq_lam   : ∀ e,        f (.lam e)         = c_lam (f e))
variable (eq_fix   : ∀ e,        f (.fix e)         = c_fix (f e))
variable (eq_app   : ∀ e1 e2,    f (.app e1 e2)     = c_app (f e1) (f e2))
variable (eq_unop  : ∀ u e,      f (.unop u e)      = c_unop u (f e))
variable (eq_binop : ∀ b e1 e2,  f (.binop b e1 e2) = c_binop b (f e1) (f e2))
variable (eq_cond  : ∀ ec et ef, f (.cond ec et ef) = c_cond (f ec) (f et) (f ef))
variable (eq_pair  : ∀ e1 e2,    f (.pair e1 e2)    = c_pair (f e1) (f e2))
variable (eq_fst   : ∀ e,        f (.fst e)         = c_fst (f e))
variable (eq_snd   : ∀ e,        f (.snd e)         = c_snd (f e))
variable (eq_inl   : ∀ e,        f (.inl e)         = c_inl (f e))
variable (eq_inr   : ∀ e,        f (.inr e)         = c_inr (f e))
variable (eq_case  : ∀ ec el er, f (.case ec el er) = c_case (f ec) (f el) (f er))
variable (eq_alloc : ∀ e,        f (.alloc e)       = c_alloc (f e))
variable (eq_load  : ∀ e,        f (.load e)        = c_load (f e))
variable (eq_store : ∀ e1 e2,    f (.store e1 e2)   = c_store (f e1) (f e2))
variable (eq_tape  : ∀ e,        f (.tape e)        = c_tape (f e))
variable (eq_rand  : ∀ e1 e2,    f (.rand e1 e2)    = c_rand (f e1) (f e2))
variable (eq_fail  :             f .fail            = c_fail)
variable (eq_urand :             f .urand           = c_urand)
variable (eq_scrut : ∀ e p,      f (.scrut e p)     = c_scrut (f e) p)

-- Per-constructor combinator measurability
variable (h_lit   : Measurable c_lit)
variable (h_lam   : Measurable c_lam) (h_fix : Measurable c_fix)
variable (h_app   : Measurable (Function.uncurry c_app))
variable (h_unop  : Measurable (Function.uncurry c_unop))
variable (h_binop : Measurable (fun (p : BinOp × α × α) => c_binop p.1 p.2.1 p.2.2))
variable (h_cond  : Measurable (fun (p : α × α × α) => c_cond p.1 p.2.1 p.2.2))
variable (h_pair  : Measurable (Function.uncurry c_pair))
variable (h_fst   : Measurable c_fst) (h_snd : Measurable c_snd)
variable (h_inl   : Measurable c_inl) (h_inr : Measurable c_inr)
variable (h_case  : Measurable (fun (p : α × α × α) => c_case p.1 p.2.1 p.2.2))
variable (h_alloc : Measurable c_alloc) (h_load : Measurable c_load)
variable (h_store : Measurable (Function.uncurry c_store))
variable (h_tape  : Measurable c_tape)
variable (h_rand  : Measurable (Function.uncurry c_rand))
variable (h_scrut : Measurable (Function.uncurry c_scrut))

include eq_bvar eq_fvar eq_lit eq_lam eq_fix eq_app eq_unop eq_binop eq_cond
        eq_pair eq_fst eq_snd eq_inl eq_inr eq_case eq_alloc eq_load eq_store
        eq_tape eq_rand eq_fail eq_urand eq_scrut
        h_lit h_lam h_fix h_app h_unop h_binop h_cond h_pair h_fst h_snd
        h_inl h_inr h_case h_alloc h_load h_store h_tape h_rand h_scrut in
/-- **The keystone**: structurally-recursive `f : Exp rT → α` is measurable when each
constructor's combinator is measurable. -/
theorem measurable_struct_rec : Measurable f := by
  apply _root_.StructRec.measurable_of_cells Exp.shape; intro s
  induction s with
  | bvar n =>
    intro U hU
    exact _root_.StructRec.cell_nullary Exp.shape (ctor := .bvar n)
      (fun p => by cases p <;> simp) (eq_bvar n) (flatten_measurable (.bvar))
  | fvar x =>
    intro U hU
    exact _root_.StructRec.cell_nullary Exp.shape (ctor := .fvar x)
      (fun p => by cases p <;> simp) (eq_fvar x) (flatten_measurable (.fvar))
  | lit =>
    intro U hU
    exact _root_.StructRec.cell_dataLeaf Exp.shape lit.measurableEmbedding
      (fun p => by cases p <;> simp) eq_lit h_lit hU
  | lam _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary Exp.shape lam.measurableEmbedding
      (fun p => by cases p <;> simp) eq_lam h_lam @ih hU
  | fix _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary Exp.shape fix.measurableEmbedding
      (fun p => by cases p <;> simp) eq_fix h_fix @ih hU
  | app _ _ ih1 ih2 =>
    intro U hU
    exact _root_.StructRec.cell_binary Exp.shape (ctor := Exp.app)
      app.measurableEmbedding (fun p => by cases p <;> simp)
      eq_app h_app @ih1 @ih2 hU
  | unop u _ ih =>
    -- Mixed (syntax-leaf × recursive): at this Shape arm the leaf `u` is fixed, so we
    -- slice the uncurried embedding at `u` via `of_uncurry_fixed_left` and call
    -- plain `cell_unary` with `ctor := Exp.unop u`.
    intro U hU
    have h_emb_u : MeasurableEmbedding (Exp.unop u : Exp rT → Exp rT) :=
      .of_uncurry_fixed_left unop.measurableEmbedding (MeasurableSet.singleton u)
    have h_c_u : Measurable (c_unop u) :=
      h_unop.comp (by fun_prop : Measurable (fun x : α => (u, x)))
    exact _root_.StructRec.cell_unary Exp.shape (ctor := (Exp.unop u : Exp rT → Exp rT))
      h_emb_u (fun p => by cases p <;> simp) (eq_unop u) h_c_u @ih hU
  | binop b _ _ ih1 ih2 =>
    intro U hU
    have h_emb_b : MeasurableEmbedding (Function.uncurry (Exp.binop b : Exp rT → Exp rT → Exp rT)) :=
      .of_uncurry_fixed_left binop.measurableEmbedding (MeasurableSet.singleton b)
    have h_c_b : Measurable (Function.uncurry (c_binop b)) :=
      h_binop.comp (by fun_prop : Measurable (fun p : α × α => (b, p.1, p.2)))
    exact _root_.StructRec.cell_binary Exp.shape (ctor := Exp.binop b)
      h_emb_b (fun p => by cases p <;> simp) (eq_binop b) h_c_b @ih1 @ih2 hU
  | cond _ _ _ ih1 ih2 ih3 =>
    intro U hU
    exact _root_.StructRec.cell_ternary Exp.shape (ctor := Exp.cond)
      cond.measurableEmbedding (fun p => by cases p <;> simp) eq_cond h_cond
      @ih1 @ih2 @ih3 hU
  | pair _ _ ih1 ih2 =>
    intro U hU
    exact _root_.StructRec.cell_binary Exp.shape (ctor := Exp.pair)
      pair.measurableEmbedding (fun p => by cases p <;> simp)
      eq_pair h_pair @ih1 @ih2 hU
  | fst _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary Exp.shape fst.measurableEmbedding
      (fun p => by cases p <;> simp) eq_fst h_fst @ih hU
  | snd _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary Exp.shape snd.measurableEmbedding
      (fun p => by cases p <;> simp) eq_snd h_snd @ih hU
  | inl _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary Exp.shape inl.measurableEmbedding
      (fun p => by cases p <;> simp) eq_inl h_inl @ih hU
  | inr _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary Exp.shape inr.measurableEmbedding
      (fun p => by cases p <;> simp) eq_inr h_inr @ih hU
  | case _ _ _ ih1 ih2 ih3 =>
    intro U hU
    exact _root_.StructRec.cell_ternary Exp.shape (ctor := Exp.case)
      case.measurableEmbedding (fun p => by cases p <;> simp) eq_case h_case
      @ih1 @ih2 @ih3 hU
  | alloc _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary Exp.shape alloc.measurableEmbedding
      (fun p => by cases p <;> simp) eq_alloc h_alloc @ih hU
  | load _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary Exp.shape load.measurableEmbedding
      (fun p => by cases p <;> simp) eq_load h_load @ih hU
  | store _ _ ih1 ih2 =>
    intro U hU
    exact _root_.StructRec.cell_binary Exp.shape (ctor := Exp.store)
      store.measurableEmbedding (fun p => by cases p <;> simp)
      eq_store h_store @ih1 @ih2 hU
  | tape _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary Exp.shape tape.measurableEmbedding
      (fun p => by cases p <;> simp) eq_tape h_tape @ih hU
  | rand _ _ ih1 ih2 =>
    intro U hU
    exact _root_.StructRec.cell_binary Exp.shape (ctor := Exp.rand)
      rand.measurableEmbedding (fun p => by cases p <;> simp)
      eq_rand h_rand @ih1 @ih2 hU
  | fail =>
    intro U hU
    exact _root_.StructRec.cell_nullary Exp.shape (ctor := .fail)
      (fun p => by cases p <;> simp) eq_fail (flatten_measurable .fail)
  | urand =>
    intro U hU
    exact _root_.StructRec.cell_nullary Exp.shape (ctor := .urand)
      (fun p => by cases p <;> simp) eq_urand (flatten_measurable .urand)
  | scrut _ ih =>
    intro U hU
    exact _root_.StructRec.cell_scrutLike Exp.shape (ctor := Exp.scrut)
      scrut.measurableEmbedding (fun p => by cases p <;> simp)
      eq_scrut h_scrut @ih hU

end StructRec

/-! ### Param-threaded keystone.

Parameter-threaded version: function `g : β → Exp rT → α` where `β` is carried
unchanged through every recursive call. Concludes `Measurable (Function.uncurry g)`. -/

section StructRecParam

variable {rT α β : Type _} [MeasurableSpace rT] [MeasurableSpace α] [MeasurableSpace β]
variable [Inhabited β]
variable {g : β → Exp rT → α}

-- Per-constructor combinators (each takes β as extra arg)
variable {c_bvar : β → Nat → α} {c_fvar : β → Var → α} {c_lit : β → BaseLit rT → α}
variable {c_lam : β → α → α} {c_fix : β → α → α}
variable {c_app : β → α → α → α}
variable {c_unop : β → UnOp → α → α}
variable {c_binop : β → BinOp → α → α → α}
variable {c_cond : β → α → α → α → α}
variable {c_pair : β → α → α → α} {c_fst : β → α → α} {c_snd : β → α → α}
variable {c_inl : β → α → α} {c_inr : β → α → α}
variable {c_case : β → α → α → α → α}
variable {c_alloc : β → α → α} {c_load : β → α → α} {c_store : β → α → α → α}
variable {c_tape : β → α → α} {c_rand : β → α → α → α}
variable {c_fail : β → α}
variable {c_urand : β → α}
variable {c_scrut : β → α → Pat rT → α}

-- Equations
variable (eq_bvar  : ∀ b n,        g b (.bvar n)        = c_bvar b n)
variable (eq_fvar  : ∀ b x,        g b (.fvar x)        = c_fvar b x)
variable (eq_lit   : ∀ b l,        g b (.lit l)         = c_lit b l)
variable (eq_lam   : ∀ b e,        g b (.lam e)         = c_lam b (g b e))
variable (eq_fix   : ∀ b e,        g b (.fix e)         = c_fix b (g b e))
variable (eq_app   : ∀ b e1 e2,    g b (.app e1 e2)     = c_app b (g b e1) (g b e2))
variable (eq_unop  : ∀ b u e,      g b (.unop u e)      = c_unop b u (g b e))
variable (eq_binop : ∀ b op e1 e2, g b (.binop op e1 e2) = c_binop b op (g b e1) (g b e2))
variable (eq_cond  : ∀ b ec et ef, g b (.cond ec et ef) = c_cond b (g b ec) (g b et) (g b ef))
variable (eq_pair  : ∀ b e1 e2,    g b (.pair e1 e2)    = c_pair b (g b e1) (g b e2))
variable (eq_fst   : ∀ b e,        g b (.fst e)         = c_fst b (g b e))
variable (eq_snd   : ∀ b e,        g b (.snd e)         = c_snd b (g b e))
variable (eq_inl   : ∀ b e,        g b (.inl e)         = c_inl b (g b e))
variable (eq_inr   : ∀ b e,        g b (.inr e)         = c_inr b (g b e))
variable (eq_case  : ∀ b ec el er, g b (.case ec el er) = c_case b (g b ec) (g b el) (g b er))
variable (eq_alloc : ∀ b e,        g b (.alloc e)       = c_alloc b (g b e))
variable (eq_load  : ∀ b e,        g b (.load e)        = c_load b (g b e))
variable (eq_store : ∀ b e1 e2,    g b (.store e1 e2)   = c_store b (g b e1) (g b e2))
variable (eq_tape  : ∀ b e,        g b (.tape e)        = c_tape b (g b e))
variable (eq_rand  : ∀ b e1 e2,    g b (.rand e1 e2)    = c_rand b (g b e1) (g b e2))
variable (eq_fail  : ∀ b,          g b .fail            = c_fail b)
variable (eq_urand : ∀ b,          g b .urand           = c_urand b)
variable (eq_scrut : ∀ b e p,      g b (.scrut e p)     = c_scrut b (g b e) p)

-- Combinator measurability (each Function.uncurry across β + other args)
variable (h_bvar  : Measurable (Function.uncurry c_bvar))
variable (h_fvar  : Measurable (Function.uncurry c_fvar))
variable (h_lit   : Measurable (Function.uncurry c_lit))
variable (h_lam   : Measurable (Function.uncurry c_lam))
variable (h_fix   : Measurable (Function.uncurry c_fix))
variable (h_app   : Measurable (fun (q : β × α × α) => c_app q.1 q.2.1 q.2.2))
variable (h_unop  : Measurable (fun (q : β × UnOp × α) => c_unop q.1 q.2.1 q.2.2))
variable (h_binop : Measurable (fun (q : β × BinOp × α × α) => c_binop q.1 q.2.1 q.2.2.1 q.2.2.2))
variable (h_cond  : Measurable (fun (q : β × α × α × α) => c_cond q.1 q.2.1 q.2.2.1 q.2.2.2))
variable (h_pair  : Measurable (fun (q : β × α × α) => c_pair q.1 q.2.1 q.2.2))
variable (h_fst   : Measurable (Function.uncurry c_fst))
variable (h_snd   : Measurable (Function.uncurry c_snd))
variable (h_inl   : Measurable (Function.uncurry c_inl))
variable (h_inr   : Measurable (Function.uncurry c_inr))
variable (h_case  : Measurable (fun (q : β × α × α × α) => c_case q.1 q.2.1 q.2.2.1 q.2.2.2))
variable (h_alloc : Measurable (Function.uncurry c_alloc))
variable (h_load  : Measurable (Function.uncurry c_load))
variable (h_store : Measurable (fun (q : β × α × α) => c_store q.1 q.2.1 q.2.2))
variable (h_tape  : Measurable (Function.uncurry c_tape))
variable (h_rand  : Measurable (fun (q : β × α × α) => c_rand q.1 q.2.1 q.2.2))
variable (h_fail  : Measurable c_fail)
variable (h_urand : Measurable c_urand)
variable (h_scrut : Measurable (fun (q : β × α × Pat rT) => c_scrut q.1 q.2.1 q.2.2))

include eq_bvar eq_fvar eq_lit eq_lam eq_fix eq_app eq_unop eq_binop eq_cond
        eq_pair eq_fst eq_snd eq_inl eq_inr eq_case eq_alloc eq_load eq_store
        eq_tape eq_rand eq_fail eq_urand eq_scrut
        h_bvar h_fvar h_lit h_lam h_fix h_app h_unop h_binop h_cond
        h_pair h_fst h_snd h_inl h_inr h_case
        h_alloc h_load h_store h_tape h_rand h_fail h_urand h_scrut in
/-- Param-threaded keystone. -/
theorem measurable_struct_rec_param : Measurable (Function.uncurry g) := by
  apply _root_.StructRec.measurable_of_cells_param Exp.shape; intro s
  induction s with
  | bvar n =>
    intro U hU
    exact _root_.StructRec.cell_nullary_param Exp.shape (ctor := .bvar n)
      (fun p => by cases p <;> simp) (fun b => eq_bvar b n)
      (h_bvar.comp (by fun_prop : Measurable (fun b : β => (b, n))))
      hU (flatten_measurable .bvar)
  | fvar x =>
    intro U hU
    exact _root_.StructRec.cell_nullary_param Exp.shape (ctor := .fvar x)
      (fun p => by cases p <;> simp) (fun b => eq_fvar b x)
      (h_fvar.comp (by fun_prop : Measurable (fun b : β => (b, x))))
      hU (flatten_measurable .fvar)
  | lit =>
    intro U hU
    exact _root_.StructRec.cell_dataLeaf_param Exp.shape lit.measurableEmbedding
      (fun p => by cases p <;> simp) eq_lit h_lit hU
  | lam _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary_param Exp.shape lam.measurableEmbedding
      (fun p => by cases p <;> simp) eq_lam h_lam @ih hU
  | fix _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary_param Exp.shape fix.measurableEmbedding
      (fun p => by cases p <;> simp) eq_fix h_fix @ih hU
  | app _ _ ih1 ih2 =>
    intro U hU
    exact _root_.StructRec.cell_binary_param Exp.shape (ctor := Exp.app)
      app.measurableEmbedding (fun p => by cases p <;> simp)
      eq_app h_app @ih1 @ih2 hU
  | pair _ _ ih1 ih2 =>
    intro U hU
    exact _root_.StructRec.cell_binary_param Exp.shape (ctor := Exp.pair)
      pair.measurableEmbedding (fun p => by cases p <;> simp)
      eq_pair h_pair @ih1 @ih2 hU
  | fst _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary_param Exp.shape fst.measurableEmbedding
      (fun p => by cases p <;> simp) eq_fst h_fst @ih hU
  | snd _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary_param Exp.shape snd.measurableEmbedding
      (fun p => by cases p <;> simp) eq_snd h_snd @ih hU
  | inl _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary_param Exp.shape inl.measurableEmbedding
      (fun p => by cases p <;> simp) eq_inl h_inl @ih hU
  | inr _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary_param Exp.shape inr.measurableEmbedding
      (fun p => by cases p <;> simp) eq_inr h_inr @ih hU
  | alloc _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary_param Exp.shape alloc.measurableEmbedding
      (fun p => by cases p <;> simp) eq_alloc h_alloc @ih hU
  | load _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary_param Exp.shape load.measurableEmbedding
      (fun p => by cases p <;> simp) eq_load h_load @ih hU
  | store _ _ ih1 ih2 =>
    intro U hU
    exact _root_.StructRec.cell_binary_param Exp.shape (ctor := Exp.store)
      store.measurableEmbedding (fun p => by cases p <;> simp)
      eq_store h_store @ih1 @ih2 hU
  | tape _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary_param Exp.shape tape.measurableEmbedding
      (fun p => by cases p <;> simp) eq_tape h_tape @ih hU
  | rand _ _ ih1 ih2 =>
    intro U hU
    exact _root_.StructRec.cell_binary_param Exp.shape (ctor := Exp.rand)
      rand.measurableEmbedding (fun p => by cases p <;> simp)
      eq_rand h_rand @ih1 @ih2 hU
  | fail =>
    intro U hU
    exact _root_.StructRec.cell_nullary_param Exp.shape (ctor := .fail)
      (fun p => by cases p <;> simp) eq_fail h_fail hU (flatten_measurable .fail)
  | urand =>
    intro U hU
    exact _root_.StructRec.cell_nullary_param Exp.shape (ctor := .urand)
      (fun p => by cases p <;> simp) eq_urand h_urand hU (flatten_measurable .urand)
  | unop u _ ih =>
    -- Mixed (syntax-leaf × recursive): at shape (Shape.unop u s'), `u` is fixed, so
    -- slice the uncurried embedding at `u` and call `cell_unary_param`.
    intro U hU
    have h_emb_u : MeasurableEmbedding (Exp.unop u : Exp rT → Exp rT) :=
      .of_uncurry_fixed_left unop.measurableEmbedding (MeasurableSet.singleton u)
    have h_c_u : Measurable (Function.uncurry (fun (b : β) (a : α) => c_unop b u a)) :=
      h_unop.comp (by fun_prop : Measurable (fun q : β × α => (q.1, u, q.2)))
    exact _root_.StructRec.cell_unary_param Exp.shape (ctor := (Exp.unop u : Exp rT → Exp rT))
      h_emb_u (fun p => by cases p <;> simp)
      (fun b p => eq_unop b u p) h_c_u @ih hU
  | binop o _ _ ih1 ih2 =>
    intro U hU
    have h_emb_o : MeasurableEmbedding
        (Function.uncurry (Exp.binop o : Exp rT → Exp rT → Exp rT)) :=
      .of_uncurry_fixed_left binop.measurableEmbedding (MeasurableSet.singleton o)
    have h_c_o : Measurable (fun (q : β × α × α) => c_binop q.1 o q.2.1 q.2.2) :=
      h_binop.comp (by fun_prop : Measurable (fun q : β × α × α => (q.1, o, q.2.1, q.2.2)))
    exact _root_.StructRec.cell_binary_param Exp.shape
      (ctor := (Exp.binop o : Exp rT → Exp rT → Exp rT))
      h_emb_o (fun p => by cases p <;> simp)
      (fun b p1 p2 => eq_binop b o p1 p2) h_c_o @ih1 @ih2 hU
  | cond _ _ _ ih1 ih2 ih3 =>
    intro U hU
    exact _root_.StructRec.cell_ternary_param Exp.shape (ctor := Exp.cond)
      cond.measurableEmbedding (fun p => by cases p <;> simp) eq_cond h_cond
      @ih1 @ih2 @ih3 hU
  | case _ _ _ ih1 ih2 ih3 =>
    intro U hU
    exact _root_.StructRec.cell_ternary_param Exp.shape (ctor := Exp.case)
      case.measurableEmbedding (fun p => by cases p <;> simp) eq_case h_case
      @ih1 @ih2 @ih3 hU
  | scrut _ ih =>
    intro U hU
    exact _root_.StructRec.cell_scrutLike_param Exp.shape (ctor := Exp.scrut)
      scrut.measurableEmbedding (fun p => by cases p <;> simp) eq_scrut h_scrut
      @ih hU

end StructRecParam

/-! ### Binder-shifting recursive measurability principle.

Same shape as `measurable_struct_rec_param`, but the `lam` and `fix` constructor
recurrences thread the parameter through transformers `t_lam, t_fix : β → β`
(typically `(i, sub) ↦ (i+1, sub)` for de-Bruijn-style recursion). All other
ctors use the unchanged `b`.

This is needed for `openRec`, `closeRec` (binder-shifting depth thread), and
similar functions where the parameter changes at binder boundaries. -/

section StructRecParamShift

variable {rT α β : Type _} [MeasurableSpace rT] [MeasurableSpace α] [MeasurableSpace β]
variable [Inhabited β]
variable {g : β → Exp rT → α}

-- Per-constructor combinators (each takes β as extra arg)
variable {c_bvar : β → Nat → α} {c_fvar : β → Var → α} {c_lit : β → BaseLit rT → α}
variable {c_lam : β → α → α} {c_fix : β → α → α}
variable {c_app : β → α → α → α}
variable {c_unop : β → UnOp → α → α}
variable {c_binop : β → BinOp → α → α → α}
variable {c_cond : β → α → α → α → α}
variable {c_pair : β → α → α → α} {c_fst : β → α → α} {c_snd : β → α → α}
variable {c_inl : β → α → α} {c_inr : β → α → α}
variable {c_case : β → α → α → α → α}
variable {c_alloc : β → α → α} {c_load : β → α → α} {c_store : β → α → α → α}
variable {c_tape : β → α → α} {c_rand : β → α → α → α}
variable {c_fail : β → α}
variable {c_urand : β → α}
variable {c_scrut : β → α → Pat rT → α}

-- Binder param transformers (only for lam and fix; identity for all other ctors).
variable {t_lam : β → β} {t_fix : β → β}

-- Equations (binder ones use shifted param).
variable (eq_bvar  : ∀ b n,        g b (.bvar n)        = c_bvar b n)
variable (eq_fvar  : ∀ b x,        g b (.fvar x)        = c_fvar b x)
variable (eq_lit   : ∀ b l,        g b (.lit l)         = c_lit b l)
variable (eq_lam   : ∀ b e,        g b (.lam e)         = c_lam b (g (t_lam b) e))
variable (eq_fix   : ∀ b e,        g b (.fix e)         = c_fix b (g (t_fix b) e))
variable (eq_app   : ∀ b e1 e2,    g b (.app e1 e2)     = c_app b (g b e1) (g b e2))
variable (eq_unop  : ∀ b u e,      g b (.unop u e)      = c_unop b u (g b e))
variable (eq_binop : ∀ b op e1 e2, g b (.binop op e1 e2) = c_binop b op (g b e1) (g b e2))
variable (eq_cond  : ∀ b ec et ef, g b (.cond ec et ef) = c_cond b (g b ec) (g b et) (g b ef))
variable (eq_pair  : ∀ b e1 e2,    g b (.pair e1 e2)    = c_pair b (g b e1) (g b e2))
variable (eq_fst   : ∀ b e,        g b (.fst e)         = c_fst b (g b e))
variable (eq_snd   : ∀ b e,        g b (.snd e)         = c_snd b (g b e))
variable (eq_inl   : ∀ b e,        g b (.inl e)         = c_inl b (g b e))
variable (eq_inr   : ∀ b e,        g b (.inr e)         = c_inr b (g b e))
variable (eq_case  : ∀ b ec el er, g b (.case ec el er) = c_case b (g b ec) (g b el) (g b er))
variable (eq_alloc : ∀ b e,        g b (.alloc e)       = c_alloc b (g b e))
variable (eq_load  : ∀ b e,        g b (.load e)        = c_load b (g b e))
variable (eq_store : ∀ b e1 e2,    g b (.store e1 e2)   = c_store b (g b e1) (g b e2))
variable (eq_tape  : ∀ b e,        g b (.tape e)        = c_tape b (g b e))
variable (eq_rand  : ∀ b e1 e2,    g b (.rand e1 e2)    = c_rand b (g b e1) (g b e2))
variable (eq_fail  : ∀ b,          g b .fail            = c_fail b)
variable (eq_urand : ∀ b,          g b .urand           = c_urand b)
variable (eq_scrut : ∀ b e p,      g b (.scrut e p)     = c_scrut b (g b e) p)

-- Combinator measurability (same as non-shift version).
variable (h_bvar  : Measurable (Function.uncurry c_bvar))
variable (h_fvar  : Measurable (Function.uncurry c_fvar))
variable (h_lit   : Measurable (Function.uncurry c_lit))
variable (h_lam   : Measurable (Function.uncurry c_lam))
variable (h_fix   : Measurable (Function.uncurry c_fix))
variable (h_app   : Measurable (fun (q : β × α × α) => c_app q.1 q.2.1 q.2.2))
variable (h_unop  : Measurable (fun (q : β × UnOp × α) => c_unop q.1 q.2.1 q.2.2))
variable (h_binop : Measurable (fun (q : β × BinOp × α × α) => c_binop q.1 q.2.1 q.2.2.1 q.2.2.2))
variable (h_cond  : Measurable (fun (q : β × α × α × α) => c_cond q.1 q.2.1 q.2.2.1 q.2.2.2))
variable (h_pair  : Measurable (fun (q : β × α × α) => c_pair q.1 q.2.1 q.2.2))
variable (h_fst   : Measurable (Function.uncurry c_fst))
variable (h_snd   : Measurable (Function.uncurry c_snd))
variable (h_inl   : Measurable (Function.uncurry c_inl))
variable (h_inr   : Measurable (Function.uncurry c_inr))
variable (h_case  : Measurable (fun (q : β × α × α × α) => c_case q.1 q.2.1 q.2.2.1 q.2.2.2))
variable (h_alloc : Measurable (Function.uncurry c_alloc))
variable (h_load  : Measurable (Function.uncurry c_load))
variable (h_store : Measurable (fun (q : β × α × α) => c_store q.1 q.2.1 q.2.2))
variable (h_tape  : Measurable (Function.uncurry c_tape))
variable (h_rand  : Measurable (fun (q : β × α × α) => c_rand q.1 q.2.1 q.2.2))
variable (h_fail  : Measurable c_fail)
variable (h_urand : Measurable c_urand)
variable (h_scrut : Measurable (fun (q : β × α × Pat rT) => c_scrut q.1 q.2.1 q.2.2))

-- Transformer measurability.
variable (h_t_lam : Measurable t_lam)
variable (h_t_fix : Measurable t_fix)

include eq_bvar eq_fvar eq_lit eq_lam eq_fix eq_app eq_unop eq_binop eq_cond
        eq_pair eq_fst eq_snd eq_inl eq_inr eq_case eq_alloc eq_load eq_store
        eq_tape eq_rand eq_fail eq_urand eq_scrut
        h_bvar h_fvar h_lit h_lam h_fix h_app h_unop h_binop h_cond
        h_pair h_fst h_snd h_inl h_inr h_case
        h_alloc h_load h_store h_tape h_rand h_fail h_urand h_scrut
        h_t_lam h_t_fix in
/-- **Param-threaded keystone with binder-shifting for `lam` and `fix`.** -/
theorem measurable_struct_rec_param_shift : Measurable (Function.uncurry g) := by
  apply _root_.StructRec.measurable_of_cells_param Exp.shape; intro s
  induction s with
  | bvar n =>
    intro U hU
    exact _root_.StructRec.cell_nullary_param Exp.shape (ctor := .bvar n)
      (fun p => by cases p <;> simp) (fun b => eq_bvar b n)
      (h_bvar.comp (by fun_prop : Measurable (fun b : β => (b, n))))
      hU (flatten_measurable .bvar)
  | fvar x =>
    intro U hU
    exact _root_.StructRec.cell_nullary_param Exp.shape (ctor := .fvar x)
      (fun p => by cases p <;> simp) (fun b => eq_fvar b x)
      (h_fvar.comp (by fun_prop : Measurable (fun b : β => (b, x))))
      hU (flatten_measurable .fvar)
  | lit =>
    intro U hU
    exact _root_.StructRec.cell_dataLeaf_param Exp.shape lit.measurableEmbedding
      (fun p => by cases p <;> simp) eq_lit h_lit hU
  | lam _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary_param_shift Exp.shape lam.measurableEmbedding
      (fun p => by cases p <;> simp) eq_lam h_lam h_t_lam @ih hU
  | fix _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary_param_shift Exp.shape fix.measurableEmbedding
      (fun p => by cases p <;> simp) eq_fix h_fix h_t_fix @ih hU
  | app _ _ ih1 ih2 =>
    intro U hU
    exact _root_.StructRec.cell_binary_param Exp.shape (ctor := Exp.app)
      app.measurableEmbedding (fun p => by cases p <;> simp)
      eq_app h_app @ih1 @ih2 hU
  | pair _ _ ih1 ih2 =>
    intro U hU
    exact _root_.StructRec.cell_binary_param Exp.shape (ctor := Exp.pair)
      pair.measurableEmbedding (fun p => by cases p <;> simp)
      eq_pair h_pair @ih1 @ih2 hU
  | fst _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary_param Exp.shape fst.measurableEmbedding
      (fun p => by cases p <;> simp) eq_fst h_fst @ih hU
  | snd _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary_param Exp.shape snd.measurableEmbedding
      (fun p => by cases p <;> simp) eq_snd h_snd @ih hU
  | inl _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary_param Exp.shape inl.measurableEmbedding
      (fun p => by cases p <;> simp) eq_inl h_inl @ih hU
  | inr _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary_param Exp.shape inr.measurableEmbedding
      (fun p => by cases p <;> simp) eq_inr h_inr @ih hU
  | alloc _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary_param Exp.shape alloc.measurableEmbedding
      (fun p => by cases p <;> simp) eq_alloc h_alloc @ih hU
  | load _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary_param Exp.shape load.measurableEmbedding
      (fun p => by cases p <;> simp) eq_load h_load @ih hU
  | store _ _ ih1 ih2 =>
    intro U hU
    exact _root_.StructRec.cell_binary_param Exp.shape (ctor := Exp.store)
      store.measurableEmbedding (fun p => by cases p <;> simp)
      eq_store h_store @ih1 @ih2 hU
  | tape _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary_param Exp.shape tape.measurableEmbedding
      (fun p => by cases p <;> simp) eq_tape h_tape @ih hU
  | rand _ _ ih1 ih2 =>
    intro U hU
    exact _root_.StructRec.cell_binary_param Exp.shape (ctor := Exp.rand)
      rand.measurableEmbedding (fun p => by cases p <;> simp)
      eq_rand h_rand @ih1 @ih2 hU
  | fail =>
    intro U hU
    exact _root_.StructRec.cell_nullary_param Exp.shape (ctor := .fail)
      (fun p => by cases p <;> simp) eq_fail h_fail hU (flatten_measurable .fail)
  | urand =>
    intro U hU
    exact _root_.StructRec.cell_nullary_param Exp.shape (ctor := .urand)
      (fun p => by cases p <;> simp) eq_urand h_urand hU (flatten_measurable .urand)
  | unop u _ ih =>
    -- Mixed (syntax-leaf × recursive): `unop` does not cross a binder, so the shift
    -- keystone uses the same `cell_unary_param` as the param keystone. Leaf `u` fixed.
    intro U hU
    have h_emb_u : MeasurableEmbedding (Exp.unop u : Exp rT → Exp rT) :=
      .of_uncurry_fixed_left unop.measurableEmbedding (MeasurableSet.singleton u)
    have h_c_u : Measurable (Function.uncurry (fun (b : β) (a : α) => c_unop b u a)) :=
      h_unop.comp (by fun_prop : Measurable (fun q : β × α => (q.1, u, q.2)))
    exact _root_.StructRec.cell_unary_param Exp.shape (ctor := (Exp.unop u : Exp rT → Exp rT))
      h_emb_u (fun p => by cases p <;> simp)
      (fun b p => eq_unop b u p) h_c_u @ih hU
  | binop o _ _ ih1 ih2 =>
    intro U hU
    have h_emb_o : MeasurableEmbedding
        (Function.uncurry (Exp.binop o : Exp rT → Exp rT → Exp rT)) :=
      .of_uncurry_fixed_left binop.measurableEmbedding (MeasurableSet.singleton o)
    have h_c_o : Measurable (fun (q : β × α × α) => c_binop q.1 o q.2.1 q.2.2) :=
      h_binop.comp (by fun_prop : Measurable (fun q : β × α × α => (q.1, o, q.2.1, q.2.2)))
    exact _root_.StructRec.cell_binary_param Exp.shape
      (ctor := (Exp.binop o : Exp rT → Exp rT → Exp rT))
      h_emb_o (fun p => by cases p <;> simp)
      (fun b p1 p2 => eq_binop b o p1 p2) h_c_o @ih1 @ih2 hU
  | cond _ _ _ ih1 ih2 ih3 =>
    intro U hU
    exact _root_.StructRec.cell_ternary_param Exp.shape (ctor := Exp.cond)
      cond.measurableEmbedding (fun p => by cases p <;> simp)
      eq_cond h_cond @ih1 @ih2 @ih3 hU
  | case _ _ _ ih1 ih2 ih3 =>
    intro U hU
    exact _root_.StructRec.cell_ternary_param Exp.shape (ctor := Exp.case)
      case.measurableEmbedding (fun p => by cases p <;> simp)
      eq_case h_case @ih1 @ih2 @ih3 hU
  | scrut _ ih =>
    intro U hU
    exact _root_.StructRec.cell_scrutLike_param Exp.shape (ctor := Exp.scrut)
      scrut.measurableEmbedding (fun p => by cases p <;> simp) eq_scrut h_scrut
      @ih hU

end StructRecParamShift

/-! ### Synthetic smoke-test battery -/

/-- Test 1: discrete codomain (`tagDepth : Exp rT → Nat`). -/
@[simp] def tagDepth : Exp rT → Nat
  | .bvar _        => 0
  | .fvar _        => 0
  | .lit _         => 0
  | .lam e         => tagDepth e + 1
  | .fix e         => tagDepth e + 1
  | .app e1 e2     => max (tagDepth e1) (tagDepth e2) + 1
  | .unop _ e      => tagDepth e + 1
  | .binop _ e1 e2 => max (tagDepth e1) (tagDepth e2) + 1
  | .cond ec et ef => max (max (tagDepth ec) (tagDepth et)) (tagDepth ef) + 1
  | .pair e1 e2    => max (tagDepth e1) (tagDepth e2) + 1
  | .fst e         => tagDepth e + 1
  | .snd e         => tagDepth e + 1
  | .inl e         => tagDepth e + 1
  | .inr e         => tagDepth e + 1
  | .case ec el er => max (max (tagDepth ec) (tagDepth el)) (tagDepth er) + 1
  | .alloc e       => tagDepth e + 1
  | .load e        => tagDepth e + 1
  | .store e1 e2   => max (tagDepth e1) (tagDepth e2) + 1
  | .tape e        => tagDepth e + 1
  | .rand e1 e2    => max (tagDepth e1) (tagDepth e2) + 1
  | .fail          => 0
  | .urand         => 0
  | .scrut e _     => tagDepth e + 1

theorem tagDepth.measurable [MeasurableSpace rT] :
    Measurable (tagDepth : Exp rT → Nat) := by
  apply measurable_struct_rec (f := tagDepth)
    (c_bvar := fun _ => 0) (c_fvar := fun _ => 0) (c_lit := fun _ => 0)
    (c_lam := (· + 1)) (c_fix := (· + 1))
    (c_app := fun n1 n2 => max n1 n2 + 1)
    (c_unop := fun _ n => n + 1)
    (c_binop := fun _ n1 n2 => max n1 n2 + 1)
    (c_cond := fun n1 n2 n3 => max (max n1 n2) n3 + 1)
    (c_pair := fun n1 n2 => max n1 n2 + 1) (c_fst := (· + 1)) (c_snd := (· + 1))
    (c_inl := (· + 1)) (c_inr := (· + 1))
    (c_case := fun n1 n2 n3 => max (max n1 n2) n3 + 1)
    (c_alloc := (· + 1)) (c_load := (· + 1)) (c_store := fun n1 n2 => max n1 n2 + 1)
    (c_tape := (· + 1)) (c_rand := fun n1 n2 => max n1 n2 + 1)
    (c_fail := 0)
    (c_urand := 0)
    (c_scrut := fun n _ => n + 1)
  all_goals first | (intros; rfl) | fun_prop

/-- Test 2: data-leaf dependent (`countLeaves : Exp rT → Nat`, counts `lit` and `scrut`
data leaves). -/
@[simp] def countLeaves : Exp rT → Nat
  | .bvar _        => 0
  | .fvar _        => 0
  | .lit _         => 1
  | .lam e         => countLeaves e
  | .fix e         => countLeaves e
  | .app e1 e2     => countLeaves e1 + countLeaves e2
  | .unop _ e      => countLeaves e
  | .binop _ e1 e2 => countLeaves e1 + countLeaves e2
  | .cond ec et ef => countLeaves ec + countLeaves et + countLeaves ef
  | .pair e1 e2    => countLeaves e1 + countLeaves e2
  | .fst e         => countLeaves e
  | .snd e         => countLeaves e
  | .inl e         => countLeaves e
  | .inr e         => countLeaves e
  | .case ec el er => countLeaves ec + countLeaves el + countLeaves er
  | .alloc e       => countLeaves e
  | .load e        => countLeaves e
  | .store e1 e2   => countLeaves e1 + countLeaves e2
  | .tape e        => countLeaves e
  | .rand e1 e2    => countLeaves e1 + countLeaves e2
  | .fail          => 0
  | .urand         => 0
  | .scrut e _     => countLeaves e + 1

theorem countLeaves.measurable [MeasurableSpace rT] :
    Measurable (countLeaves : Exp rT → Nat) := by
  apply measurable_struct_rec (f := countLeaves)
    (c_bvar := fun _ => 0) (c_fvar := fun _ => 0) (c_lit := fun _ => 1)
    (c_lam := id) (c_fix := id)
    (c_app := (· + ·))
    (c_unop := fun _ n => n)
    (c_binop := fun _ n1 n2 => n1 + n2)
    (c_cond := fun n1 n2 n3 => n1 + n2 + n3)
    (c_pair := (· + ·)) (c_fst := id) (c_snd := id)
    (c_inl := id) (c_inr := id)
    (c_case := fun n1 n2 n3 => n1 + n2 + n3)
    (c_alloc := id) (c_load := id) (c_store := (· + ·))
    (c_tape := id) (c_rand := (· + ·))
    (c_fail := 0)
    (c_urand := 0)
    (c_scrut := fun n _ => n + 1)
  all_goals first | (intros; rfl) | fun_prop

/-- Test 3: endo-map (`Exp rT → Exp rT`, non-discrete codomain). -/
@[simp] def endoMap : Exp rT → Exp rT
  | .bvar n        => .bvar n
  | .fvar x        => .fvar x
  | .lit b         => .lit b
  | .lam e         => .lam (.lam (endoMap e))
  | .fix e         => .fix (endoMap e)
  | .app e1 e2     => .app (endoMap e1) (endoMap e2)
  | .unop u e      => .unop u (endoMap e)
  | .binop b e1 e2 => .binop b (endoMap e1) (endoMap e2)
  | .cond ec et ef => .cond (endoMap ec) (endoMap et) (endoMap ef)
  | .pair e1 e2    => .pair (endoMap e1) (endoMap e2)
  | .fst e         => .fst (endoMap e)
  | .snd e         => .snd (endoMap e)
  | .inl e         => .inl (endoMap e)
  | .inr e         => .inr (endoMap e)
  | .case ec el er => .case (endoMap ec) (endoMap el) (endoMap er)
  | .alloc e       => .alloc (endoMap e)
  | .load e        => .load (endoMap e)
  | .store e1 e2   => .store (endoMap e1) (endoMap e2)
  | .tape e        => .tape (endoMap e)
  | .rand e1 e2    => .rand (endoMap e1) (endoMap e2)
  | .fail          => .fail
  | .urand         => .urand
  | .scrut e p     => .scrut (endoMap e) p

theorem endoMap.measurable [MeasurableSpace rT] :
    Measurable (endoMap : Exp rT → Exp rT) := by
  apply measurable_struct_rec (f := endoMap)
    (c_bvar := Exp.bvar) (c_fvar := Exp.fvar) (c_lit := Exp.lit)
    (c_lam := fun e => .lam (.lam e)) (c_fix := Exp.fix)
    (c_app := fun e1 e2 => .app e1 e2)
    (c_unop := fun u e => .unop u e)
    (c_binop := fun b e1 e2 => .binop b e1 e2)
    (c_cond := fun ec et ef => .cond ec et ef)
    (c_pair := fun e1 e2 => .pair e1 e2) (c_fst := Exp.fst) (c_snd := Exp.snd)
    (c_inl := Exp.inl) (c_inr := Exp.inr)
    (c_case := fun ec el er => .case ec el er)
    (c_alloc := Exp.alloc) (c_load := Exp.load) (c_store := fun e1 e2 => .store e1 e2)
    (c_tape := Exp.tape) (c_rand := fun e1 e2 => .rand e1 e2)
    (c_fail := .fail)
    (c_urand := .urand)
    (c_scrut := fun e p => .scrut e p)
  all_goals first | (intros; rfl) | fun_prop

/-- Test 4: param-threaded (`addAcc : Nat → Exp rT → Nat`, the `β` is the running
accumulator threaded unchanged into every recursive call; the `bvar` leaf actually
uses the accumulator). -/
@[simp] def addAcc : Nat → Exp rT → Nat
  | acc, .bvar n        => acc + n
  | acc, .fvar _        => acc
  | acc, .lit _         => acc
  | acc, .lam e         => addAcc acc e
  | acc, .fix e         => addAcc acc e
  | acc, .app e1 e2     => addAcc acc e1 + addAcc acc e2
  | acc, .unop _ e      => addAcc acc e
  | acc, .binop _ e1 e2 => addAcc acc e1 + addAcc acc e2
  | acc, .cond ec et ef => addAcc acc ec + addAcc acc et + addAcc acc ef
  | acc, .pair e1 e2    => addAcc acc e1 + addAcc acc e2
  | acc, .fst e         => addAcc acc e
  | acc, .snd e         => addAcc acc e
  | acc, .inl e         => addAcc acc e
  | acc, .inr e         => addAcc acc e
  | acc, .case ec el er => addAcc acc ec + addAcc acc el + addAcc acc er
  | acc, .alloc e       => addAcc acc e
  | acc, .load e        => addAcc acc e
  | acc, .store e1 e2   => addAcc acc e1 + addAcc acc e2
  | acc, .tape e        => addAcc acc e
  | acc, .rand e1 e2    => addAcc acc e1 + addAcc acc e2
  | acc, .fail          => acc
  | acc, .urand         => acc
  | acc, .scrut e _     => addAcc acc e

theorem addAcc.measurable [MeasurableSpace rT] :
    Measurable (Function.uncurry (addAcc : Nat → Exp rT → Nat)) := by
  apply measurable_struct_rec_param (g := addAcc)
    (c_bvar := fun acc n => acc + n) (c_fvar := fun acc _ => acc)
    (c_lit := fun acc _ => acc)
    (c_lam := fun _ n => n) (c_fix := fun _ n => n)
    (c_app := fun _ n1 n2 => n1 + n2)
    (c_unop := fun _ _ n => n)
    (c_binop := fun _ _ n1 n2 => n1 + n2)
    (c_cond := fun _ n1 n2 n3 => n1 + n2 + n3)
    (c_pair := fun _ n1 n2 => n1 + n2) (c_fst := fun _ n => n) (c_snd := fun _ n => n)
    (c_inl := fun _ n => n) (c_inr := fun _ n => n)
    (c_case := fun _ n1 n2 n3 => n1 + n2 + n3)
    (c_alloc := fun _ n => n) (c_load := fun _ n => n) (c_store := fun _ n1 n2 => n1 + n2)
    (c_tape := fun _ n => n) (c_rand := fun _ n1 n2 => n1 + n2)
    (c_fail := fun acc => acc)
    (c_urand := fun acc => acc)
    (c_scrut := fun _ n _ => n)
  all_goals first | (intros; rfl) | fun_prop

/-! ### Singleton-class for `Exp rT` (lifted from `MeasurableSingletonClass rT`).

Was previously in `Discrete.lean`; moved here so every stamped file carries its own
singleton section (matching `BaseLit.lean`/`Pat.lean`). -/

@[simp] def singletonCyl {rT : Type _} : Exp rT → Cylinder rT
  | .bvar n        => .bvar n
  | .fvar x        => .fvar x
  | .lit b         => .lit {b}
  | .lam e         => .lam (singletonCyl e)
  | .fix e         => .fix (singletonCyl e)
  | .app e1 e2     => .app (singletonCyl e1) (singletonCyl e2)
  | .unop u e      => .unop u (singletonCyl e)
  | .binop b e1 e2 => .binop b (singletonCyl e1) (singletonCyl e2)
  | .cond ec et ef => .cond (singletonCyl ec) (singletonCyl et) (singletonCyl ef)
  | .pair e1 e2    => .pair (singletonCyl e1) (singletonCyl e2)
  | .fst e         => .fst (singletonCyl e)
  | .snd e         => .snd (singletonCyl e)
  | .inl e         => .inl (singletonCyl e)
  | .inr e         => .inr (singletonCyl e)
  | .case ec el er => .case (singletonCyl ec) (singletonCyl el) (singletonCyl er)
  | .alloc e       => .alloc (singletonCyl e)
  | .load e        => .load (singletonCyl e)
  | .store e1 e2   => .store (singletonCyl e1) (singletonCyl e2)
  | .tape e        => .tape (singletonCyl e)
  | .rand e1 e2    => .rand (singletonCyl e1) (singletonCyl e2)
  | .fail          => .fail
  | .urand         => .urand
  | .scrut e p     => .scrut (singletonCyl e) {p}

theorem singletonCyl_flatten {rT : Type _} (e : Exp rT) :
    (singletonCyl e).flatten = {e} := by
  induction e with
  | bvar n => simp
  | fvar x => simp
  | lit b => simp
  | lam e ih => simp [ih]
  | fix e ih => simp [ih]
  | app e1 e2 ih1 ih2 => simp [ih1, ih2]
  | unop u e ih => simp [ih]
  | binop b e1 e2 ih1 ih2 => simp [ih1, ih2]
  | cond ec et ef ihc iht ihf => simp [ihc, iht, ihf]
  | pair e1 e2 ih1 ih2 => simp [ih1, ih2]
  | fst e ih => simp [ih]
  | snd e ih => simp [ih]
  | inl e ih => simp [ih]
  | inr e ih => simp [ih]
  | case ec el er ihc ihl ihr => simp [ihc, ihl, ihr]
  | alloc e ih => simp [ih]
  | load e ih => simp [ih]
  | store e1 e2 ih1 ih2 => simp [ih1, ih2]
  | tape e ih => simp [ih]
  | rand e1 e2 ih1 ih2 => simp [ih1, ih2]
  | fail => simp
  | urand => simp
  | scrut e p ih => simp [ih]

theorem singletonCyl_hasMeasurableLeaves
    {rT : Type _} [MeasurableSpace rT] [MeasurableSingletonClass rT] (e : Exp rT) :
    (singletonCyl e).HasMeasurableLeaves := by
  induction e with
  | bvar n => exact .bvar
  | fvar x => exact .fvar
  | lit b => exact .lit _ (MeasurableSet.singleton b)
  | lam e ih => exact .lam ih
  | fix e ih => exact .fix ih
  | app e1 e2 ih1 ih2 => exact .app ih1 ih2
  | unop u e ih => exact .unop ih
  | binop b e1 e2 ih1 ih2 => exact .binop ih1 ih2
  | cond ec et ef ihc iht ihf => exact .cond ihc iht ihf
  | pair e1 e2 ih1 ih2 => exact .pair ih1 ih2
  | fst e ih => exact .fst ih
  | snd e ih => exact .snd ih
  | inl e ih => exact .inl ih
  | inr e ih => exact .inr ih
  | case ec el er ihc ihl ihr => exact .case ihc ihl ihr
  | alloc e ih => exact .alloc ih
  | load e ih => exact .load ih
  | store e1 e2 ih1 ih2 => exact .store ih1 ih2
  | tape e ih => exact .tape ih
  | rand e1 e2 ih1 ih2 => exact .rand ih1 ih2
  | fail => exact .fail
  | urand => exact .urand
  | scrut e p ih => exact .scrut _ ih (MeasurableSet.singleton p)

instance instMeasurableSingletonClass
    {rT : Type _} [MeasurableSpace rT] [MeasurableSingletonClass rT] :
    MeasurableSingletonClass (Exp rT) where
  measurableSet_singleton e := by
    rw [← singletonCyl_flatten e]
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨singletonCyl e, singletonCyl_hasMeasurableLeaves e, rfl⟩

end Exp
end ProbLang
end ProbLangMeasures
