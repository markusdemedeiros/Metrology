module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.Pat

meta import Metrology.Meta

@[expose] public section


noncomputable section ProbLangMeasures

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

/-# Measure space on expressions.

Follows the same `BaseLit`/`Pat` template. `Exp` has:
- two syntax-leaf constructors (`bvar : Nat`, `fvar : Var`)
- one data-leaf constructor (`lit : BaseLit rT`)
- one nullary constructor (`fail`)
- many recursive constructors of arities 1–3 (`lam`, `fix`, `fst`, `snd`, `inl`, `inr`,
  `alloc`, `load`, `tape`; `app`, `pair`, `store`, `rand`; `cond`, `case`)
- mixed constructors:
  - `unop : UnOp + 1 rec` (UnOp is a syntax-leaf-style discrete tag retained in the shape)
  - `binop : BinOp + 2 rec`
  - `scrut : 1 rec + Pat rT` (Pat is a data leaf)
-/

namespace ProbLang.Exp

macro "solve_ι_inj" : tactic => `(tactic|
  (intro a b h;
   first
   | (cases h; rfl)
   | (obtain ⟨_, _⟩ := a; obtain ⟨_, _⟩ := b; cases h; rfl)
   | (obtain ⟨_, _, _⟩ := a; obtain ⟨_, _, _⟩ := b; cases h; rfl)))

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
  | scrut (s : Shape)
  deriving Countable

/-- Interpret a cylinder as the set of `Exp rT` it describes. -/
@[simp] def Cylinder.flatten {rT : Type _} : Cylinder rT → Set (Exp rT)
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
  | scrut S : HasMeasurableLeaves c → MeasurableSet S → HasMeasurableLeaves (.scrut c S)

instance instMeasurableSpaceExp [MeasurableSpace rT] : MeasurableSpace (Exp rT) :=
  .generateFrom <| Cylinder.flatten '' { c : Cylinder rT | c.HasMeasurableLeaves }

@[simp] def shape : Exp rT → Shape
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
  | .scrut e _     => .scrut (shape e)

/-- Shape of a cylinder (forgets data leaves). -/
@[simp] def Cylinder.shape {rT : Type _} : Cylinder rT → Shape
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
  | .scrut c _     => .scrut (shape c)

/-- The "universe cylinder" for a given shape: `univ` at every data leaf, same skeleton. -/
@[simp] def Shape.cylinder {rT : Type _} : Shape → Cylinder rT
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
  | .scrut c S, .scrut c' S' =>
      match Cylinder.inter? c c' with
      | some r => some (.scrut r (S ∩ S'))
      | none => none
  | _, _ => none

/-- Every element of a cylinder's flatten has that cylinder's shape. -/
theorem Cylinder.shape_of_mem_flatten {rT : Type _} {c : Cylinder rT} {e : Exp rT}
    (h : e ∈ Cylinder.flatten c) : Exp.shape e = Cylinder.shape c := by
  induction c generalizing e with
  | bvar _ | fvar _ | fail => simp_all
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
    (h : Cylinder.shape c₁ ≠ Cylinder.shape c₂) : Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ = ∅ := by
  ext e
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro he₁ he₂
  exact h ((Cylinder.shape_of_mem_flatten he₁).symm.trans (Cylinder.shape_of_mem_flatten he₂))

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
    case lit S₂ => simp [Cylinder.inter?]; ext e; cases e <;> simp
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | lam c ih =>
    cases c₂
    case lam c' =>
      show (Exp.lam.ι '' Cylinder.flatten c) ∩ (Exp.lam.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Exp.lam.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | fix c ih =>
    cases c₂
    case fix c' =>
      show (Exp.fix.ι '' Cylinder.flatten c) ∩ (Exp.fix.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Exp.fix.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | app a b ih₁ ih₂ =>
    cases c₂
    case app a' b' =>
      show (Exp.app.ι '' (Cylinder.flatten a ×ˢ Cylinder.flatten b)) ∩
           (Exp.app.ι '' (Cylinder.flatten a' ×ˢ Cylinder.flatten b')) = _
      rw [← Set.image_inter Exp.app.ι.inj, Set.prod_inter_prod, ih₁, ih₂]
      cases hr₁ : Cylinder.inter? a a' <;> cases hr₂ : Cylinder.inter? b b' <;>
        simp [Cylinder.inter?, hr₁, hr₂]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | unop u c ih =>
    cases c₂
    case unop u' c' =>
      show (Exp.unop u '' Cylinder.flatten c) ∩ (Exp.unop u' '' Cylinder.flatten c') = _
      by_cases hu : u = u'
      · subst hu
        rw [← Set.image_inter (fun _ _ h => by injection h), ih]
        cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
      · have hinter : Cylinder.inter? (Cylinder.unop u c) (Cylinder.unop u' c') = none := by
          simp [Cylinder.inter?, hu]
        rw [hinter]
        ext e
        simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_empty_iff_false, iff_false,
          Option.elim_none, not_and]
        rintro ⟨a, _, rfl⟩ ⟨a', _, hh⟩
        injection hh with hu_eq _
        exact hu hu_eq.symm
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | binop b a₁ a₂ ih₁ ih₂ =>
    cases c₂
    case binop b' a₁' a₂' =>
      show ((fun p => Exp.binop b p.1 p.2) '' (Cylinder.flatten a₁ ×ˢ Cylinder.flatten a₂)) ∩
           ((fun p => Exp.binop b' p.1 p.2) '' (Cylinder.flatten a₁' ×ˢ Cylinder.flatten a₂')) = _
      by_cases hb : b = b'
      · subst hb
        rw [← Set.image_inter (fun _ _ h => by injection h with _ h1 h2; exact Prod.ext h1 h2),
            Set.prod_inter_prod, ih₁, ih₂]
        cases hr₁ : Cylinder.inter? a₁ a₁' <;> cases hr₂ : Cylinder.inter? a₂ a₂' <;>
          simp [Cylinder.inter?, hr₁, hr₂]
      · have hinter : Cylinder.inter? (Cylinder.binop b a₁ a₂) (Cylinder.binop b' a₁' a₂') = none := by
          simp [Cylinder.inter?, hb]
        rw [hinter]
        ext e
        simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_empty_iff_false, iff_false,
          Option.elim_none, not_and]
        rintro ⟨a, _, rfl⟩ ⟨a', _, hh⟩
        injection hh with hb_eq _ _
        exact hb hb_eq.symm
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | cond cc ct cf ihc iht ihf =>
    cases c₂
    case cond cc' ct' cf' =>
      show (Exp.cond.ι '' (Cylinder.flatten cc ×ˢ Cylinder.flatten ct ×ˢ Cylinder.flatten cf)) ∩
           (Exp.cond.ι '' (Cylinder.flatten cc' ×ˢ Cylinder.flatten ct' ×ˢ Cylinder.flatten cf')) = _
      rw [← Set.image_inter Exp.cond.ι.inj, Set.prod_inter_prod, Set.prod_inter_prod,
          ihc, iht, ihf]
      cases hrc : Cylinder.inter? cc cc' <;> cases hrt : Cylinder.inter? ct ct' <;>
        cases hrf : Cylinder.inter? cf cf' <;>
        simp [Cylinder.inter?, hrc, hrt, hrf]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | pair a b ih₁ ih₂ =>
    cases c₂
    case pair a' b' =>
      show (Exp.pair.ι '' (Cylinder.flatten a ×ˢ Cylinder.flatten b)) ∩
           (Exp.pair.ι '' (Cylinder.flatten a' ×ˢ Cylinder.flatten b')) = _
      rw [← Set.image_inter Exp.pair.ι.inj, Set.prod_inter_prod, ih₁, ih₂]
      cases hr₁ : Cylinder.inter? a a' <;> cases hr₂ : Cylinder.inter? b b' <;>
        simp [Cylinder.inter?, hr₁, hr₂]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | fst c ih =>
    cases c₂
    case fst c' =>
      show (Exp.fst.ι '' Cylinder.flatten c) ∩ (Exp.fst.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Exp.fst.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | snd c ih =>
    cases c₂
    case snd c' =>
      show (Exp.snd.ι '' Cylinder.flatten c) ∩ (Exp.snd.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Exp.snd.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | inl c ih =>
    cases c₂
    case inl c' =>
      show (Exp.inl.ι '' Cylinder.flatten c) ∩ (Exp.inl.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Exp.inl.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | inr c ih =>
    cases c₂
    case inr c' =>
      show (Exp.inr.ι '' Cylinder.flatten c) ∩ (Exp.inr.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Exp.inr.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | case cc cl cr ihc ihl ihr =>
    cases c₂
    case case cc' cl' cr' =>
      show (Exp.case.ι '' (Cylinder.flatten cc ×ˢ Cylinder.flatten cl ×ˢ Cylinder.flatten cr)) ∩
           (Exp.case.ι '' (Cylinder.flatten cc' ×ˢ Cylinder.flatten cl' ×ˢ Cylinder.flatten cr')) = _
      rw [← Set.image_inter Exp.case.ι.inj, Set.prod_inter_prod, Set.prod_inter_prod,
          ihc, ihl, ihr]
      cases hrc : Cylinder.inter? cc cc' <;> cases hrl : Cylinder.inter? cl cl' <;>
        cases hrr : Cylinder.inter? cr cr' <;>
        simp [Cylinder.inter?, hrc, hrl, hrr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | alloc c ih =>
    cases c₂
    case alloc c' =>
      show (Exp.alloc.ι '' Cylinder.flatten c) ∩ (Exp.alloc.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Exp.alloc.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | load c ih =>
    cases c₂
    case load c' =>
      show (Exp.load.ι '' Cylinder.flatten c) ∩ (Exp.load.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Exp.load.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | store a b ih₁ ih₂ =>
    cases c₂
    case store a' b' =>
      show (Exp.store.ι '' (Cylinder.flatten a ×ˢ Cylinder.flatten b)) ∩
           (Exp.store.ι '' (Cylinder.flatten a' ×ˢ Cylinder.flatten b')) = _
      rw [← Set.image_inter Exp.store.ι.inj, Set.prod_inter_prod, ih₁, ih₂]
      cases hr₁ : Cylinder.inter? a a' <;> cases hr₂ : Cylinder.inter? b b' <;>
        simp [Cylinder.inter?, hr₁, hr₂]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | tape c ih =>
    cases c₂
    case tape c' =>
      show (Exp.tape.ι '' Cylinder.flatten c) ∩ (Exp.tape.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Exp.tape.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | rand a b ih₁ ih₂ =>
    cases c₂
    case rand a' b' =>
      show (Exp.rand.ι '' (Cylinder.flatten a ×ˢ Cylinder.flatten b)) ∩
           (Exp.rand.ι '' (Cylinder.flatten a' ×ˢ Cylinder.flatten b')) = _
      rw [← Set.image_inter Exp.rand.ι.inj, Set.prod_inter_prod, ih₁, ih₂]
      cases hr₁ : Cylinder.inter? a a' <;> cases hr₂ : Cylinder.inter? b b' <;>
        simp [Cylinder.inter?, hr₁, hr₂]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | fail =>
    cases c₂
    case fail => simp [Cylinder.inter?]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | scrut c S ih =>
    cases c₂
    case scrut c' S' =>
      show (Exp.scrut.ι '' (Cylinder.flatten c ×ˢ S)) ∩ (Exp.scrut.ι '' (Cylinder.flatten c' ×ˢ S')) = _
      rw [← Set.image_inter Exp.scrut.ι.inj, Set.prod_inter_prod, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)

theorem Cylinder.flatten_inter_some {rT : Type _} {c₁ c₂ c : Cylinder rT}
    (h : Cylinder.inter? c₁ c₂ = some c) :
    Cylinder.flatten c = Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ := by
  rw [Cylinder.flatten_inter, h]; rfl

set_option maxHeartbeats 1000000 in
/-- Inheritance of `HasMeasurableLeaves` under `Cylinder.inter?`.

Same one-liner as for `BaseLit`/`Pat` (compare `BaseLit.lean:171`,
`Pat.lean:194`); the heartbeat bump is purely to absorb the 22×22 case-split
blow-up of `induction h₁ <;> cases h₂` over `Exp`'s constructor count.
The proof itself is structurally identical to the smaller-arity versions. -/
theorem Cylinder.hasMeasurableLeaves_inter [MeasurableSpace rT]
    {c₁ c₂ c : Cylinder rT}
    (h₁ : c₁.HasMeasurableLeaves) (h₂ : c₂.HasMeasurableLeaves)
    (h : Cylinder.inter? c₁ c₂ = some c) : c.HasMeasurableLeaves := by
  induction h₁ generalizing c₂ c <;> cases h₂ <;>
    simp_all [Cylinder.inter?] <;> grind [HasMeasurableLeaves, MeasurableSet.inter]

/-! ### Per-constructor covers. -/

def cover.bvar (S : Set Nat) : Set (Exp rT) :=
  ⋃ n ∈ S, Cylinder.flatten (.bvar n)

def cover.fvar (S : Set Var) : Set (Exp rT) :=
  ⋃ x ∈ S, Cylinder.flatten (.fvar x)

def cover.lit (S : Set (BaseLit rT)) : Set (Exp rT) :=
  Cylinder.flatten (.lit S)

def cover.lam (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.lam s.cylinder)

def cover.fix (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.fix s.cylinder)

def cover.app (S : Set (Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.app p.1.cylinder p.2.cylinder)

def cover.unop (S : Set (UnOp × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.unop p.1 p.2.cylinder)

def cover.binop (S : Set (BinOp × Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.binop p.1 p.2.1.cylinder p.2.2.cylinder)

def cover.cond (S : Set (Shape × Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.cond p.1.cylinder p.2.1.cylinder p.2.2.cylinder)

def cover.pair (S : Set (Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.pair p.1.cylinder p.2.cylinder)

def cover.fst (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.fst s.cylinder)

def cover.snd (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.snd s.cylinder)

def cover.inl (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.inl s.cylinder)

def cover.inr (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.inr s.cylinder)

def cover.case (S : Set (Shape × Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.case p.1.cylinder p.2.1.cylinder p.2.2.cylinder)

def cover.alloc (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.alloc s.cylinder)

def cover.load (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.load s.cylinder)

def cover.store (S : Set (Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.store p.1.cylinder p.2.cylinder)

def cover.tape (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.tape s.cylinder)

def cover.rand (S : Set (Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.rand p.1.cylinder p.2.cylinder)

def cover.fail (S : Set Unit) : Set (Exp rT) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.fail : Cylinder rT)

def cover.scrut (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.scrut s.cylinder Set.univ)

/-- Cylinder of a given shape has measurable leaves. -/
theorem Shape.cylinder_hasMeasurableLeaves [MeasurableSpace rT] (s : Shape) :
    (s.cylinder (rT := rT)).HasMeasurableLeaves := by
  induction s <;> constructor <;> measurability

set_option maxHeartbeats 1000000 in
/-- Flattening a cylinder of a shape equals set of terms with a given shape. -/
@[simp] theorem Shape.cylinder_preimage_shape (s : Shape) :
    (s.cylinder (rT := rT)).flatten = Exp.shape ⁻¹' {s} := by
  ext p; induction p generalizing s <;> cases s <;> simp_all <;> tauto

/-- Flattening a cylinder gives a measurable set. -/
@[measurability]
theorem flatten_measurable [MeasurableSpace rT] {c : Cylinder rT}
    (hc : c.HasMeasurableLeaves) : MeasurableSet c.flatten :=
  MeasurableSpace.measurableSet_generateFrom ⟨c, hc, rfl⟩

attribute [aesop safe constructors (rule_sets := [Measurable])]
  ProbLang.Exp.Cylinder.HasMeasurableLeaves

attribute [aesop safe apply (rule_sets := [Measurable])]
  Shape.cylinder_hasMeasurableLeaves

/-! ### The cylinder flatten family is a π-system that spans `Exp rT`. -/

theorem Cylinder.flatten_isPiSystem [MeasurableSpace rT] :
    IsPiSystem
      ({S : Set (Exp rT) | ∃ c : Cylinder rT, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S}) := by
  rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩ hne
  have hi : Cylinder.inter? c₁ c₂ ≠ none := by
    intro h
    have : c₁.flatten ∩ c₂.flatten = ∅ := by rw [Cylinder.flatten_inter, h]; rfl
    exact hne.ne_empty this
  obtain ⟨c, hc⟩ : ∃ c, Cylinder.inter? c₁ c₂ = some c := Option.ne_none_iff_exists'.mp hi
  exact ⟨c, Cylinder.hasMeasurableLeaves_inter hc₁ hc₂ hc, Cylinder.flatten_inter_some hc⟩

theorem Cylinder.flatten_isCountablySpanning [MeasurableSpace rT] :
    IsCountablySpanning
      ({S : Set (Exp rT) | ∃ c : Cylinder rT, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S}) := by
  obtain ⟨enc⟩ := nonempty_encodable Shape
  refine ⟨fun n =>
    match enc.decode n with
    | some s => Cylinder.flatten (Shape.cylinder s : Cylinder rT)
    | none => Cylinder.flatten (.fail : Cylinder rT), ?_, ?_⟩
  · intro n
    cases h : enc.decode n with
    | none => exact ⟨.fail, .fail, by simp [h]⟩
    | some s => exact ⟨Shape.cylinder s, Shape.cylinder_hasMeasurableLeaves s, by simp [h]⟩
  · ext e
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨enc.encode (Exp.shape e), ?_⟩
    have hd : enc.decode (enc.encode (Exp.shape e)) = some (Exp.shape e) := enc.encodek _
    rw [hd]
    simp [Shape.cylinder_preimage_shape]

/-! ### Measurability of the per-constructor covers. -/

macro "solve_cover_measurable" : tactic => `(tactic|
  first
  | exact .biUnion (Set.to_countable _) fun _ _ => flatten_measurable (by measurability)
  | exact flatten_measurable (by measurability))

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
theorem cover.scrut.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (scrut (rT := rT) S) := by solve_cover_measurable

macro "solve_cover_eq_image" ctor:ident : tactic => `(tactic|
  (ext e; cases e <;> simp [$ctor:ident]))

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

theorem cover.scrut_univ_eq_range :
    cover.scrut (rT := rT) Set.univ = .range (Function.uncurry Exp.scrut) := by
  solve_cover_eq_image cover.scrut

/-! ### Measurable constructors. -/

@[fun_prop]
theorem bvar.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (Exp.bvar.ι (rT := rT)) := Measurable.of_discrete

@[fun_prop]
theorem fvar.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (Exp.fvar.ι (rT := rT)) := Measurable.of_discrete

@[fun_prop]
theorem fail.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (Exp.fail.ι (rT := rT)) := Measurable.of_discrete

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

macro "solve_discrete_ME" eq_image:term ", " meas:term : tactic => `(tactic|
  (refine ⟨fun _ _ h => by injection h, Measurable.of_discrete, fun S _ => ?_⟩
   rw [← $eq_image S]
   exact $meas S))

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
    (f_fail : Unit → α) (f_scrut : Exp rT × Pat rT → α) :
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
        (fun e p => f_scrut (e, p))) ⁻¹' S
      = (Exp.bvar.ι  '' (f_bvar  ⁻¹' S))
      ∪ (Exp.fvar.ι  '' (f_fvar  ⁻¹' S))
      ∪ (Exp.lit.ι   '' (f_lit   ⁻¹' S))
      ∪ (Exp.lam.ι   '' (f_lam   ⁻¹' S))
      ∪ (Exp.fix.ι   '' (f_fix   ⁻¹' S))
      ∪ (Exp.app.ι   '' (f_app   ⁻¹' S))
      ∪ (Exp.unop.ι  '' (f_unop  ⁻¹' S))
      ∪ (Exp.binop.ι '' (f_binop ⁻¹' S))
      ∪ (Exp.cond.ι  '' (f_cond  ⁻¹' S))
      ∪ (Exp.pair.ι  '' (f_pair  ⁻¹' S))
      ∪ (Exp.fst.ι   '' (f_fst   ⁻¹' S))
      ∪ (Exp.snd.ι   '' (f_snd   ⁻¹' S))
      ∪ (Exp.inl.ι   '' (f_inl   ⁻¹' S))
      ∪ (Exp.inr.ι   '' (f_inr   ⁻¹' S))
      ∪ (Exp.case.ι  '' (f_case  ⁻¹' S))
      ∪ (Exp.alloc.ι '' (f_alloc ⁻¹' S))
      ∪ (Exp.load.ι  '' (f_load  ⁻¹' S))
      ∪ (Exp.store.ι '' (f_store ⁻¹' S))
      ∪ (Exp.tape.ι  '' (f_tape  ⁻¹' S))
      ∪ (Exp.rand.ι  '' (f_rand  ⁻¹' S))
      ∪ (Exp.fail.ι  '' (f_fail  ⁻¹' S))
      ∪ (Exp.scrut.ι '' (f_scrut ⁻¹' S)) := by
  ext e; cases e <;> aesop

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
    (f_fail : Unit → α) (f_scrut : Exp rT × Pat rT → α)
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
        (fun e p => f_scrut (e, p))) := by
  intro S hS
  rw [Exp.casesOn_preimage_decomp]
  iterate 21 refine .union ?_ ?_
  · exact bvar.measurableEmbedding.measurableSet_image'  .of_discrete
  · exact fvar.measurableEmbedding.measurableSet_image'  .of_discrete
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
  · exact fail.measurableEmbedding.measurableSet_image'  .of_discrete
  · exact scrut.measurableEmbedding.measurableSet_image' (h_scrut hS)

/-! ### Param-threaded one-level dispatch (no recursion).

`measurable_rec_param` is the joint analogue of `measurable_rec`: continuations
take both the constructor payload AND an external `β` parameter, and the result
is joint-measurable in `(e, b) : Exp rT × β`. Built directly from
`casesOn_preimage_decomp` via `Prod.map`-style embeddings. -/

set_option maxHeartbeats 2000000 in
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
    (f_fail : β × Unit → α) (f_scrut : β × Exp rT × Pat rT → α) :
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
        (fun e pat => f_scrut (p.2, e, pat))) ⁻¹' S
      = ((fun q : β × Nat => (Exp.bvar q.2, q.1))   '' (f_bvar  ⁻¹' S))
      ∪ ((fun q : β × Var => (Exp.fvar q.2, q.1))   '' (f_fvar  ⁻¹' S))
      ∪ ((fun q : β × BaseLit rT => (Exp.lit q.2, q.1))   '' (f_lit ⁻¹' S))
      ∪ ((fun q : β × Exp rT => (Exp.lam q.2, q.1))   '' (f_lam   ⁻¹' S))
      ∪ ((fun q : β × Exp rT => (Exp.fix q.2, q.1))   '' (f_fix   ⁻¹' S))
      ∪ ((fun q : β × Exp rT × Exp rT => (Exp.app q.2.1 q.2.2, q.1))
            '' (f_app  ⁻¹' S))
      ∪ ((fun q : β × UnOp × Exp rT => (Exp.unop q.2.1 q.2.2, q.1))
            '' (f_unop ⁻¹' S))
      ∪ ((fun q : β × BinOp × Exp rT × Exp rT =>
            (Exp.binop q.2.1 q.2.2.1 q.2.2.2, q.1)) '' (f_binop ⁻¹' S))
      ∪ ((fun q : β × Exp rT × Exp rT × Exp rT =>
            (Exp.cond q.2.1 q.2.2.1 q.2.2.2, q.1)) '' (f_cond ⁻¹' S))
      ∪ ((fun q : β × Exp rT × Exp rT => (Exp.pair q.2.1 q.2.2, q.1))
            '' (f_pair ⁻¹' S))
      ∪ ((fun q : β × Exp rT => (Exp.fst q.2, q.1)) '' (f_fst ⁻¹' S))
      ∪ ((fun q : β × Exp rT => (Exp.snd q.2, q.1)) '' (f_snd ⁻¹' S))
      ∪ ((fun q : β × Exp rT => (Exp.inl q.2, q.1)) '' (f_inl ⁻¹' S))
      ∪ ((fun q : β × Exp rT => (Exp.inr q.2, q.1)) '' (f_inr ⁻¹' S))
      ∪ ((fun q : β × Exp rT × Exp rT × Exp rT =>
            (Exp.case q.2.1 q.2.2.1 q.2.2.2, q.1)) '' (f_case ⁻¹' S))
      ∪ ((fun q : β × Exp rT => (Exp.alloc q.2, q.1)) '' (f_alloc ⁻¹' S))
      ∪ ((fun q : β × Exp rT => (Exp.load q.2, q.1)) '' (f_load ⁻¹' S))
      ∪ ((fun q : β × Exp rT × Exp rT => (Exp.store q.2.1 q.2.2, q.1))
            '' (f_store ⁻¹' S))
      ∪ ((fun q : β × Exp rT => (Exp.tape q.2, q.1)) '' (f_tape ⁻¹' S))
      ∪ ((fun q : β × Exp rT × Exp rT => (Exp.rand q.2.1 q.2.2, q.1))
            '' (f_rand ⁻¹' S))
      ∪ ((fun q : β × Unit => (Exp.fail, q.1)) '' (f_fail ⁻¹' S))
      ∪ ((fun q : β × Exp rT × Pat rT => (Exp.scrut q.2.1 q.2.2, q.1))
            '' (f_scrut ⁻¹' S)) := by
  ext ⟨e, b⟩; cases e <;> aesop

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
    (c_fail : β × Unit → α) (c_scrut : β × Exp rT × Pat rT → α)
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
    (h_fail : Measurable c_fail) (h_scrut : Measurable c_scrut) :
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
        (fun e pat => c_scrut (p.2, e, pat))) := by
  intro S hS
  rw [casesOn_preimage_decomp_param]
  -- Each piece: `(fun q => (ctor q.2, q.1)) '' (c_X ⁻¹' S)`. The cover map is
  -- `Prod.map ctor.ι id ∘ Prod.swap`, a composition of measurable embeddings.
  iterate 21 refine .union ?_ ?_
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
        eq_tape eq_rand eq_fail eq_scrut
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
    intro U hU
    have h_emb_u : MeasurableEmbedding (Exp.unop u : Exp rT → Exp rT) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x y hxy
        have hxy' : Function.uncurry (Exp.unop : UnOp → Exp rT → Exp rT) (u, x)
                  = Function.uncurry (Exp.unop : UnOp → Exp rT → Exp rT) (u, y) := by
          simpa [Function.uncurry] using hxy
        have := unop.measurableEmbedding.injective hxy'
        exact (Prod.mk.injEq .. |>.mp this).2
      · exact unop.ι.measurable.comp (by fun_prop : Measurable (fun x : Exp rT => (u, x)))
      · intro V hV
        have heq2 : (Exp.unop u : Exp rT → Exp rT) '' V
            = (Function.uncurry (Exp.unop : UnOp → Exp rT → Exp rT)) '' (({u} : Set UnOp) ×ˢ V) := by
          ext y; simp [Function.uncurry]
        rw [heq2]
        exact unop.measurableEmbedding.measurableSet_image'
          ((MeasurableSet.singleton u).prod hV)
    have h_c_u : Measurable (c_unop u) :=
      h_unop.comp (by fun_prop : Measurable (fun x : α => (u, x)))
    exact _root_.StructRec.cell_unary Exp.shape (ctor := (Exp.unop u : Exp rT → Exp rT))
      h_emb_u (fun p => by cases p <;> simp) (eq_unop u) h_c_u @ih hU
  | binop b _ _ ih1 ih2 =>
    intro U hU
    have h_emb_b : MeasurableEmbedding (Function.uncurry (Exp.binop b : Exp rT → Exp rT → Exp rT)) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x y hxy
        simp [Function.uncurry] at hxy
        ext
        · exact hxy.1
        · exact hxy.2
      · exact (binop.measurableEmbedding.measurable).comp
          (by fun_prop : Measurable (fun p : Exp rT × Exp rT => (b, p.1, p.2)))
      · intro V hV
        have heq2 : Function.uncurry (Exp.binop b : Exp rT → Exp rT → Exp rT) '' V
            = (fun (p : BinOp × Exp rT × Exp rT) => Exp.binop p.1 p.2.1 p.2.2)
                '' ({b} ×ˢ V) := by
          ext y; simp [Function.uncurry]
        rw [heq2]
        refine binop.measurableEmbedding.measurableSet_image' ?_
        exact (MeasurableSet.singleton b).prod hV
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
variable (h_scrut : Measurable (fun (q : β × α × Pat rT) => c_scrut q.1 q.2.1 q.2.2))

include eq_bvar eq_fvar eq_lit eq_lam eq_fix eq_app eq_unop eq_binop eq_cond
        eq_pair eq_fst eq_snd eq_inl eq_inr eq_case eq_alloc eq_load eq_store
        eq_tape eq_rand eq_fail eq_scrut
        h_bvar h_fvar h_lit h_lam h_fix h_app h_unop h_binop h_cond
        h_pair h_fst h_snd h_inl h_inr h_case
        h_alloc h_load h_store h_tape h_rand h_fail h_scrut in
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
  | unop u _ ih =>
    -- Partial-application approach: at shape (Shape.unop u s'), u is fixed.
    -- Use cell_unary_param with ctor := Exp.unop u and combinator c_unop b u.
    intro U hU
    have h_emb_u : MeasurableEmbedding (Exp.unop u : Exp rT → Exp rT) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x y hxy
        have hxy' : Function.uncurry (Exp.unop : UnOp → Exp rT → Exp rT) (u, x)
                  = Function.uncurry (Exp.unop : UnOp → Exp rT → Exp rT) (u, y) := by
          simpa [Function.uncurry] using hxy
        have := unop.measurableEmbedding.injective hxy'
        exact (Prod.mk.injEq .. |>.mp this).2
      · exact unop.ι.measurable.comp (by fun_prop : Measurable (fun x : Exp rT => (u, x)))
      · intro V hV
        have heq2 : (Exp.unop u : Exp rT → Exp rT) '' V
            = (Function.uncurry (Exp.unop : UnOp → Exp rT → Exp rT)) '' (({u} : Set UnOp) ×ˢ V) := by
          ext y; simp [Function.uncurry]
        rw [heq2]
        exact unop.measurableEmbedding.measurableSet_image'
          ((MeasurableSet.singleton u).prod hV)
    have h_c_u : Measurable (Function.uncurry (fun (b : β) (a : α) => c_unop b u a)) :=
      h_unop.comp (by fun_prop : Measurable (fun q : β × α => (q.1, u, q.2)))
    exact _root_.StructRec.cell_unary_param Exp.shape (ctor := (Exp.unop u : Exp rT → Exp rT))
      h_emb_u (fun p => by cases p <;> simp)
      (fun b p => eq_unop b u p) h_c_u @ih hU
  | binop o _ _ ih1 ih2 =>
    intro U hU
    have h_emb_o : MeasurableEmbedding
        (Function.uncurry (Exp.binop o : Exp rT → Exp rT → Exp rT)) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x y hxy
        simp [Function.uncurry] at hxy
        ext
        · exact hxy.1
        · exact hxy.2
      · exact (binop.measurableEmbedding.measurable).comp
          (by fun_prop : Measurable (fun p : Exp rT × Exp rT => (o, p.1, p.2)))
      · intro V hV
        have heq2 : Function.uncurry (Exp.binop o : Exp rT → Exp rT → Exp rT) '' V
            = (fun (p : BinOp × Exp rT × Exp rT) => Exp.binop p.1 p.2.1 p.2.2)
                '' (({o} : Set BinOp) ×ˢ V) := by
          ext y; simp [Function.uncurry]
        rw [heq2]
        exact binop.measurableEmbedding.measurableSet_image'
          ((MeasurableSet.singleton o).prod hV)
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
variable (h_scrut : Measurable (fun (q : β × α × Pat rT) => c_scrut q.1 q.2.1 q.2.2))

-- Transformer measurability.
variable (h_t_lam : Measurable t_lam)
variable (h_t_fix : Measurable t_fix)

include eq_bvar eq_fvar eq_lit eq_lam eq_fix eq_app eq_unop eq_binop eq_cond
        eq_pair eq_fst eq_snd eq_inl eq_inr eq_case eq_alloc eq_load eq_store
        eq_tape eq_rand eq_fail eq_scrut
        h_bvar h_fvar h_lit h_lam h_fix h_app h_unop h_binop h_cond
        h_pair h_fst h_snd h_inl h_inr h_case
        h_alloc h_load h_store h_tape h_rand h_fail h_scrut
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
  | unop u _ ih =>
    intro U hU
    have h_emb_u : MeasurableEmbedding (Exp.unop u : Exp rT → Exp rT) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x y hxy
        have hxy' : Function.uncurry (Exp.unop : UnOp → Exp rT → Exp rT) (u, x)
                  = Function.uncurry (Exp.unop : UnOp → Exp rT → Exp rT) (u, y) := by
          simpa [Function.uncurry] using hxy
        have := unop.measurableEmbedding.injective hxy'
        exact (Prod.mk.injEq .. |>.mp this).2
      · exact unop.ι.measurable.comp (by fun_prop : Measurable (fun x : Exp rT => (u, x)))
      · intro V hV
        have heq2 : (Exp.unop u : Exp rT → Exp rT) '' V
            = (Function.uncurry (Exp.unop : UnOp → Exp rT → Exp rT)) '' (({u} : Set UnOp) ×ˢ V) := by
          ext y; simp [Function.uncurry]
        rw [heq2]
        exact unop.measurableEmbedding.measurableSet_image'
          ((MeasurableSet.singleton u).prod hV)
    have h_c_u : Measurable (Function.uncurry (fun (b : β) (a : α) => c_unop b u a)) :=
      h_unop.comp (by fun_prop : Measurable (fun q : β × α => (q.1, u, q.2)))
    exact _root_.StructRec.cell_unary_param Exp.shape (ctor := (Exp.unop u : Exp rT → Exp rT))
      h_emb_u (fun p => by cases p <;> simp)
      (fun b p => eq_unop b u p) h_c_u @ih hU
  | binop o _ _ ih1 ih2 =>
    intro U hU
    have h_emb_o : MeasurableEmbedding
        (Function.uncurry (Exp.binop o : Exp rT → Exp rT → Exp rT)) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x y hxy
        simp [Function.uncurry] at hxy
        ext
        · exact hxy.1
        · exact hxy.2
      · exact (binop.measurableEmbedding.measurable).comp
          (by fun_prop : Measurable (fun p : Exp rT × Exp rT => (o, p.1, p.2)))
      · intro V hV
        have heq2 : Function.uncurry (Exp.binop o : Exp rT → Exp rT → Exp rT) '' V
            = (fun (p : BinOp × Exp rT × Exp rT) => Exp.binop p.1 p.2.1 p.2.2)
                '' (({o} : Set BinOp) ×ˢ V) := by
          ext y; simp [Function.uncurry]
        rw [heq2]
        exact binop.measurableEmbedding.measurableSet_image'
          ((MeasurableSet.singleton o).prod hV)
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

end Exp
end ProbLang
end ProbLangMeasures
