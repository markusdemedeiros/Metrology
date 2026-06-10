module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.Val
public import Metrology.ProbLang.CoreMeasures.Stamp

meta import Metrology.Meta

@[expose] public section

/-## ProbLang Measure theory -/

-- TODO move this to the semantics file once we have that (leave here until then though,
-- during drop-in step, so we can prove discreteness assuming discrete R type)

-- NOTE Tecnically speaking this is a strict extension: we can instanstiate the reals type
-- with Unit and then I guess also make the ops trivial? Perhaps I need a class with
-- all of this stuff. I do NOT want to have to do the whole thing at once, so I need
-- the option to take the discrete measure over whatever the reals type is

-- NOTE This actually could be a good thing to be honest, since I can also instanstiate
-- reals with floats? Pog?

noncomputable section ProbLangMeasures

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

/-# Measure space on evaluation-context items. -/

namespace ProbLang.EctxItem

theorem appL.ι.inj   {α : Type _} : Function.Injective (@EctxItem.appL.ι   α) := by solve_ι_inj
theorem appR.ι.inj   {α : Type _} : Function.Injective (@EctxItem.appR.ι   α) := by solve_ι_inj
theorem unop.ι.inj   {α : Type _} : Function.Injective (@EctxItem.unop.ι   α) := by solve_ι_inj
theorem binopL.ι.inj {α : Type _} : Function.Injective (@EctxItem.binopL.ι α) := by solve_ι_inj
theorem binopR.ι.inj {α : Type _} : Function.Injective (@EctxItem.binopR.ι α) := by solve_ι_inj
theorem condC.ι.inj  {α : Type _} : Function.Injective (@EctxItem.condC.ι  α) := by solve_ι_inj
theorem pairL.ι.inj  {α : Type _} : Function.Injective (@EctxItem.pairL.ι  α) := by solve_ι_inj
theorem pairR.ι.inj  {α : Type _} : Function.Injective (@EctxItem.pairR.ι  α) := by solve_ι_inj
theorem fst.ι.inj    {α : Type _} : Function.Injective (@EctxItem.fst.ι    α) := by solve_ι_inj
theorem snd.ι.inj    {α : Type _} : Function.Injective (@EctxItem.snd.ι    α) := by solve_ι_inj
theorem inl.ι.inj    {α : Type _} : Function.Injective (@EctxItem.inl.ι    α) := by solve_ι_inj
theorem inr.ι.inj    {α : Type _} : Function.Injective (@EctxItem.inr.ι    α) := by solve_ι_inj
theorem case.ι.inj   {α : Type _} : Function.Injective (@EctxItem.case.ι   α) := by solve_ι_inj
theorem alloc.ι.inj  {α : Type _} : Function.Injective (@EctxItem.alloc.ι  α) := by solve_ι_inj
theorem load.ι.inj   {α : Type _} : Function.Injective (@EctxItem.load.ι   α) := by solve_ι_inj
theorem storeL.ι.inj {α : Type _} : Function.Injective (@EctxItem.storeL.ι α) := by solve_ι_inj
theorem storeR.ι.inj {α : Type _} : Function.Injective (@EctxItem.storeR.ι α) := by solve_ι_inj
theorem tape.ι.inj   {α : Type _} : Function.Injective (@EctxItem.tape.ι   α) := by solve_ι_inj
theorem randL.ι.inj  {α : Type _} : Function.Injective (@EctxItem.randL.ι  α) := by solve_ι_inj
theorem randR.ι.inj  {α : Type _} : Function.Injective (@EctxItem.randR.ι  α) := by solve_ι_inj
theorem scrut.ι.inj  {α : Type _} : Function.Injective (@EctxItem.scrut.ι  α) := by solve_ι_inj

/-- A cylinder is an `EctxItem`-shaped value with each data-leaf payload replaced by a
measurable set of that type. Syntax-leaf args (`UnOp`, `BinOp`) are kept as-is. -/
inductive Cylinder (α : Type _)
  | appL   (S : Set (Val α))
  | appR   (S : Set (Exp α))
  | unop   (u : UnOp)
  | binopL (op : BinOp) (S : Set (Val α))
  | binopR (op : BinOp) (S : Set (Exp α))
  | condC  (S1 S2 : Set (Exp α))
  | pairL  (S : Set (Val α))
  | pairR  (S : Set (Exp α))
  | fst
  | snd
  | inl
  | inr
  | case   (S1 S2 : Set (Exp α))
  | alloc
  | load
  | storeL (S : Set (Val α))
  | storeR (S : Set (Exp α))
  | tape
  | randL  (S : Set (Val α))
  | randR  (S : Set (Exp α))
  | scrut  (S : Set (Pat α))

/-- An item with all data-leaf payloads forgotten. Syntax-leaf args are kept. -/
inductive Shape
  | appL
  | appR
  | unop (u : UnOp)
  | binopL (op : BinOp)
  | binopR (op : BinOp)
  | condC
  | pairL
  | pairR
  | fst
  | snd
  | inl
  | inr
  | case
  | alloc
  | load
  | storeL
  | storeR
  | tape
  | randL
  | randR
  | scrut
  deriving Countable

/-- Interpret a cylinder as the set of `EctxItem α` it describes. -/
@[simp, stamp_simp] def Cylinder.flatten {α : Type _} : Cylinder α → Set (EctxItem α)
  | .appL S         => EctxItem.appL '' S
  | .appR S         => EctxItem.appR '' S
  | .unop u         => {EctxItem.unop u}
  | .binopL op S    => EctxItem.binopL op '' S
  | .binopR op S    => EctxItem.binopR op '' S
  | .condC S1 S2    => (fun p => EctxItem.condC p.1 p.2) '' (S1 ×ˢ S2)
  | .pairL S        => EctxItem.pairL '' S
  | .pairR S        => EctxItem.pairR '' S
  | .fst            => {EctxItem.fst}
  | .snd            => {EctxItem.snd}
  | .inl            => {EctxItem.inl}
  | .inr            => {EctxItem.inr}
  | .case S1 S2     => (fun p => EctxItem.case p.1 p.2) '' (S1 ×ˢ S2)
  | .alloc          => {EctxItem.alloc}
  | .load           => {EctxItem.load}
  | .storeL S       => EctxItem.storeL '' S
  | .storeR S       => EctxItem.storeR '' S
  | .tape           => {EctxItem.tape}
  | .randL S        => EctxItem.randL '' S
  | .randR S        => EctxItem.randR '' S
  | .scrut S        => EctxItem.scrut '' S

/-- A cylinder has measurable leaves if every data-leaf set is measurable. -/
inductive Cylinder.HasMeasurableLeaves {α : Type _} [MeasurableSpace α] :
    Cylinder α → Prop where
  | appL S   : MeasurableSet S → HasMeasurableLeaves (.appL S)
  | appR S   : MeasurableSet S → HasMeasurableLeaves (.appR S)
  | unop     : HasMeasurableLeaves (.unop u)
  | binopL S : MeasurableSet S → HasMeasurableLeaves (.binopL op S)
  | binopR S : MeasurableSet S → HasMeasurableLeaves (.binopR op S)
  | condC S1 S2 : MeasurableSet S1 → MeasurableSet S2 → HasMeasurableLeaves (.condC S1 S2)
  | pairL S  : MeasurableSet S → HasMeasurableLeaves (.pairL S)
  | pairR S  : MeasurableSet S → HasMeasurableLeaves (.pairR S)
  | fst      : HasMeasurableLeaves .fst
  | snd      : HasMeasurableLeaves .snd
  | inl      : HasMeasurableLeaves .inl
  | inr      : HasMeasurableLeaves .inr
  | case S1 S2 : MeasurableSet S1 → MeasurableSet S2 → HasMeasurableLeaves (.case S1 S2)
  | alloc    : HasMeasurableLeaves .alloc
  | load     : HasMeasurableLeaves .load
  | storeL S : MeasurableSet S → HasMeasurableLeaves (.storeL S)
  | storeR S : MeasurableSet S → HasMeasurableLeaves (.storeR S)
  | tape     : HasMeasurableLeaves .tape
  | randL S  : MeasurableSet S → HasMeasurableLeaves (.randL S)
  | randR S  : MeasurableSet S → HasMeasurableLeaves (.randR S)
  | scrut S  : MeasurableSet S → HasMeasurableLeaves (.scrut S)

instance instMeasurableSpaceEctxItem [MeasurableSpace α] : MeasurableSpace (EctxItem α) :=
  .generateFrom <| Cylinder.flatten '' { c : Cylinder α | c.HasMeasurableLeaves }

@[simp, stamp_simp] def shape : EctxItem α → Shape
  | .appL _       => .appL
  | .appR _       => .appR
  | .unop u       => .unop u
  | .binopL op _  => .binopL op
  | .binopR op _  => .binopR op
  | .condC _ _    => .condC
  | .pairL _      => .pairL
  | .pairR _      => .pairR
  | .fst          => .fst
  | .snd          => .snd
  | .inl          => .inl
  | .inr          => .inr
  | .case _ _     => .case
  | .alloc        => .alloc
  | .load         => .load
  | .storeL _     => .storeL
  | .storeR _     => .storeR
  | .tape         => .tape
  | .randL _      => .randL
  | .randR _      => .randR
  | .scrut _      => .scrut

/-- Shape of a cylinder (forgets data leaves). -/
@[simp, stamp_simp] def Cylinder.shape {α : Type _} : Cylinder α → Shape
  | .appL _       => .appL
  | .appR _       => .appR
  | .unop u       => .unop u
  | .binopL op _  => .binopL op
  | .binopR op _  => .binopR op
  | .condC _ _    => .condC
  | .pairL _      => .pairL
  | .pairR _      => .pairR
  | .fst          => .fst
  | .snd          => .snd
  | .inl          => .inl
  | .inr          => .inr
  | .case _ _     => .case
  | .alloc        => .alloc
  | .load         => .load
  | .storeL _     => .storeL
  | .storeR _     => .storeR
  | .tape         => .tape
  | .randL _      => .randL
  | .randR _      => .randR
  | .scrut _      => .scrut

/-- The "universe cylinder" for a given shape: `univ` at every data leaf, same skeleton. -/
@[simp, stamp_simp] def Shape.cylinder {α : Type _} : Shape → Cylinder α
  | .appL         => .appL Set.univ
  | .appR         => .appR Set.univ
  | .unop u       => .unop u
  | .binopL op    => .binopL op Set.univ
  | .binopR op    => .binopR op Set.univ
  | .condC        => .condC Set.univ Set.univ
  | .pairL        => .pairL Set.univ
  | .pairR        => .pairR Set.univ
  | .fst          => .fst
  | .snd          => .snd
  | .inl          => .inl
  | .inr          => .inr
  | .case         => .case Set.univ Set.univ
  | .alloc        => .alloc
  | .load         => .load
  | .storeL       => .storeL Set.univ
  | .storeR       => .storeR Set.univ
  | .tape         => .tape
  | .randL        => .randL Set.univ
  | .randR        => .randR Set.univ
  | .scrut        => .scrut Set.univ

/-! ### Cylinder intersection. -/

/-- Partial intersection of cylinders. -/
def Cylinder.inter? {α : Type _} : Cylinder α → Cylinder α → Option (Cylinder α)
  | .appL S, .appL S' => some (.appL (S ∩ S'))
  | .appR S, .appR S' => some (.appR (S ∩ S'))
  | .unop u, .unop u' => if u = u' then some (.unop u) else none
  | .binopL op S, .binopL op' S' =>
      if op = op' then some (.binopL op (S ∩ S')) else none
  | .binopR op S, .binopR op' S' =>
      if op = op' then some (.binopR op (S ∩ S')) else none
  | .condC S1 S2, .condC S1' S2' => some (.condC (S1 ∩ S1') (S2 ∩ S2'))
  | .pairL S, .pairL S' => some (.pairL (S ∩ S'))
  | .pairR S, .pairR S' => some (.pairR (S ∩ S'))
  | .fst, .fst => some .fst
  | .snd, .snd => some .snd
  | .inl, .inl => some .inl
  | .inr, .inr => some .inr
  | .case S1 S2, .case S1' S2' => some (.case (S1 ∩ S1') (S2 ∩ S2'))
  | .alloc, .alloc => some .alloc
  | .load, .load => some .load
  | .storeL S, .storeL S' => some (.storeL (S ∩ S'))
  | .storeR S, .storeR S' => some (.storeR (S ∩ S'))
  | .tape, .tape => some .tape
  | .randL S, .randL S' => some (.randL (S ∩ S'))
  | .randR S, .randR S' => some (.randR (S ∩ S'))
  | .scrut S, .scrut S' => some (.scrut (S ∩ S'))
  | _, _ => none

/-- Every element of a cylinder's flatten has that cylinder's shape. -/
theorem Cylinder.shape_of_mem_flatten {α : Type _} {c : Cylinder α} {K : EctxItem α}
    (h : K ∈ Cylinder.flatten c) : EctxItem.shape K = Cylinder.shape c := by
  cases c <;> simp_all <;>
    (first
      | (obtain ⟨_, _, rfl⟩ := h; rfl)
      | (obtain ⟨_, _, _, _, rfl⟩ := h; rfl))

/-- Flattens of cylinders with different shapes are disjoint. -/
theorem Cylinder.flatten_disjoint_of_shape_ne {α : Type _} {c₁ c₂ : Cylinder α}
    (h : Cylinder.shape c₁ ≠ Cylinder.shape c₂) : Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ = ∅ :=
  Stamp.flatten_disjoint_of_shape_ne (cShape := Cylinder.shape)
    (fun {_ _} h => Cylinder.shape_of_mem_flatten h) h

/-- The cylinder flatten of the intersection equals the intersection of the
flattens. Mirrors `BaseLit.Cylinder.flatten_inter`. -/
theorem Cylinder.flatten_inter {α : Type _} (c₁ c₂ : Cylinder α) :
    Cylinder.flatten c₁ ∩ Cylinder.flatten c₂
      = (Cylinder.inter? c₁ c₂).elim ∅ Cylinder.flatten := by
  induction c₁ with
  | appL S =>
    cases c₂
    case appL S' =>
      simp only [Cylinder.flatten, Cylinder.inter?, Option.elim]
      exact Stamp.flatten_inter_data EctxItem.appL.ι.inj
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | appR S =>
    cases c₂
    case appR S' =>
      simp only [Cylinder.flatten, Cylinder.inter?, Option.elim]
      exact Stamp.flatten_inter_data EctxItem.appR.ι.inj
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | unop u =>
    cases c₂
    case unop u' =>
      simp only [Cylinder.flatten]
      refine Stamp.flatten_inter_leaf (flatten := Cylinder.flatten) (ctor := EctxItem.unop)
        (fun _ _ h => by injection h) Cylinder.unop (fun _ => rfl) ?_
      simp only [Cylinder.inter?]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | binopL op S =>
    cases c₂
    case binopL op' S' =>
      simp only [Cylinder.flatten]
      refine Stamp.flatten_inter_mixed_data (flatten := Cylinder.flatten) (ctor := EctxItem.binopL)
        (fun _ _ _ h => by injection h) (fun h => by injection h) Cylinder.binopL (fun _ _ => rfl) ?_
      simp only [Cylinder.inter?]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | binopR op S =>
    cases c₂
    case binopR op' S' =>
      simp only [Cylinder.flatten]
      refine Stamp.flatten_inter_mixed_data (flatten := Cylinder.flatten) (ctor := EctxItem.binopR)
        (fun _ _ _ h => by injection h) (fun h => by injection h) Cylinder.binopR (fun _ _ => rfl) ?_
      simp only [Cylinder.inter?]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | condC S1 S2 =>
    cases c₂
    case condC S1' S2' =>
      simp only [Cylinder.flatten, Cylinder.inter?, Option.elim]
      exact Stamp.flatten_inter_prod EctxItem.condC.ι.inj
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | pairL S =>
    cases c₂
    case pairL S' =>
      simp only [Cylinder.flatten, Cylinder.inter?, Option.elim]
      exact Stamp.flatten_inter_data EctxItem.pairL.ι.inj
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | pairR S =>
    cases c₂
    case pairR S' =>
      simp only [Cylinder.flatten, Cylinder.inter?, Option.elim]
      exact Stamp.flatten_inter_data EctxItem.pairR.ι.inj
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | fst =>
    cases c₂
    case fst => simp [Cylinder.inter?]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | snd =>
    cases c₂
    case snd => simp [Cylinder.inter?]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | inl =>
    cases c₂
    case inl => simp [Cylinder.inter?]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | inr =>
    cases c₂
    case inr => simp [Cylinder.inter?]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | case S1 S2 =>
    cases c₂
    case case S1' S2' =>
      simp only [Cylinder.flatten, Cylinder.inter?, Option.elim]
      exact Stamp.flatten_inter_prod EctxItem.case.ι.inj
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | alloc =>
    cases c₂
    case alloc => simp [Cylinder.inter?]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | load =>
    cases c₂
    case load => simp [Cylinder.inter?]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | storeL S =>
    cases c₂
    case storeL S' =>
      simp only [Cylinder.flatten, Cylinder.inter?, Option.elim]
      exact Stamp.flatten_inter_data EctxItem.storeL.ι.inj
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | storeR S =>
    cases c₂
    case storeR S' =>
      simp only [Cylinder.flatten, Cylinder.inter?, Option.elim]
      exact Stamp.flatten_inter_data EctxItem.storeR.ι.inj
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | tape =>
    cases c₂
    case tape => simp [Cylinder.inter?]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | randL S =>
    cases c₂
    case randL S' =>
      simp only [Cylinder.flatten, Cylinder.inter?, Option.elim]
      exact Stamp.flatten_inter_data EctxItem.randL.ι.inj
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | randR S =>
    cases c₂
    case randR S' =>
      simp only [Cylinder.flatten, Cylinder.inter?, Option.elim]
      exact Stamp.flatten_inter_data EctxItem.randR.ι.inj
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | scrut S =>
    cases c₂
    case scrut S' =>
      simp only [Cylinder.flatten, Cylinder.inter?, Option.elim]
      exact Stamp.flatten_inter_data EctxItem.scrut.ι.inj
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)

theorem Cylinder.flatten_inter_some {α : Type _} {c₁ c₂ c : Cylinder α}
    (h : Cylinder.inter? c₁ c₂ = some c) :
    Cylinder.flatten c = Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ :=
  Stamp.flatten_inter_some Cylinder.flatten_inter h

/-- Inheritance of `HasMeasurableLeaves` under `Cylinder.inter?`. Per-constructor and
linear in constructor count (no `grind`, no heartbeat bump): `cases c₁`, then `cases c₂`
(off-diagonal dies on `inter? = none ≠ some c`), and the diagonal reduces the `inter?`
`some`/`if` and rebuilds the constructor with `MeasurableSet.inter` of the leaf sets. -/
theorem Cylinder.hasMeasurableLeaves_inter [MeasurableSpace α]
    {c₁ c₂ c : Cylinder α}
    (h₁ : c₁.HasMeasurableLeaves) (h₂ : c₂.HasMeasurableLeaves)
    (h : Cylinder.inter? c₁ c₂ = some c) : c.HasMeasurableLeaves := by
  cases c₁ with
  | fst | snd | inl | inr | alloc | load | tape =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    all_goals simp_all
  | appL S₁ | appR S₁ | pairL S₁ | pairR S₁ | storeL S₁ | storeR S₁ | randL S₁ | randR S₁
  | scrut S₁ =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    all_goals (
      cases h₁; cases h₂; injection h with h; subst h
      constructor; exact MeasurableSet.inter ‹_› ‹_›)
  | condC S₁ S₂ | case S₁ S₂ =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    all_goals (
      cases h₁; cases h₂; injection h with h; subst h
      constructor <;> exact MeasurableSet.inter ‹_› ‹_›)
  | unop u =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    cases h₁; cases h₂
    revert h; split <;> rintro ⟨rfl⟩
    exact .unop
  | binopL op S₁ | binopR op S₁ =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    all_goals (
      cases h₁; cases h₂
      revert h; split <;> rintro ⟨rfl⟩
      constructor; exact MeasurableSet.inter ‹_› ‹_›)

/-! ### Per-constructor covers. -/

@[stamp_simp] def cover.appL (S : Set (Val α)) : Set (EctxItem α) := Cylinder.flatten (.appL S)
@[stamp_simp] def cover.appR (S : Set (Exp α)) : Set (EctxItem α) := Cylinder.flatten (.appR S)

@[stamp_simp] def cover.unop (S : Set UnOp) : Set (EctxItem α) :=
  ⋃ u ∈ S, Cylinder.flatten (Cylinder.unop u : Cylinder α)

@[stamp_simp] def cover.binopL (S : Set BinOp) : Set (EctxItem α) :=
  ⋃ op ∈ S, Cylinder.flatten (.binopL op Set.univ)

@[stamp_simp] def cover.binopR (S : Set BinOp) : Set (EctxItem α) :=
  ⋃ op ∈ S, Cylinder.flatten (.binopR op Set.univ)

@[stamp_simp] def cover.condC (S : Set Unit) : Set (EctxItem α) :=
  ⋃ _ ∈ S, Cylinder.flatten (.condC (Set.univ : Set (Exp α)) Set.univ)

@[stamp_simp] def cover.pairL (S : Set (Val α)) : Set (EctxItem α) := Cylinder.flatten (.pairL S)
@[stamp_simp] def cover.pairR (S : Set (Exp α)) : Set (EctxItem α) := Cylinder.flatten (.pairR S)

@[stamp_simp] def cover.fst (S : Set Unit) : Set (EctxItem α) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.fst : Cylinder α)
@[stamp_simp] def cover.snd (S : Set Unit) : Set (EctxItem α) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.snd : Cylinder α)
@[stamp_simp] def cover.inl (S : Set Unit) : Set (EctxItem α) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.inl : Cylinder α)
@[stamp_simp] def cover.inr (S : Set Unit) : Set (EctxItem α) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.inr : Cylinder α)

@[stamp_simp] def cover.case (S : Set Unit) : Set (EctxItem α) :=
  ⋃ _ ∈ S, Cylinder.flatten (.case (Set.univ : Set (Exp α)) Set.univ)

@[stamp_simp] def cover.alloc (S : Set Unit) : Set (EctxItem α) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.alloc : Cylinder α)
@[stamp_simp] def cover.load (S : Set Unit) : Set (EctxItem α) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.load : Cylinder α)

@[stamp_simp] def cover.storeL (S : Set (Val α)) : Set (EctxItem α) := Cylinder.flatten (.storeL S)
@[stamp_simp] def cover.storeR (S : Set (Exp α)) : Set (EctxItem α) := Cylinder.flatten (.storeR S)

@[stamp_simp] def cover.tape (S : Set Unit) : Set (EctxItem α) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.tape : Cylinder α)

@[stamp_simp] def cover.randL (S : Set (Val α)) : Set (EctxItem α) := Cylinder.flatten (.randL S)
@[stamp_simp] def cover.randR (S : Set (Exp α)) : Set (EctxItem α) := Cylinder.flatten (.randR S)

@[stamp_simp] def cover.scrut (S : Set (Pat α)) : Set (EctxItem α) := Cylinder.flatten (.scrut S)

/-- Cylinder of a given shape has measurable leaves. -/
theorem Shape.cylinder_hasMeasurableLeaves [MeasurableSpace α] (s : Shape) :
    (s.cylinder (α := α)).HasMeasurableLeaves := by
  cases s <;> constructor <;> measurability

/-- Flattening a cylinder of a shape equals set of terms with a given shape. -/
@[simp] theorem Shape.cylinder_preimage_shape (s : Shape) :
    (s.cylinder (α := α)).flatten = EctxItem.shape ⁻¹' {s} :=
  Stamp.cylinder_preimage_shape (cShape := Cylinder.shape)
    (fun {_ _} h => Cylinder.shape_of_mem_flatten h)
    (fun s => by cases s <;> simp_all)
    (fun K => by cases K <;> simp_all) s

/-- Flattening a cylinder gives a measurable set. -/
@[measurability]
theorem flatten_measurable [MeasurableSpace α] {c : Cylinder α}
    (hc : c.HasMeasurableLeaves) : MeasurableSet c.flatten :=
  Stamp.flatten_measurable rfl hc

attribute [aesop safe constructors (rule_sets := [Measurable])]
  ProbLang.EctxItem.Cylinder.HasMeasurableLeaves

attribute [aesop safe apply (rule_sets := [Measurable])]
  Shape.cylinder_hasMeasurableLeaves

/-! ### The cylinder flatten family is a π-system that spans `EctxItem α`. -/

theorem Cylinder.flatten_isPiSystem [MeasurableSpace α] :
    IsPiSystem
      ({S : Set (EctxItem α) | ∃ c : Cylinder α, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S}) :=
  Stamp.flatten_isPiSystem Cylinder.flatten_inter
    (fun {_ _ _} => Cylinder.hasMeasurableLeaves_inter)

theorem Cylinder.flatten_isCountablySpanning [MeasurableSpace α] :
    IsCountablySpanning
      ({S : Set (EctxItem α) | ∃ c : Cylinder α, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S}) :=
  Stamp.flatten_isCountablySpanning Shape.cylinder_hasMeasurableLeaves
    Shape.cylinder_preimage_shape .fst .fst

/-! ### Measurability of the per-constructor covers. -/

@[measurability]
theorem cover.appL.measurable [MeasurableSpace α] {S : Set (Val α)} (hS : MeasurableSet S) :
    MeasurableSet (appL (α := α) S) := flatten_measurable (.appL _ hS)

@[measurability]
theorem cover.appR.measurable [MeasurableSpace α] {S : Set (Exp α)} (hS : MeasurableSet S) :
    MeasurableSet (appR (α := α) S) := flatten_measurable (.appR _ hS)

@[measurability]
theorem cover.unop.measurable [MeasurableSpace α] (S : Set UnOp) :
    MeasurableSet (unop (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.binopL.measurable [MeasurableSpace α] (S : Set BinOp) :
    MeasurableSet (binopL (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.binopR.measurable [MeasurableSpace α] (S : Set BinOp) :
    MeasurableSet (binopR (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.condC.measurable [MeasurableSpace α] (S : Set Unit) :
    MeasurableSet (condC (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.pairL.measurable [MeasurableSpace α] {S : Set (Val α)} (hS : MeasurableSet S) :
    MeasurableSet (pairL (α := α) S) := flatten_measurable (.pairL _ hS)

@[measurability]
theorem cover.pairR.measurable [MeasurableSpace α] {S : Set (Exp α)} (hS : MeasurableSet S) :
    MeasurableSet (pairR (α := α) S) := flatten_measurable (.pairR _ hS)

@[measurability]
theorem cover.fst.measurable [MeasurableSpace α] (S : Set Unit) :
    MeasurableSet (fst (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.snd.measurable [MeasurableSpace α] (S : Set Unit) :
    MeasurableSet (snd (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.inl.measurable [MeasurableSpace α] (S : Set Unit) :
    MeasurableSet (inl (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.inr.measurable [MeasurableSpace α] (S : Set Unit) :
    MeasurableSet (inr (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.case.measurable [MeasurableSpace α] (S : Set Unit) :
    MeasurableSet (case (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.alloc.measurable [MeasurableSpace α] (S : Set Unit) :
    MeasurableSet (alloc (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.load.measurable [MeasurableSpace α] (S : Set Unit) :
    MeasurableSet (load (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.storeL.measurable [MeasurableSpace α] {S : Set (Val α)} (hS : MeasurableSet S) :
    MeasurableSet (storeL (α := α) S) := flatten_measurable (.storeL _ hS)

@[measurability]
theorem cover.storeR.measurable [MeasurableSpace α] {S : Set (Exp α)} (hS : MeasurableSet S) :
    MeasurableSet (storeR (α := α) S) := flatten_measurable (.storeR _ hS)

@[measurability]
theorem cover.tape.measurable [MeasurableSpace α] (S : Set Unit) :
    MeasurableSet (tape (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.randL.measurable [MeasurableSpace α] {S : Set (Val α)} (hS : MeasurableSet S) :
    MeasurableSet (randL (α := α) S) := flatten_measurable (.randL _ hS)

@[measurability]
theorem cover.randR.measurable [MeasurableSpace α] {S : Set (Exp α)} (hS : MeasurableSet S) :
    MeasurableSet (randR (α := α) S) := flatten_measurable (.randR _ hS)

@[measurability]
theorem cover.scrut.measurable [MeasurableSpace α] {S : Set (Pat α)} (hS : MeasurableSet S) :
    MeasurableSet (scrut (α := α) S) := flatten_measurable (.scrut _ hS)

theorem cover.appL_eq_image (S : Set (Val α)) :
    cover.appL (α := α) S = EctxItem.appL '' S := by solve_cover_eq_image cover.appL

theorem cover.appR_eq_image (S : Set (Exp α)) :
    cover.appR (α := α) S = EctxItem.appR '' S := by solve_cover_eq_image cover.appR

theorem cover.unop_eq_image (S : Set UnOp) :
    cover.unop (α := α) S = EctxItem.unop '' S := by solve_cover_eq_image cover.unop

theorem cover.binopL_univ_eq_range :
    cover.binopL (α := α) Set.univ = .range (Function.uncurry EctxItem.binopL) := by
  solve_cover_eq_image cover.binopL

theorem cover.binopR_univ_eq_range :
    cover.binopR (α := α) Set.univ = .range (Function.uncurry EctxItem.binopR) := by
  solve_cover_eq_image cover.binopR

theorem cover.condC_univ_eq_range :
    cover.condC (α := α) Set.univ = .range (Function.uncurry EctxItem.condC) := by
  solve_cover_eq_image cover.condC

theorem cover.pairL_eq_image (S : Set (Val α)) :
    cover.pairL (α := α) S = EctxItem.pairL '' S := by solve_cover_eq_image cover.pairL

theorem cover.pairR_eq_image (S : Set (Exp α)) :
    cover.pairR (α := α) S = EctxItem.pairR '' S := by solve_cover_eq_image cover.pairR

theorem cover.fst_eq_image (S : Set Unit) :
    cover.fst (α := α) S = (fun _ : Unit => (EctxItem.fst : EctxItem α)) '' S := by
  solve_cover_eq_image cover.fst

theorem cover.snd_eq_image (S : Set Unit) :
    cover.snd (α := α) S = (fun _ : Unit => (EctxItem.snd : EctxItem α)) '' S := by
  solve_cover_eq_image cover.snd

theorem cover.inl_eq_image (S : Set Unit) :
    cover.inl (α := α) S = (fun _ : Unit => (EctxItem.inl : EctxItem α)) '' S := by
  solve_cover_eq_image cover.inl

theorem cover.inr_eq_image (S : Set Unit) :
    cover.inr (α := α) S = (fun _ : Unit => (EctxItem.inr : EctxItem α)) '' S := by
  solve_cover_eq_image cover.inr

theorem cover.case_univ_eq_range :
    cover.case (α := α) Set.univ = .range (Function.uncurry EctxItem.case) := by
  solve_cover_eq_image cover.case

theorem cover.alloc_eq_image (S : Set Unit) :
    cover.alloc (α := α) S = (fun _ : Unit => (EctxItem.alloc : EctxItem α)) '' S := by
  solve_cover_eq_image cover.alloc

theorem cover.load_eq_image (S : Set Unit) :
    cover.load (α := α) S = (fun _ : Unit => (EctxItem.load : EctxItem α)) '' S := by
  solve_cover_eq_image cover.load

theorem cover.storeL_eq_image (S : Set (Val α)) :
    cover.storeL (α := α) S = EctxItem.storeL '' S := by solve_cover_eq_image cover.storeL

theorem cover.storeR_eq_image (S : Set (Exp α)) :
    cover.storeR (α := α) S = EctxItem.storeR '' S := by solve_cover_eq_image cover.storeR

theorem cover.tape_eq_image (S : Set Unit) :
    cover.tape (α := α) S = (fun _ : Unit => (EctxItem.tape : EctxItem α)) '' S := by
  solve_cover_eq_image cover.tape

theorem cover.randL_eq_image (S : Set (Val α)) :
    cover.randL (α := α) S = EctxItem.randL '' S := by solve_cover_eq_image cover.randL

theorem cover.randR_eq_image (S : Set (Exp α)) :
    cover.randR (α := α) S = EctxItem.randR '' S := by solve_cover_eq_image cover.randR

theorem cover.scrut_eq_image (S : Set (Pat α)) :
    cover.scrut (α := α) S = EctxItem.scrut '' S := by solve_cover_eq_image cover.scrut

/-! ### Measurable constructors. -/

@[fun_prop]
theorem unop.ι.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (EctxItem.unop.ι (α := α)) := (by measurability)

@[fun_prop]
theorem fst.ι.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (EctxItem.fst.ι (α := α)) := (by measurability)

@[fun_prop]
theorem snd.ι.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (EctxItem.snd.ι (α := α)) := (by measurability)

@[fun_prop]
theorem inl.ι.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (EctxItem.inl.ι (α := α)) := (by measurability)

@[fun_prop]
theorem inr.ι.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (EctxItem.inr.ι (α := α)) := (by measurability)

@[fun_prop]
theorem alloc.ι.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (EctxItem.alloc.ι (α := α)) := (by measurability)

@[fun_prop]
theorem load.ι.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (EctxItem.load.ι (α := α)) := (by measurability)

@[fun_prop]
theorem tape.ι.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (EctxItem.tape.ι (α := α)) := (by measurability)

@[fun_prop]
theorem appL.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.appL.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @appL S hS =>
    suffices h : EctxItem.appL.ι ⁻¹' Cylinder.flatten (.appL S) = S by rw [h]; exact hS
    ext v; simp
  | _ => convert MeasurableSet.empty; ext v; simp

@[fun_prop]
theorem appR.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.appR.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @appR S hS =>
    suffices h : EctxItem.appR.ι ⁻¹' Cylinder.flatten (.appR S) = S by rw [h]; exact hS
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem pairL.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.pairL.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @pairL S hS =>
    suffices h : EctxItem.pairL.ι ⁻¹' Cylinder.flatten (.pairL S) = S by rw [h]; exact hS
    ext v; simp
  | _ => convert MeasurableSet.empty; ext v; simp

@[fun_prop]
theorem pairR.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.pairR.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @pairR S hS =>
    suffices h : EctxItem.pairR.ι ⁻¹' Cylinder.flatten (.pairR S) = S by rw [h]; exact hS
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem storeL.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.storeL.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @storeL S hS =>
    suffices h : EctxItem.storeL.ι ⁻¹' Cylinder.flatten (.storeL S) = S by rw [h]; exact hS
    ext v; simp
  | _ => convert MeasurableSet.empty; ext v; simp

@[fun_prop]
theorem storeR.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.storeR.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @storeR S hS =>
    suffices h : EctxItem.storeR.ι ⁻¹' Cylinder.flatten (.storeR S) = S by rw [h]; exact hS
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem randL.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.randL.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @randL S hS =>
    suffices h : EctxItem.randL.ι ⁻¹' Cylinder.flatten (.randL S) = S by rw [h]; exact hS
    ext v; simp
  | _ => convert MeasurableSet.empty; ext v; simp

@[fun_prop]
theorem randR.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.randR.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @randR S hS =>
    suffices h : EctxItem.randR.ι ⁻¹' Cylinder.flatten (.randR S) = S by rw [h]; exact hS
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem scrut.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.scrut.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @scrut S hS =>
    suffices h : EctxItem.scrut.ι ⁻¹' Cylinder.flatten (.scrut S) = S by rw [h]; exact hS
    ext p; simp
  | _ => convert MeasurableSet.empty; ext p; simp

@[fun_prop]
theorem binopL.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.binopL.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @binopL op S hS =>
    suffices heq : EctxItem.binopL.ι ⁻¹' Cylinder.flatten (.binopL op S)
                = ({op} : Set BinOp) ×ˢ S by rw [heq]; measurability
    ext ⟨_, _⟩; simp; tauto
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop]
theorem binopR.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.binopR.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @binopR op S hS =>
    suffices heq : EctxItem.binopR.ι ⁻¹' Cylinder.flatten (.binopR op S)
                = ({op} : Set BinOp) ×ˢ S by rw [heq]; measurability
    ext ⟨_, _⟩; simp; tauto
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop]
theorem condC.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.condC.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @condC S1 S2 hS1 hS2 =>
    suffices h : EctxItem.condC.ι ⁻¹' Cylinder.flatten (.condC S1 S2)
                = S1 ×ˢ S2 by rw [h]; measurability
    ext ⟨_, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop]
theorem case.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.case.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @case S1 S2 hS1 hS2 =>
    suffices h : EctxItem.case.ι ⁻¹' Cylinder.flatten (.case S1 S2)
                = S1 ×ˢ S2 by rw [h]; measurability
    ext ⟨_, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

/-! ### Raw-constructor `fun_prop` lemmas. Nullary ctors are constants and don't
need lemmas; arity-1 ctors get a `Measurable f` form; arity-2 get `Function.uncurry`. -/

@[fun_prop]
theorem unop.measurable [MeasurableSpace α] :
    Measurable (EctxItem.unop : UnOp → EctxItem α) := unop.ι.measurable

@[fun_prop]
theorem appL.measurable [MeasurableSpace α] :
    Measurable (EctxItem.appL : Val α → EctxItem α) := appL.ι.measurable

@[fun_prop]
theorem appR.measurable [MeasurableSpace α] :
    Measurable (EctxItem.appR : Exp α → EctxItem α) := appR.ι.measurable

@[fun_prop]
theorem pairL.measurable [MeasurableSpace α] :
    Measurable (EctxItem.pairL : Val α → EctxItem α) := pairL.ι.measurable

@[fun_prop]
theorem pairR.measurable [MeasurableSpace α] :
    Measurable (EctxItem.pairR : Exp α → EctxItem α) := pairR.ι.measurable

@[fun_prop]
theorem storeL.measurable [MeasurableSpace α] :
    Measurable (EctxItem.storeL : Val α → EctxItem α) := storeL.ι.measurable

@[fun_prop]
theorem storeR.measurable [MeasurableSpace α] :
    Measurable (EctxItem.storeR : Exp α → EctxItem α) := storeR.ι.measurable

@[fun_prop]
theorem randL.measurable [MeasurableSpace α] :
    Measurable (EctxItem.randL : Val α → EctxItem α) := randL.ι.measurable

@[fun_prop]
theorem randR.measurable [MeasurableSpace α] :
    Measurable (EctxItem.randR : Exp α → EctxItem α) := randR.ι.measurable

@[fun_prop]
theorem scrut.measurable [MeasurableSpace α] :
    Measurable (EctxItem.scrut : Pat α → EctxItem α) := scrut.ι.measurable

@[fun_prop]
theorem binopL.measurable [MeasurableSpace α] :
    Measurable (Function.uncurry (EctxItem.binopL : BinOp → Val α → EctxItem α)) :=
  binopL.ι.measurable

@[fun_prop]
theorem binopR.measurable [MeasurableSpace α] :
    Measurable (Function.uncurry (EctxItem.binopR : BinOp → Exp α → EctxItem α)) :=
  binopR.ι.measurable

@[fun_prop]
theorem condC.measurable [MeasurableSpace α] :
    Measurable (Function.uncurry (EctxItem.condC : Exp α → Exp α → EctxItem α)) :=
  condC.ι.measurable

@[fun_prop]
theorem case.measurable [MeasurableSpace α] :
    Measurable (Function.uncurry (EctxItem.case : Exp α → Exp α → EctxItem α)) :=
  case.ι.measurable

/-! ### Measurable embeddings. -/

theorem unop.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.unop : UnOp → EctxItem α) := by
  solve_discrete_ME cover.unop_eq_image, cover.unop.measurable

theorem fst.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (fun _ : Unit => (EctxItem.fst : EctxItem α)) := by
  solve_nullary_ME cover.fst, cover.fst_eq_image, cover.fst.measurable

theorem snd.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (fun _ : Unit => (EctxItem.snd : EctxItem α)) := by
  solve_nullary_ME cover.snd, cover.snd_eq_image, cover.snd.measurable

theorem inl.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (fun _ : Unit => (EctxItem.inl : EctxItem α)) := by
  solve_nullary_ME cover.inl, cover.inl_eq_image, cover.inl.measurable

theorem inr.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (fun _ : Unit => (EctxItem.inr : EctxItem α)) := by
  solve_nullary_ME cover.inr, cover.inr_eq_image, cover.inr.measurable

theorem alloc.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (fun _ : Unit => (EctxItem.alloc : EctxItem α)) := by
  solve_nullary_ME cover.alloc, cover.alloc_eq_image, cover.alloc.measurable

theorem load.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (fun _ : Unit => (EctxItem.load : EctxItem α)) := by
  solve_nullary_ME cover.load, cover.load_eq_image, cover.load.measurable

theorem tape.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (fun _ : Unit => (EctxItem.tape : EctxItem α)) := by
  solve_nullary_ME cover.tape, cover.tape_eq_image, cover.tape.measurable

theorem appL.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.appL : Val α → EctxItem α) :=
  ⟨fun _ _ h => by injection h, EctxItem.appL.ι.measurable,
    fun _ hS => flatten_measurable (.appL _ hS)⟩

theorem appR.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.appR : Exp α → EctxItem α) :=
  ⟨fun _ _ h => by injection h, EctxItem.appR.ι.measurable,
    fun _ hS => flatten_measurable (.appR _ hS)⟩

theorem pairL.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.pairL : Val α → EctxItem α) :=
  ⟨fun _ _ h => by injection h, EctxItem.pairL.ι.measurable,
    fun _ hS => flatten_measurable (.pairL _ hS)⟩

theorem pairR.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.pairR : Exp α → EctxItem α) :=
  ⟨fun _ _ h => by injection h, EctxItem.pairR.ι.measurable,
    fun _ hS => flatten_measurable (.pairR _ hS)⟩

theorem storeL.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.storeL : Val α → EctxItem α) :=
  ⟨fun _ _ h => by injection h, EctxItem.storeL.ι.measurable,
    fun _ hS => flatten_measurable (.storeL _ hS)⟩

theorem storeR.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.storeR : Exp α → EctxItem α) :=
  ⟨fun _ _ h => by injection h, EctxItem.storeR.ι.measurable,
    fun _ hS => flatten_measurable (.storeR _ hS)⟩

theorem randL.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.randL : Val α → EctxItem α) :=
  ⟨fun _ _ h => by injection h, EctxItem.randL.ι.measurable,
    fun _ hS => flatten_measurable (.randL _ hS)⟩

theorem randR.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.randR : Exp α → EctxItem α) :=
  ⟨fun _ _ h => by injection h, EctxItem.randR.ι.measurable,
    fun _ hS => flatten_measurable (.randR _ hS)⟩

theorem scrut.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.scrut : Pat α → EctxItem α) :=
  ⟨fun _ _ h => by injection h, EctxItem.scrut.ι.measurable,
    fun _ hS => flatten_measurable (.scrut _ hS)⟩

theorem binopL.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (Function.uncurry (EctxItem.binopL : BinOp → Val α → EctxItem α)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := EctxItem.binopL.ι.inj) (h_meas := EctxItem.binopL.ι.measurable)
    (h_gen := (generateFrom_eq_prod singletonsAndUniv_generateFrom
                MeasurableSpace.generateFrom_measurableSet
                singletonsAndUniv_isCountablySpanning isCountablySpanning_measurableSet).symm)
    (h_pi := singletonsAndUniv_isPiSystem.prod
              (fun S (hS : MeasurableSet S) T (hT : MeasurableSet T) _ => hS.inter hT))
    (h_basic := by
      rintro A hA S (hS : MeasurableSet S)
      rcases hA with rfl | ⟨op, rfl⟩
      · rw [show ((Function.uncurry EctxItem.binopL) '' (Set.univ ×ˢ S) : Set (EctxItem α))
              = ⋃ op : BinOp, EctxItem.binopL op '' S from by
            ext K; simp [Function.uncurry]]
        exact .iUnion fun op => flatten_measurable (.binopL (op := op) _ hS)
      · rw [show ((Function.uncurry EctxItem.binopL) '' (({op} : Set BinOp) ×ˢ S) : Set (EctxItem α))
              = Cylinder.flatten (.binopL op S) from by ext K; cases K <;> simp [Function.uncurry]]
        exact flatten_measurable (.binopL _ hS))
    (h_cov_meas := cover.binopL.measurable _) (h_cov_range := cover.binopL_univ_eq_range)

theorem binopR.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (Function.uncurry (EctxItem.binopR : BinOp → Exp α → EctxItem α)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := EctxItem.binopR.ι.inj) (h_meas := EctxItem.binopR.ι.measurable)
    (h_gen := (generateFrom_eq_prod singletonsAndUniv_generateFrom
                MeasurableSpace.generateFrom_measurableSet
                singletonsAndUniv_isCountablySpanning isCountablySpanning_measurableSet).symm)
    (h_pi := singletonsAndUniv_isPiSystem.prod
              (fun S (hS : MeasurableSet S) T (hT : MeasurableSet T) _ => hS.inter hT))
    (h_basic := by
      rintro A hA S (hS : MeasurableSet S)
      rcases hA with rfl | ⟨op, rfl⟩
      · rw [show ((Function.uncurry EctxItem.binopR) '' (Set.univ ×ˢ S) : Set (EctxItem α))
              = ⋃ op : BinOp, EctxItem.binopR op '' S from by
            ext K; simp [Function.uncurry]]
        exact .iUnion fun op => flatten_measurable (.binopR (op := op) _ hS)
      · rw [show ((Function.uncurry EctxItem.binopR) '' (({op} : Set BinOp) ×ˢ S) : Set (EctxItem α))
              = Cylinder.flatten (.binopR op S) from by ext K; cases K <;> simp [Function.uncurry]]
        exact flatten_measurable (.binopR _ hS))
    (h_cov_meas := cover.binopR.measurable _) (h_cov_range := cover.binopR_univ_eq_range)

theorem condC.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (Function.uncurry (EctxItem.condC : Exp α → Exp α → EctxItem α)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := EctxItem.condC.ι.inj) (h_meas := EctxItem.condC.ι.measurable)
    (h_gen := (generateFrom_eq_prod MeasurableSpace.generateFrom_measurableSet
                MeasurableSpace.generateFrom_measurableSet
                isCountablySpanning_measurableSet isCountablySpanning_measurableSet).symm)
    (h_pi := IsPiSystem.prod
              (fun S (hS : MeasurableSet S) T (hT : MeasurableSet T) _ => hS.inter hT)
              (fun S (hS : MeasurableSet S) T (hT : MeasurableSet T) _ => hS.inter hT))
    (h_basic := by
      rintro S₁ (hS₁ : MeasurableSet S₁) S₂ (hS₂ : MeasurableSet S₂)
      rw [show ((Function.uncurry EctxItem.condC) '' (S₁ ×ˢ S₂) : Set (EctxItem α))
            = Cylinder.flatten (.condC S₁ S₂) from by ext K; cases K <;> simp [Function.uncurry]]
      exact flatten_measurable (.condC _ _ hS₁ hS₂))
    (h_cov_meas := cover.condC.measurable _) (h_cov_range := cover.condC_univ_eq_range)

theorem case.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (Function.uncurry (EctxItem.case : Exp α → Exp α → EctxItem α)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := EctxItem.case.ι.inj) (h_meas := EctxItem.case.ι.measurable)
    (h_gen := (generateFrom_eq_prod MeasurableSpace.generateFrom_measurableSet
                MeasurableSpace.generateFrom_measurableSet
                isCountablySpanning_measurableSet isCountablySpanning_measurableSet).symm)
    (h_pi := IsPiSystem.prod
              (fun S (hS : MeasurableSet S) T (hT : MeasurableSet T) _ => hS.inter hT)
              (fun S (hS : MeasurableSet S) T (hT : MeasurableSet T) _ => hS.inter hT))
    (h_basic := by
      rintro S₁ (hS₁ : MeasurableSet S₁) S₂ (hS₂ : MeasurableSet S₂)
      rw [show ((Function.uncurry EctxItem.case) '' (S₁ ×ˢ S₂) : Set (EctxItem α))
            = Cylinder.flatten (.case S₁ S₂) from by ext K; cases K <;> simp [Function.uncurry]]
      exact flatten_measurable (.case _ _ hS₁ hS₂))
    (h_cov_meas := cover.case.measurable _) (h_cov_range := cover.case_univ_eq_range)

/-- Per-constructor cell family for the `casesOn` preimage decomposition. -/
def decompCell
    {α : Type _} {β : Type _} (S : Set β)
    (f_appL : Val α → β) (f_appR : Exp α → β) (f_unop : UnOp → β)
    (f_binopL : BinOp × Val α → β) (f_binopR : BinOp × Exp α → β)
    (f_condC : Exp α × Exp α → β)
    (f_pairL : Val α → β) (f_pairR : Exp α → β)
    (f_fst : Unit → β) (f_snd : Unit → β) (f_inl : Unit → β) (f_inr : Unit → β)
    (f_case : Exp α × Exp α → β)
    (f_alloc : Unit → β) (f_load : Unit → β)
    (f_storeL : Val α → β) (f_storeR : Exp α → β)
    (f_tape : Unit → β)
    (f_randL : Val α → β) (f_randR : Exp α → β)
    (f_scrut : Pat α → β) : Fin 21 → Set (EctxItem α) :=
  ![ EctxItem.appL.ι   '' (f_appL   ⁻¹' S)
   , EctxItem.appR.ι   '' (f_appR   ⁻¹' S)
   , EctxItem.unop.ι   '' (f_unop   ⁻¹' S)
   , EctxItem.binopL.ι '' (f_binopL ⁻¹' S)
   , EctxItem.binopR.ι '' (f_binopR ⁻¹' S)
   , EctxItem.condC.ι  '' (f_condC  ⁻¹' S)
   , EctxItem.pairL.ι  '' (f_pairL  ⁻¹' S)
   , EctxItem.pairR.ι  '' (f_pairR  ⁻¹' S)
   , EctxItem.fst.ι    '' (f_fst    ⁻¹' S)
   , EctxItem.snd.ι    '' (f_snd    ⁻¹' S)
   , EctxItem.inl.ι    '' (f_inl    ⁻¹' S)
   , EctxItem.inr.ι    '' (f_inr    ⁻¹' S)
   , EctxItem.case.ι   '' (f_case   ⁻¹' S)
   , EctxItem.alloc.ι  '' (f_alloc  ⁻¹' S)
   , EctxItem.load.ι   '' (f_load   ⁻¹' S)
   , EctxItem.storeL.ι '' (f_storeL ⁻¹' S)
   , EctxItem.storeR.ι '' (f_storeR ⁻¹' S)
   , EctxItem.tape.ι   '' (f_tape   ⁻¹' S)
   , EctxItem.randL.ι  '' (f_randL  ⁻¹' S)
   , EctxItem.randR.ι  '' (f_randR  ⁻¹' S)
   , EctxItem.scrut.ι  '' (f_scrut  ⁻¹' S) ]

theorem casesOn_preimage_decomp
    {α : Type _} {β : Type _} (S : Set β)
    (f_appL : Val α → β) (f_appR : Exp α → β) (f_unop : UnOp → β)
    (f_binopL : BinOp × Val α → β) (f_binopR : BinOp × Exp α → β)
    (f_condC : Exp α × Exp α → β)
    (f_pairL : Val α → β) (f_pairR : Exp α → β)
    (f_fst : Unit → β) (f_snd : Unit → β) (f_inl : Unit → β) (f_inr : Unit → β)
    (f_case : Exp α × Exp α → β)
    (f_alloc : Unit → β) (f_load : Unit → β)
    (f_storeL : Val α → β) (f_storeR : Exp α → β)
    (f_tape : Unit → β)
    (f_randL : Val α → β) (f_randR : Exp α → β)
    (f_scrut : Pat α → β) :
    (fun K : EctxItem α => EctxItem.casesOn (motive := fun _ => β) K
        f_appL f_appR f_unop
        (fun op v => f_binopL (op, v))
        (fun op e => f_binopR (op, e))
        (fun e₁ e₂ => f_condC (e₁, e₂))
        f_pairL f_pairR
        (f_fst ()) (f_snd ()) (f_inl ()) (f_inr ())
        (fun e₁ e₂ => f_case (e₁, e₂))
        (f_alloc ()) (f_load ())
        f_storeL f_storeR
        (f_tape ())
        f_randL f_randR
        f_scrut) ⁻¹' S
      = ⋃ i, decompCell S f_appL f_appR f_unop f_binopL f_binopR f_condC
          f_pairL f_pairR f_fst f_snd f_inl f_inr f_case f_alloc f_load
          f_storeL f_storeR f_tape f_randL f_randR f_scrut i := by
  ext K
  simp only [Set.mem_preimage, Set.mem_iUnion, decompCell]
  constructor
  · intro hK; cases K
    · exact ⟨0, _, hK, rfl⟩
    · exact ⟨1, _, hK, rfl⟩
    · exact ⟨2, _, hK, rfl⟩
    · exact ⟨3, ⟨_, _⟩, hK, rfl⟩
    · exact ⟨4, ⟨_, _⟩, hK, rfl⟩
    · exact ⟨5, ⟨_, _⟩, hK, rfl⟩
    · exact ⟨6, _, hK, rfl⟩
    · exact ⟨7, _, hK, rfl⟩
    · exact ⟨8, (), hK, rfl⟩
    · exact ⟨9, (), hK, rfl⟩
    · exact ⟨10, (), hK, rfl⟩
    · exact ⟨11, (), hK, rfl⟩
    · exact ⟨12, ⟨_, _⟩, hK, rfl⟩
    · exact ⟨13, (), hK, rfl⟩
    · exact ⟨14, (), hK, rfl⟩
    · exact ⟨15, _, hK, rfl⟩
    · exact ⟨16, _, hK, rfl⟩
    · exact ⟨17, (), hK, rfl⟩
    · exact ⟨18, _, hK, rfl⟩
    · exact ⟨19, _, hK, rfl⟩
    · exact ⟨20, _, hK, rfl⟩
  · rintro ⟨i, hi⟩; fin_cases i <;>
      · obtain ⟨q, hq, hp⟩ := hi; cases hp; simpa using hq

@[fun_prop]
theorem measurable_rec
    {α : Type _} [MeasurableSpace α]
    {β : Type _} [MeasurableSpace β]
    (f_appL : Val α → β) (f_appR : Exp α → β) (f_unop : UnOp → β)
    (f_binopL : BinOp × Val α → β) (f_binopR : BinOp × Exp α → β)
    (f_condC : Exp α × Exp α → β)
    (f_pairL : Val α → β) (f_pairR : Exp α → β)
    (f_fst : Unit → β) (f_snd : Unit → β) (f_inl : Unit → β) (f_inr : Unit → β)
    (f_case : Exp α × Exp α → β)
    (f_alloc : Unit → β) (f_load : Unit → β)
    (f_storeL : Val α → β) (f_storeR : Exp α → β)
    (f_tape : Unit → β)
    (f_randL : Val α → β) (f_randR : Exp α → β)
    (f_scrut : Pat α → β)
    (h_appL : Measurable f_appL) (h_appR : Measurable f_appR)
    (h_binopL : Measurable f_binopL) (h_binopR : Measurable f_binopR)
    (h_condC : Measurable f_condC)
    (h_pairL : Measurable f_pairL) (h_pairR : Measurable f_pairR)
    (h_case : Measurable f_case)
    (h_storeL : Measurable f_storeL) (h_storeR : Measurable f_storeR)
    (h_randL : Measurable f_randL) (h_randR : Measurable f_randR)
    (h_scrut : Measurable f_scrut) :
    Measurable (fun K : EctxItem α => EctxItem.casesOn (motive := fun _ => β) K
        f_appL f_appR f_unop
        (fun op v => f_binopL (op, v))
        (fun op e => f_binopR (op, e))
        (fun e₁ e₂ => f_condC (e₁, e₂))
        f_pairL f_pairR
        (f_fst ()) (f_snd ()) (f_inl ()) (f_inr ())
        (fun e₁ e₂ => f_case (e₁, e₂))
        (f_alloc ()) (f_load ())
        f_storeL f_storeR
        (f_tape ())
        f_randL f_randR
        f_scrut) := by
  intro S hS
  rw [EctxItem.casesOn_preimage_decomp]
  refine .iUnion fun i => ?_
  fin_cases i
  · exact appL.measurableEmbedding.measurableSet_image'   (h_appL hS)
  · exact appR.measurableEmbedding.measurableSet_image'   (h_appR hS)
  · exact unop.measurableEmbedding.measurableSet_image'   (by measurability)
  · exact binopL.measurableEmbedding.measurableSet_image' (h_binopL hS)
  · exact binopR.measurableEmbedding.measurableSet_image' (h_binopR hS)
  · exact condC.measurableEmbedding.measurableSet_image'  (h_condC hS)
  · exact pairL.measurableEmbedding.measurableSet_image'  (h_pairL hS)
  · exact pairR.measurableEmbedding.measurableSet_image'  (h_pairR hS)
  · exact fst.measurableEmbedding.measurableSet_image'    (by measurability)
  · exact snd.measurableEmbedding.measurableSet_image'    (by measurability)
  · exact inl.measurableEmbedding.measurableSet_image'    (by measurability)
  · exact inr.measurableEmbedding.measurableSet_image'    (by measurability)
  · exact case.measurableEmbedding.measurableSet_image'   (h_case hS)
  · exact alloc.measurableEmbedding.measurableSet_image'  (by measurability)
  · exact load.measurableEmbedding.measurableSet_image'   (by measurability)
  · exact storeL.measurableEmbedding.measurableSet_image' (h_storeL hS)
  · exact storeR.measurableEmbedding.measurableSet_image' (h_storeR hS)
  · exact tape.measurableEmbedding.measurableSet_image'   (by measurability)
  · exact randL.measurableEmbedding.measurableSet_image'  (h_randL hS)
  · exact randR.measurableEmbedding.measurableSet_image'  (h_randR hS)
  · exact scrut.measurableEmbedding.measurableSet_image'  (h_scrut hS)

/-! ### Param-threaded one-level dispatch.

`measurable_rec_param` is the joint analogue of `measurable_rec`: continuations
take both the constructor payload AND an external `β` parameter, and the result
is joint-measurable in `(K, b) : EctxItem α × β`. Built directly from
`casesOn_preimage_decomp_param` via `Prod.map`-style embeddings.

This is the analogue of `Exp.measurable_rec_param`; the only difference is the
21-way constructor list of `EctxItem`. -/

/-- Per-constructor cell family for the `β`-parameterised decomposition. -/
def decompCell_param
    {α : Type _} {β γ : Type _} (S : Set γ)
    (f_appL : β × Val α → γ) (f_appR : β × Exp α → γ) (f_unop : β × UnOp → γ)
    (f_binopL : β × BinOp × Val α → γ) (f_binopR : β × BinOp × Exp α → γ)
    (f_condC : β × Exp α × Exp α → γ)
    (f_pairL : β × Val α → γ) (f_pairR : β × Exp α → γ)
    (f_fst : β × Unit → γ) (f_snd : β × Unit → γ)
    (f_inl : β × Unit → γ) (f_inr : β × Unit → γ)
    (f_case : β × Exp α × Exp α → γ)
    (f_alloc : β × Unit → γ) (f_load : β × Unit → γ)
    (f_storeL : β × Val α → γ) (f_storeR : β × Exp α → γ)
    (f_tape : β × Unit → γ)
    (f_randL : β × Val α → γ) (f_randR : β × Exp α → γ)
    (f_scrut : β × Pat α → γ) : Fin 21 → Set (EctxItem α × β) :=
  ![ (fun q : β × Val α => (EctxItem.appL q.2, q.1))   '' (f_appL   ⁻¹' S)
   , (fun q : β × Exp α => (EctxItem.appR q.2, q.1))   '' (f_appR   ⁻¹' S)
   , (fun q : β × UnOp => (EctxItem.unop q.2, q.1))    '' (f_unop   ⁻¹' S)
   , (fun q : β × BinOp × Val α => (EctxItem.binopL q.2.1 q.2.2, q.1)) '' (f_binopL ⁻¹' S)
   , (fun q : β × BinOp × Exp α => (EctxItem.binopR q.2.1 q.2.2, q.1)) '' (f_binopR ⁻¹' S)
   , (fun q : β × Exp α × Exp α => (EctxItem.condC q.2.1 q.2.2, q.1))  '' (f_condC  ⁻¹' S)
   , (fun q : β × Val α => (EctxItem.pairL q.2, q.1))  '' (f_pairL  ⁻¹' S)
   , (fun q : β × Exp α => (EctxItem.pairR q.2, q.1))  '' (f_pairR  ⁻¹' S)
   , (fun q : β × Unit => (EctxItem.fst, q.1))         '' (f_fst    ⁻¹' S)
   , (fun q : β × Unit => (EctxItem.snd, q.1))         '' (f_snd    ⁻¹' S)
   , (fun q : β × Unit => (EctxItem.inl, q.1))         '' (f_inl    ⁻¹' S)
   , (fun q : β × Unit => (EctxItem.inr, q.1))         '' (f_inr    ⁻¹' S)
   , (fun q : β × Exp α × Exp α => (EctxItem.case q.2.1 q.2.2, q.1))   '' (f_case   ⁻¹' S)
   , (fun q : β × Unit => (EctxItem.alloc, q.1))       '' (f_alloc  ⁻¹' S)
   , (fun q : β × Unit => (EctxItem.load, q.1))        '' (f_load   ⁻¹' S)
   , (fun q : β × Val α => (EctxItem.storeL q.2, q.1)) '' (f_storeL ⁻¹' S)
   , (fun q : β × Exp α => (EctxItem.storeR q.2, q.1)) '' (f_storeR ⁻¹' S)
   , (fun q : β × Unit => (EctxItem.tape, q.1))        '' (f_tape   ⁻¹' S)
   , (fun q : β × Val α => (EctxItem.randL q.2, q.1))  '' (f_randL  ⁻¹' S)
   , (fun q : β × Exp α => (EctxItem.randR q.2, q.1))  '' (f_randR  ⁻¹' S)
   , (fun q : β × Pat α => (EctxItem.scrut q.2, q.1))  '' (f_scrut  ⁻¹' S) ]

/-- Joint preimage decomposition for `EctxItem.casesOn` with a `β` parameter. -/
theorem casesOn_preimage_decomp_param
    {α : Type _} {β γ : Type _} (S : Set γ)
    (f_appL : β × Val α → γ) (f_appR : β × Exp α → γ) (f_unop : β × UnOp → γ)
    (f_binopL : β × BinOp × Val α → γ) (f_binopR : β × BinOp × Exp α → γ)
    (f_condC : β × Exp α × Exp α → γ)
    (f_pairL : β × Val α → γ) (f_pairR : β × Exp α → γ)
    (f_fst : β × Unit → γ) (f_snd : β × Unit → γ)
    (f_inl : β × Unit → γ) (f_inr : β × Unit → γ)
    (f_case : β × Exp α × Exp α → γ)
    (f_alloc : β × Unit → γ) (f_load : β × Unit → γ)
    (f_storeL : β × Val α → γ) (f_storeR : β × Exp α → γ)
    (f_tape : β × Unit → γ)
    (f_randL : β × Val α → γ) (f_randR : β × Exp α → γ)
    (f_scrut : β × Pat α → γ) :
    (fun p : EctxItem α × β => EctxItem.casesOn (motive := fun _ => γ) p.1
        (fun v => f_appL (p.2, v)) (fun e => f_appR (p.2, e))
        (fun u => f_unop (p.2, u))
        (fun op v => f_binopL (p.2, op, v))
        (fun op e => f_binopR (p.2, op, e))
        (fun e₁ e₂ => f_condC (p.2, e₁, e₂))
        (fun v => f_pairL (p.2, v)) (fun e => f_pairR (p.2, e))
        (f_fst (p.2, ())) (f_snd (p.2, ()))
        (f_inl (p.2, ())) (f_inr (p.2, ()))
        (fun e₁ e₂ => f_case (p.2, e₁, e₂))
        (f_alloc (p.2, ())) (f_load (p.2, ()))
        (fun v => f_storeL (p.2, v)) (fun e => f_storeR (p.2, e))
        (f_tape (p.2, ()))
        (fun v => f_randL (p.2, v)) (fun e => f_randR (p.2, e))
        (fun pat => f_scrut (p.2, pat))) ⁻¹' S
      = ⋃ i, decompCell_param S f_appL f_appR f_unop f_binopL f_binopR f_condC
          f_pairL f_pairR f_fst f_snd f_inl f_inr f_case f_alloc f_load
          f_storeL f_storeR f_tape f_randL f_randR f_scrut i := by
  ext ⟨K, x⟩
  simp only [Set.mem_preimage, Set.mem_iUnion, decompCell_param]
  constructor
  · intro hK; cases K
    · exact ⟨0, (x, _), hK, rfl⟩
    · exact ⟨1, (x, _), hK, rfl⟩
    · exact ⟨2, (x, _), hK, rfl⟩
    · exact ⟨3, (x, _, _), hK, rfl⟩
    · exact ⟨4, (x, _, _), hK, rfl⟩
    · exact ⟨5, (x, _, _), hK, rfl⟩
    · exact ⟨6, (x, _), hK, rfl⟩
    · exact ⟨7, (x, _), hK, rfl⟩
    · exact ⟨8, (x, ()), hK, rfl⟩
    · exact ⟨9, (x, ()), hK, rfl⟩
    · exact ⟨10, (x, ()), hK, rfl⟩
    · exact ⟨11, (x, ()), hK, rfl⟩
    · exact ⟨12, (x, _, _), hK, rfl⟩
    · exact ⟨13, (x, ()), hK, rfl⟩
    · exact ⟨14, (x, ()), hK, rfl⟩
    · exact ⟨15, (x, _), hK, rfl⟩
    · exact ⟨16, (x, _), hK, rfl⟩
    · exact ⟨17, (x, ()), hK, rfl⟩
    · exact ⟨18, (x, _), hK, rfl⟩
    · exact ⟨19, (x, _), hK, rfl⟩
    · exact ⟨20, (x, _), hK, rfl⟩
  · rintro ⟨i, hi⟩; fin_cases i <;>
      · obtain ⟨q, hq, hp⟩ := hi; cases hp; simpa using hq

/-- Joint param version of `EctxItem.measurable_rec`. -/
@[fun_prop]
theorem measurable_rec_param
    {α : Type _} [MeasurableSpace α]
    {β : Type _} [MeasurableSpace β]
    {γ : Type _} [MeasurableSpace γ]
    (f_appL : β × Val α → γ) (f_appR : β × Exp α → γ) (f_unop : β × UnOp → γ)
    (f_binopL : β × BinOp × Val α → γ) (f_binopR : β × BinOp × Exp α → γ)
    (f_condC : β × Exp α × Exp α → γ)
    (f_pairL : β × Val α → γ) (f_pairR : β × Exp α → γ)
    (f_fst : β × Unit → γ) (f_snd : β × Unit → γ)
    (f_inl : β × Unit → γ) (f_inr : β × Unit → γ)
    (f_case : β × Exp α × Exp α → γ)
    (f_alloc : β × Unit → γ) (f_load : β × Unit → γ)
    (f_storeL : β × Val α → γ) (f_storeR : β × Exp α → γ)
    (f_tape : β × Unit → γ)
    (f_randL : β × Val α → γ) (f_randR : β × Exp α → γ)
    (f_scrut : β × Pat α → γ)
    (h_appL : Measurable f_appL) (h_appR : Measurable f_appR)
    (h_unop : Measurable f_unop)
    (h_binopL : Measurable f_binopL) (h_binopR : Measurable f_binopR)
    (h_condC : Measurable f_condC)
    (h_pairL : Measurable f_pairL) (h_pairR : Measurable f_pairR)
    (h_fst : Measurable f_fst) (h_snd : Measurable f_snd)
    (h_inl : Measurable f_inl) (h_inr : Measurable f_inr)
    (h_case : Measurable f_case)
    (h_alloc : Measurable f_alloc) (h_load : Measurable f_load)
    (h_storeL : Measurable f_storeL) (h_storeR : Measurable f_storeR)
    (h_tape : Measurable f_tape)
    (h_randL : Measurable f_randL) (h_randR : Measurable f_randR)
    (h_scrut : Measurable f_scrut) :
    Measurable (fun p : EctxItem α × β => EctxItem.casesOn (motive := fun _ => γ) p.1
        (fun v => f_appL (p.2, v)) (fun e => f_appR (p.2, e))
        (fun u => f_unop (p.2, u))
        (fun op v => f_binopL (p.2, op, v))
        (fun op e => f_binopR (p.2, op, e))
        (fun e₁ e₂ => f_condC (p.2, e₁, e₂))
        (fun v => f_pairL (p.2, v)) (fun e => f_pairR (p.2, e))
        (f_fst (p.2, ())) (f_snd (p.2, ()))
        (f_inl (p.2, ())) (f_inr (p.2, ()))
        (fun e₁ e₂ => f_case (p.2, e₁, e₂))
        (f_alloc (p.2, ())) (f_load (p.2, ()))
        (fun v => f_storeL (p.2, v)) (fun e => f_storeR (p.2, e))
        (f_tape (p.2, ()))
        (fun v => f_randL (p.2, v)) (fun e => f_randR (p.2, e))
        (fun pat => f_scrut (p.2, pat))) := by
  intro S hS
  rw [casesOn_preimage_decomp_param]
  refine .iUnion fun i => ?_
  fin_cases i
  · exact ((appL.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_appL hS)
  · exact ((appR.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_appR hS)
  · exact ((unop.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_unop hS)
  · exact ((binopL.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_binopL hS)
  · exact ((binopR.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_binopR hS)
  · exact ((condC.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_condC hS)
  · exact ((pairL.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_pairL hS)
  · exact ((pairR.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_pairR hS)
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
  · exact ((storeL.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_storeL hS)
  · exact ((storeR.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_storeR hS)
  · exact ((tape.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_tape hS)
  · exact ((randL.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_randL hS)
  · exact ((randR.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_randR hS)
  · exact ((scrut.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_scrut hS)

/-! ### Synthetic smoke-test battery

`EctxItem` is non-recursive, so there is no struct-rec keystone; the battery is
phrased through the `casesOn` keystones `measurable_rec` / `measurable_rec_param`,
modelled on `BaseLit.lean`. Each test exercises all 21 constructor slots. -/

/-- Test 1: discrete codomain (`tagDepth : EctxItem α → Nat`, one tag per constructor;
ignores all payloads). -/
@[simp] def tagDepth : EctxItem α → Nat
  | .appL _    => 0
  | .appR _    => 1
  | .unop _    => 2
  | .binopL _ _ => 3
  | .binopR _ _ => 4
  | .condC _ _ => 5
  | .pairL _   => 6
  | .pairR _   => 7
  | .fst       => 8
  | .snd       => 9
  | .inl       => 10
  | .inr       => 11
  | .case _ _  => 12
  | .alloc     => 13
  | .load      => 14
  | .storeL _  => 15
  | .storeR _  => 16
  | .tape      => 17
  | .randL _   => 18
  | .randR _   => 19
  | .scrut _   => 20

theorem tagDepth.measurable [MeasurableSpace α] :
    Measurable (tagDepth : EctxItem α → Nat) := by
  have heq : (tagDepth : EctxItem α → Nat)
    = (fun K : EctxItem α => EctxItem.casesOn (motive := fun _ => Nat) K
        (fun _ => 0) (fun _ => 1) (fun _ => 2)
        (fun _ _ => 3) (fun _ _ => 4) (fun _ _ => 5)
        (fun _ => 6) (fun _ => 7)
        8 9 10 11 (fun _ _ => 12) 13 14
        (fun _ => 15) (fun _ => 16) 17 (fun _ => 18) (fun _ => 19) (fun _ => 20)) := by
    funext K; cases K <;> rfl
  rw [heq]
  apply measurable_rec
    (f_appL := fun _ => 0) (f_appR := fun _ => 1) (f_unop := fun _ => 2)
    (f_binopL := fun _ => 3) (f_binopR := fun _ => 4) (f_condC := fun _ => 5)
    (f_pairL := fun _ => 6) (f_pairR := fun _ => 7)
    (f_fst := fun _ => 8) (f_snd := fun _ => 9) (f_inl := fun _ => 10) (f_inr := fun _ => 11)
    (f_case := fun _ => 12) (f_alloc := fun _ => 13) (f_load := fun _ => 14)
    (f_storeL := fun _ => 15) (f_storeR := fun _ => 16) (f_tape := fun _ => 17)
    (f_randL := fun _ => 18) (f_randR := fun _ => 19) (f_scrut := fun _ => 20)
  all_goals fun_prop

/-- Test 2: data-leaf dependent (`countLeaves : EctxItem α → Nat`, returns 1 for the
constructors that carry a payload and 0 for the nullary ones). -/
@[simp] def countLeaves : EctxItem α → Nat
  | .appL _    => 1
  | .appR _    => 1
  | .unop _    => 1
  | .binopL _ _ => 1
  | .binopR _ _ => 1
  | .condC _ _ => 1
  | .pairL _   => 1
  | .pairR _   => 1
  | .fst       => 0
  | .snd       => 0
  | .inl       => 0
  | .inr       => 0
  | .case _ _  => 1
  | .alloc     => 0
  | .load      => 0
  | .storeL _  => 1
  | .storeR _  => 1
  | .tape      => 0
  | .randL _   => 1
  | .randR _   => 1
  | .scrut _   => 1

theorem countLeaves.measurable [MeasurableSpace α] :
    Measurable (countLeaves : EctxItem α → Nat) := by
  have heq : (countLeaves : EctxItem α → Nat)
    = (fun K : EctxItem α => EctxItem.casesOn (motive := fun _ => Nat) K
        (fun _ => 1) (fun _ => 1) (fun _ => 1)
        (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1)
        (fun _ => 1) (fun _ => 1)
        0 0 0 0 (fun _ _ => 1) 0 0
        (fun _ => 1) (fun _ => 1) 0 (fun _ => 1) (fun _ => 1) (fun _ => 1)) := by
    funext K; cases K <;> rfl
  rw [heq]
  apply measurable_rec
    (f_appL := fun _ => 1) (f_appR := fun _ => 1) (f_unop := fun _ => 1)
    (f_binopL := fun _ => 1) (f_binopR := fun _ => 1) (f_condC := fun _ => 1)
    (f_pairL := fun _ => 1) (f_pairR := fun _ => 1)
    (f_fst := fun _ => 0) (f_snd := fun _ => 0) (f_inl := fun _ => 0) (f_inr := fun _ => 0)
    (f_case := fun _ => 1) (f_alloc := fun _ => 0) (f_load := fun _ => 0)
    (f_storeL := fun _ => 1) (f_storeR := fun _ => 1) (f_tape := fun _ => 0)
    (f_randL := fun _ => 1) (f_randR := fun _ => 1) (f_scrut := fun _ => 1)
  all_goals fun_prop

/-- Test 3: endo-map (`endoMap : EctxItem α → EctxItem α`, non-discrete codomain). The
`appR` branch genuinely transforms its `Exp α` data leaf through the measurable map
`Exp.fst`, so the obligation closes through `Exp.fst.measurable` composed with the
`appR` embedding; all other constructors are relabelled to themselves. -/
@[simp] def endoMap : EctxItem α → EctxItem α
  | .appL v    => .appL v
  | .appR e    => .appR (Exp.fst e)
  | .unop u    => .unop u
  | .binopL op v => .binopL op v
  | .binopR op e => .binopR op e
  | .condC e1 e2 => .condC e1 e2
  | .pairL v   => .pairL v
  | .pairR e   => .pairR e
  | .fst       => .fst
  | .snd       => .snd
  | .inl       => .inl
  | .inr       => .inr
  | .case e1 e2 => .case e1 e2
  | .alloc     => .alloc
  | .load      => .load
  | .storeL v  => .storeL v
  | .storeR e  => .storeR e
  | .tape      => .tape
  | .randL v   => .randL v
  | .randR e   => .randR e
  | .scrut p   => .scrut p

theorem endoMap.measurable [MeasurableSpace α] :
    Measurable (endoMap : EctxItem α → EctxItem α) := by
  have heq : (endoMap : EctxItem α → EctxItem α)
    = (fun K : EctxItem α => EctxItem.casesOn (motive := fun _ => EctxItem α) K
        EctxItem.appL (fun e => EctxItem.appR (Exp.fst e)) EctxItem.unop
        EctxItem.binopL EctxItem.binopR EctxItem.condC
        EctxItem.pairL EctxItem.pairR
        EctxItem.fst EctxItem.snd EctxItem.inl EctxItem.inr
        EctxItem.case EctxItem.alloc EctxItem.load
        EctxItem.storeL EctxItem.storeR EctxItem.tape
        EctxItem.randL EctxItem.randR EctxItem.scrut) := by
    funext K; cases K <;> rfl
  rw [heq]
  apply measurable_rec
    (f_appL := EctxItem.appL) (f_appR := fun e => EctxItem.appR (Exp.fst e))
    (f_unop := EctxItem.unop)
    (f_binopL := fun q : BinOp × Val α => EctxItem.binopL q.1 q.2)
    (f_binopR := fun q : BinOp × Exp α => EctxItem.binopR q.1 q.2)
    (f_condC := fun q : Exp α × Exp α => EctxItem.condC q.1 q.2)
    (f_pairL := EctxItem.pairL) (f_pairR := EctxItem.pairR)
    (f_fst := fun _ => EctxItem.fst) (f_snd := fun _ => EctxItem.snd)
    (f_inl := fun _ => EctxItem.inl) (f_inr := fun _ => EctxItem.inr)
    (f_case := fun q : Exp α × Exp α => EctxItem.case q.1 q.2)
    (f_alloc := fun _ => EctxItem.alloc) (f_load := fun _ => EctxItem.load)
    (f_storeL := EctxItem.storeL) (f_storeR := EctxItem.storeR)
    (f_tape := fun _ => EctxItem.tape)
    (f_randL := EctxItem.randL) (f_randR := EctxItem.randR)
    (f_scrut := EctxItem.scrut)
  all_goals fun_prop

/-- Test 4: param-threaded (`addAcc : Nat → EctxItem α → Nat`, a `Nat` accumulator carried
alongside via `measurable_rec_param`). -/
@[simp] def addAcc : Nat → EctxItem α → Nat
  | acc, .appL _    => acc + 1
  | acc, .appR _    => acc + 1
  | acc, _          => acc

theorem addAcc.measurable [MeasurableSpace α] :
    Measurable (fun p : EctxItem α × Nat => addAcc p.2 p.1) := by
  have heq : (fun p : EctxItem α × Nat => addAcc p.2 p.1)
    = (fun p : EctxItem α × Nat => EctxItem.casesOn (motive := fun _ => Nat) p.1
        (fun v => (fun q : Nat × Val α => q.1 + 1) (p.2, v))
        (fun e => (fun q : Nat × Exp α => q.1 + 1) (p.2, e))
        (fun u => (fun q : Nat × UnOp => q.1) (p.2, u))
        (fun op v => (fun q : Nat × BinOp × Val α => q.1) (p.2, op, v))
        (fun op e => (fun q : Nat × BinOp × Exp α => q.1) (p.2, op, e))
        (fun e₁ e₂ => (fun q : Nat × Exp α × Exp α => q.1) (p.2, e₁, e₂))
        (fun v => (fun q : Nat × Val α => q.1) (p.2, v))
        (fun e => (fun q : Nat × Exp α => q.1) (p.2, e))
        ((fun q : Nat × Unit => q.1) (p.2, ())) ((fun q : Nat × Unit => q.1) (p.2, ()))
        ((fun q : Nat × Unit => q.1) (p.2, ())) ((fun q : Nat × Unit => q.1) (p.2, ()))
        (fun e₁ e₂ => (fun q : Nat × Exp α × Exp α => q.1) (p.2, e₁, e₂))
        ((fun q : Nat × Unit => q.1) (p.2, ())) ((fun q : Nat × Unit => q.1) (p.2, ()))
        (fun v => (fun q : Nat × Val α => q.1) (p.2, v))
        (fun e => (fun q : Nat × Exp α => q.1) (p.2, e))
        ((fun q : Nat × Unit => q.1) (p.2, ()))
        (fun v => (fun q : Nat × Val α => q.1) (p.2, v))
        (fun e => (fun q : Nat × Exp α => q.1) (p.2, e))
        (fun pat => (fun q : Nat × Pat α => q.1) (p.2, pat))) := by
    funext p; obtain ⟨K, x⟩ := p; cases K <;> rfl
  rw [heq]
  apply measurable_rec_param
    (f_appL := fun q : Nat × Val α => q.1 + 1) (f_appR := fun q : Nat × Exp α => q.1 + 1)
    (f_unop := fun q : Nat × UnOp => q.1)
    (f_binopL := fun q : Nat × BinOp × Val α => q.1)
    (f_binopR := fun q : Nat × BinOp × Exp α => q.1)
    (f_condC := fun q : Nat × Exp α × Exp α => q.1)
    (f_pairL := fun q : Nat × Val α => q.1) (f_pairR := fun q : Nat × Exp α => q.1)
    (f_fst := fun q : Nat × Unit => q.1) (f_snd := fun q : Nat × Unit => q.1)
    (f_inl := fun q : Nat × Unit => q.1) (f_inr := fun q : Nat × Unit => q.1)
    (f_case := fun q : Nat × Exp α × Exp α => q.1)
    (f_alloc := fun q : Nat × Unit => q.1) (f_load := fun q : Nat × Unit => q.1)
    (f_storeL := fun q : Nat × Val α => q.1) (f_storeR := fun q : Nat × Exp α => q.1)
    (f_tape := fun q : Nat × Unit => q.1)
    (f_randL := fun q : Nat × Val α => q.1) (f_randR := fun q : Nat × Exp α => q.1)
    (f_scrut := fun q : Nat × Pat α => q.1)
  all_goals fun_prop

/-! ### Singleton-class for `EctxItem α` (lifted from `MeasurableSingletonClass α`).

Was previously in `Discrete.lean`; moved here so every stamped file carries its own
singleton section (matching `BaseLit.lean`/`Pat.lean`/`Exp.lean`). -/

@[simp] def singletonCyl {α : Type _} : EctxItem α → Cylinder α
  | .appL v        => .appL {v}
  | .appR e        => .appR {e}
  | .unop u        => .unop u
  | .binopL op v   => .binopL op {v}
  | .binopR op e   => .binopR op {e}
  | .condC e1 e2   => .condC {e1} {e2}
  | .pairL v       => .pairL {v}
  | .pairR e       => .pairR {e}
  | .fst           => .fst
  | .snd           => .snd
  | .inl           => .inl
  | .inr           => .inr
  | .case e1 e2    => .case {e1} {e2}
  | .alloc         => .alloc
  | .load          => .load
  | .storeL v      => .storeL {v}
  | .storeR e      => .storeR {e}
  | .tape          => .tape
  | .randL v       => .randL {v}
  | .randR e       => .randR {e}
  | .scrut p       => .scrut {p}

theorem singletonCyl_flatten {α : Type _} (i : EctxItem α) :
    (singletonCyl i).flatten = {i} := by
  cases i <;> simp

theorem singletonCyl_hasMeasurableLeaves
    {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α] (i : EctxItem α) :
    (singletonCyl i).HasMeasurableLeaves := by
  cases i
  case appL v   => exact .appL _ (MeasurableSet.singleton v)
  case appR e   => exact .appR _ (MeasurableSet.singleton e)
  case unop u   => exact .unop
  case binopL op v => exact .binopL _ (MeasurableSet.singleton v)
  case binopR op e => exact .binopR _ (MeasurableSet.singleton e)
  case condC e1 e2 => exact .condC _ _ (MeasurableSet.singleton e1) (MeasurableSet.singleton e2)
  case pairL v  => exact .pairL _ (MeasurableSet.singleton v)
  case pairR e  => exact .pairR _ (MeasurableSet.singleton e)
  case fst => exact .fst
  case snd => exact .snd
  case inl => exact .inl
  case inr => exact .inr
  case case e1 e2 => exact .case _ _ (MeasurableSet.singleton e1) (MeasurableSet.singleton e2)
  case alloc => exact .alloc
  case load => exact .load
  case storeL v => exact .storeL _ (MeasurableSet.singleton v)
  case storeR e => exact .storeR _ (MeasurableSet.singleton e)
  case tape => exact .tape
  case randL v => exact .randL _ (MeasurableSet.singleton v)
  case randR e => exact .randR _ (MeasurableSet.singleton e)
  case scrut p => exact .scrut _ (MeasurableSet.singleton p)

instance instMeasurableSingletonClass
    {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (EctxItem α) where
  measurableSet_singleton i := by
    rw [← singletonCyl_flatten i]
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨singletonCyl i, singletonCyl_hasMeasurableLeaves i, rfl⟩

