module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.BaseLit
public import Metrology.ProbLang.CoreMeasures.Stamp

meta import Metrology.Meta

@[expose] public section

/-! # `StampTest`: a deliberately nasty toy type for validating `STAMPING.md`.

`Probe rT` exercises the *whole* classification vocabulary in one type:
- `nil`               — nullary
- `tag (n : Nat)`     — pure syntax leaf (countable + discrete)
- `dat (b : BaseLit rT)` — pure data leaf (reuses `BaseLit`'s measurable space)
- `box (p)`           — unary recursive
- `pr  (p1 p2)`       — binary recursive
- `tri (p1 p2 p3)`    — ternary recursive
- `mix (op : UnOp) (p)` — syntax-leaf × recursive (unop-like)
- `scr (p) (b : BaseLit rT)` — recursive × foreign data leaf (scrut-like)
- `quad (p1 p2 p3 p4)` — 4-ary recursive (exceeds cell stock; forces §21)

This file is stamped following `STAMPING.md` ONLY. -/

noncomputable section ProbLangMeasures

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace ProbLang.StampTest

@[uncurriedProjections, curriedProjections, constructors]
inductive Probe (rT : Type _)
  | nil
  | tag  (n : Nat)
  | dat  (b : BaseLit rT)
  | box  (p : Probe rT)
  | pr   (p1 p2 : Probe rT)
  | tri  (p1 p2 p3 : Probe rT)
  | mix  (op : UnOp) (p : Probe rT)
  | scr  (p : Probe rT) (b : BaseLit rT)
  | quad (p1 p2 p3 p4 : Probe rT)
  deriving Inhabited

/-! ### §1 injectivity -/

theorem nil.ι.inj {rT : Type _} : Function.Injective (@Probe.nil.ι rT) := by solve_ι_inj
theorem tag.ι.inj {rT : Type _} : Function.Injective (@Probe.tag.ι rT) := by solve_ι_inj
theorem dat.ι.inj {rT : Type _} : Function.Injective (@Probe.dat.ι rT) := by solve_ι_inj
theorem box.ι.inj {rT : Type _} : Function.Injective (@Probe.box.ι rT) := by solve_ι_inj
theorem pr.ι.inj {rT : Type _} : Function.Injective (@Probe.pr.ι rT) := by solve_ι_inj
theorem tri.ι.inj {rT : Type _} : Function.Injective (@Probe.tri.ι rT) := by solve_ι_inj
theorem mix.ι.inj {rT : Type _} : Function.Injective (@Probe.mix.ι rT) := by solve_ι_inj
theorem scr.ι.inj {rT : Type _} : Function.Injective (@Probe.scr.ι rT) := by solve_ι_inj
theorem quad.ι.inj {rT : Type _} : Function.Injective (@Probe.quad.ι rT) := by solve_ι_inj

/-! ### §2–§3 Cylinder and Shape -/

inductive Cylinder (rT : Type _)
  | nil
  | tag  (n : Nat)
  | dat  (S : Set (BaseLit rT))
  | box  (c : Cylinder rT)
  | pr   (c1 c2 : Cylinder rT)
  | tri  (c1 c2 c3 : Cylinder rT)
  | mix  (op : UnOp) (c : Cylinder rT)
  | scr  (c : Cylinder rT) (S : Set (BaseLit rT))
  | quad (c1 c2 c3 c4 : Cylinder rT)

inductive Shape
  | nil
  | tag  (n : Nat)
  | dat
  | box  (s : Shape)
  | pr   (s1 s2 : Shape)
  | tri  (s1 s2 s3 : Shape)
  | mix  (op : UnOp) (s : Shape)
  | scr  (s : Shape)
  | quad (s1 s2 s3 s4 : Shape)
  deriving Countable

/-! ### §4 flatten -/

@[simp, stamp_simp] def Cylinder.flatten {rT : Type _} : Cylinder rT → Set (Probe rT)
  | .nil          => {Probe.nil}
  | .tag n        => {Probe.tag n}
  | .dat S        => Probe.dat '' S
  | .box c        => Probe.box '' flatten c
  | .pr c1 c2     => (fun p => Probe.pr p.1 p.2) '' (flatten c1 ×ˢ flatten c2)
  | .tri c1 c2 c3 =>
      (fun p : Probe rT × Probe rT × Probe rT => Probe.tri p.1 p.2.1 p.2.2) ''
        (flatten c1 ×ˢ flatten c2 ×ˢ flatten c3)
  | .mix op c     => Probe.mix op '' flatten c
  | .scr c S      => (fun p => Probe.scr p.1 p.2) '' (flatten c ×ˢ S)
  | .quad c1 c2 c3 c4 =>
      (fun p : Probe rT × Probe rT × Probe rT × Probe rT =>
        Probe.quad p.1 p.2.1 p.2.2.1 p.2.2.2) ''
        (flatten c1 ×ˢ flatten c2 ×ˢ flatten c3 ×ˢ flatten c4)

/-! ### §5 HasMeasurableLeaves -/

inductive Cylinder.HasMeasurableLeaves {rT : Type _} [MeasurableSpace rT] :
    Cylinder rT → Prop where
  | nil  : HasMeasurableLeaves .nil
  | tag  : HasMeasurableLeaves (.tag n)
  | dat S : MeasurableSet S → HasMeasurableLeaves (.dat S)
  | box  : HasMeasurableLeaves c → HasMeasurableLeaves (.box c)
  | pr   : HasMeasurableLeaves c1 → HasMeasurableLeaves c2 → HasMeasurableLeaves (.pr c1 c2)
  | tri  : HasMeasurableLeaves c1 → HasMeasurableLeaves c2 → HasMeasurableLeaves c3 →
            HasMeasurableLeaves (.tri c1 c2 c3)
  | mix  : HasMeasurableLeaves c → HasMeasurableLeaves (.mix op c)
  | scr S : HasMeasurableLeaves c → MeasurableSet S → HasMeasurableLeaves (.scr c S)
  | quad : HasMeasurableLeaves c1 → HasMeasurableLeaves c2 → HasMeasurableLeaves c3 →
            HasMeasurableLeaves c4 → HasMeasurableLeaves (.quad c1 c2 c3 c4)

/-! ### §6 σ-algebra instance -/

instance instMeasurableSpaceProbe [MeasurableSpace rT] : MeasurableSpace (Probe rT) :=
  .generateFrom <| Cylinder.flatten '' { c : Cylinder rT | c.HasMeasurableLeaves }

/-! ### §7 shape maps -/

@[simp, stamp_simp] def Probe.shape : Probe rT → Shape
  | .nil          => .nil
  | .tag n        => .tag n
  | .dat _        => .dat
  | .box p        => .box (shape p)
  | .pr p1 p2     => .pr (shape p1) (shape p2)
  | .tri p1 p2 p3 => .tri (shape p1) (shape p2) (shape p3)
  | .mix op p     => .mix op (shape p)
  | .scr p _      => .scr (shape p)
  | .quad p1 p2 p3 p4 => .quad (shape p1) (shape p2) (shape p3) (shape p4)

@[simp, stamp_simp] def Cylinder.shape {rT : Type _} : Cylinder rT → Shape
  | .nil          => .nil
  | .tag n        => .tag n
  | .dat _        => .dat
  | .box c        => .box (shape c)
  | .pr c1 c2     => .pr (shape c1) (shape c2)
  | .tri c1 c2 c3 => .tri (shape c1) (shape c2) (shape c3)
  | .mix op c     => .mix op (shape c)
  | .scr c _      => .scr (shape c)
  | .quad c1 c2 c3 c4 => .quad (shape c1) (shape c2) (shape c3) (shape c4)

@[simp, stamp_simp] def Shape.cylinder {rT : Type _} : Shape → Cylinder rT
  | .nil          => .nil
  | .tag n        => .tag n
  | .dat          => .dat Set.univ
  | .box s        => .box (cylinder s)
  | .pr s1 s2     => .pr (cylinder s1) (cylinder s2)
  | .tri s1 s2 s3 => .tri (cylinder s1) (cylinder s2) (cylinder s3)
  | .mix op s     => .mix op (cylinder s)
  | .scr s        => .scr (cylinder s) Set.univ
  | .quad s1 s2 s3 s4 => .quad (cylinder s1) (cylinder s2) (cylinder s3) (cylinder s4)

/-! ### §8 inter? -/

def Cylinder.inter? {rT : Type _} : Cylinder rT → Cylinder rT → Option (Cylinder rT)
  | .nil, .nil       => some .nil
  | .tag a, .tag b   => if a = b then some (.tag a) else none
  | .dat S₁, .dat S₂ => some (.dat (S₁ ∩ S₂))
  | .box c, .box c'  =>
      match Cylinder.inter? c c' with
      | some r => some (.box r)
      | none   => none
  | .pr a b, .pr a' b' =>
      match Cylinder.inter? a a', Cylinder.inter? b b' with
      | some r₁, some r₂ => some (.pr r₁ r₂)
      | _, _ => none
  | .tri a b d, .tri a' b' d' =>
      match Cylinder.inter? a a', Cylinder.inter? b b', Cylinder.inter? d d' with
      | some r₁, some r₂, some r₃ => some (.tri r₁ r₂ r₃)
      | _, _, _ => none
  | .mix u c, .mix u' c' =>
      if u = u' then
        match Cylinder.inter? c c' with
        | some r => some (.mix u r)
        | none   => none
      else none
  | .scr c S, .scr c' S' =>
      match Cylinder.inter? c c' with
      | some r => some (.scr r (S ∩ S'))
      | none   => none
  | .quad a b d e, .quad a' b' d' e' =>
      match Cylinder.inter? a a', Cylinder.inter? b b', Cylinder.inter? d d', Cylinder.inter? e e' with
      | some r₁, some r₂, some r₃, some r₄ => some (.quad r₁ r₂ r₃ r₄)
      | _, _, _, _ => none
  | _, _ => none

/-! ### §9 shape_of_mem_flatten -/

theorem Cylinder.shape_of_mem_flatten {rT : Type _} {c : Cylinder rT} {p : Probe rT}
    (h : p ∈ Cylinder.flatten c) : Probe.shape p = Cylinder.shape c := by
  induction c generalizing p with
  | nil | tag _ => simp_all
  | dat _ => obtain ⟨_, _, rfl⟩ := h; rfl
  | box c ih => obtain ⟨x, hx, rfl⟩ := h; show Probe.shape (Probe.box x) = _; simp [Probe.shape, ih hx]
  | pr c₁ c₂ ih₁ ih₂ =>
    obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩ := h
    show Probe.shape (Probe.pr x y) = _; simp [Probe.shape, ih₁ hx, ih₂ hy]
  | tri c₁ c₂ c₃ ih₁ ih₂ ih₃ =>
    obtain ⟨⟨x, y, z⟩, ⟨hx, hy, hz⟩, rfl⟩ := h
    show Probe.shape (Probe.tri x y z) = _; simp [Probe.shape, ih₁ hx, ih₂ hy, ih₃ hz]
  | mix u c ih =>
    obtain ⟨x, hx, rfl⟩ := h; show Probe.shape (Probe.mix u x) = _; simp [Probe.shape, ih hx]
  | scr c S ih =>
    obtain ⟨⟨x, y⟩, ⟨hx, _⟩, rfl⟩ := h
    show Probe.shape (Probe.scr x y) = _; simp [Probe.shape, ih hx]
  | quad c₁ c₂ c₃ c₄ ih₁ ih₂ ih₃ ih₄ =>
    obtain ⟨⟨w, x, y, z⟩, ⟨hw, hx, hy, hz⟩, rfl⟩ := h
    show Probe.shape (Probe.quad w x y z) = _; simp [Probe.shape, ih₁ hw, ih₂ hx, ih₃ hy, ih₄ hz]

/-! ### §10 flatten_disjoint_of_shape_ne -/

theorem Cylinder.flatten_disjoint_of_shape_ne {rT : Type _} {c₁ c₂ : Cylinder rT}
    (h : Cylinder.shape c₁ ≠ Cylinder.shape c₂) :
    Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ = ∅ :=
  Stamp.flatten_disjoint_of_shape_ne (cShape := Cylinder.shape)
    (fun {_ _} h => Cylinder.shape_of_mem_flatten h) h

/-! ### §11 flatten_inter -/

theorem Cylinder.flatten_inter {rT : Type _} (c₁ c₂ : Cylinder rT) :
    Cylinder.flatten c₁ ∩ Cylinder.flatten c₂
      = (Cylinder.inter? c₁ c₂).elim ∅ Cylinder.flatten := by
  induction c₁ generalizing c₂ with
  | nil =>
    cases c₂
    case nil => simp [Cylinder.inter?]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | tag x₁ =>
    cases c₂
    case tag x₂ => simp [Cylinder.inter?]; split_ifs <;> simp_all
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | dat S₁ =>
    cases c₂
    case dat S₂ =>
      simp only [Cylinder.flatten, Cylinder.inter?, Option.elim]
      exact Stamp.flatten_inter_data dat.ι.inj
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | box c ih =>
    cases c₂
    case box c' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_image₁ box.ι.inj Cylinder.box (fun _ => rfl) (ih c')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? c c' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | pr a b ih₁ ih₂ =>
    cases c₂
    case pr a' b' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_image₂ pr.ι.inj Cylinder.pr (fun _ _ => rfl)
        (ih₁ a') (ih₂ b')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? a a' <;> cases Cylinder.inter? b b' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | tri c₁ c₂ c₃ ih₁ ih₂ ih₃ =>
    cases c₂
    case tri c₁' c₂' c₃' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_image₃ tri.ι.inj Cylinder.tri (fun _ _ _ => rfl)
        (ih₁ c₁') (ih₂ c₂') (ih₃ c₃')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? c₁ c₁' <;> cases Cylinder.inter? c₂ c₂' <;>
          cases Cylinder.inter? c₃ c₃' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | mix u c ih =>
    cases c₂
    case mix u' c' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_mixed₁ (fun _ _ _ h => by injection h)
        (fun h => by injection h) Cylinder.mix (fun _ _ => rfl) (ih c')
        (by rw [Cylinder.inter?]; split <;> [cases Cylinder.inter? c c'; skip] <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | scr c S ih =>
    cases c₂
    case scr c' S' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_scrut scr.ι.inj Cylinder.scr (fun _ _ => rfl) (ih c')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? c c' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | quad c₁ c₂ c₃ c₄ ih₁ ih₂ ih₃ ih₄ =>
    cases c₂
    case quad c₁' c₂' c₃' c₄' =>
      simp only [Cylinder.flatten]
      exact Stamp.flatten_inter_image₄ quad.ι.inj Cylinder.quad (fun _ _ _ _ => rfl)
        (ih₁ c₁') (ih₂ c₂') (ih₃ c₃') (ih₄ c₄')
        (by rw [Cylinder.inter?]; cases Cylinder.inter? c₁ c₁' <;> cases Cylinder.inter? c₂ c₂' <;>
          cases Cylinder.inter? c₃ c₃' <;> cases Cylinder.inter? c₄ c₄' <;> rfl)
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)

/-! ### §12 flatten_inter_some -/

theorem Cylinder.flatten_inter_some {rT : Type _} {c₁ c₂ c : Cylinder rT}
    (h : Cylinder.inter? c₁ c₂ = some c) :
    Cylinder.flatten c = Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ :=
  Stamp.flatten_inter_some Cylinder.flatten_inter h

/-! ### §13 hasMeasurableLeaves_inter -/

theorem Cylinder.hasMeasurableLeaves_inter [MeasurableSpace rT]
    {c₁ c₂ c : Cylinder rT}
    (h₁ : c₁.HasMeasurableLeaves) (h₂ : c₂.HasMeasurableLeaves)
    (h : Cylinder.inter? c₁ c₂ = some c) : c.HasMeasurableLeaves := by
  induction c₁ generalizing c₂ c with
  | tag | nil =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    all_goals first | (split at h <;> simp_all) | simp_all
  | dat S₁ =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    cases h₁; cases h₂; injection h with h; subst h; exact .dat _ (MeasurableSet.inter ‹_› ‹_›)
  | box c ih =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    all_goals (
      cases h₁; cases h₂
      revert h; split <;> rintro ⟨rfl⟩; rename_i ha
      exact .box (ih ‹_› ‹_› ha))
  | pr a b iha ihb =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    cases h₁; cases h₂
    revert h; split <;> rintro ⟨rfl⟩; rename_i ha hb
    exact .pr (iha ‹_› ‹_› ha) (ihb ‹_› ‹_› hb)
  | tri a b d iha ihb ihd =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    cases h₁; cases h₂
    revert h; split <;> rintro ⟨rfl⟩; rename_i ha hb hd
    exact .tri (iha ‹_› ‹_› ha) (ihb ‹_› ‹_› hb) (ihd ‹_› ‹_› hd)
  | mix u c ih =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    cases h₁; cases h₂
    revert h; split <;> [split; skip] <;> rintro ⟨rfl⟩
    rename_i ha
    exact .mix (ih ‹_› ‹_› ha)
  | scr c S ih =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    cases h₁; cases h₂
    revert h; split <;> rintro ⟨rfl⟩; rename_i ha
    exact .scr _ (ih ‹_› ‹_› ha) (MeasurableSet.inter ‹_› ‹_›)
  | quad a b d e iha ihb ihd ihe =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    cases h₁; cases h₂
    revert h; split <;> rintro ⟨rfl⟩; rename_i ha hb hd he
    exact .quad (iha ‹_› ‹_› ha) (ihb ‹_› ‹_› hb) (ihd ‹_› ‹_› hd) (ihe ‹_› ‹_› he)

/-! ### §14 per-constructor covers -/

@[stamp_simp] def cover.nil (S : Set Unit) : Set (Probe rT) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.nil : Cylinder rT)
@[stamp_simp] def cover.tag (S : Set Nat) : Set (Probe rT) :=
  ⋃ x ∈ S, Cylinder.flatten (.tag x)
@[stamp_simp] def cover.dat (S : Set (BaseLit rT)) : Set (Probe rT) :=
  Cylinder.flatten (.dat S)
@[stamp_simp] def cover.box (S : Set Shape) : Set (Probe rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.box s.cylinder)
@[stamp_simp] def cover.pr (S : Set (Shape × Shape)) : Set (Probe rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.pr p.1.cylinder p.2.cylinder)
@[stamp_simp] def cover.tri (S : Set (Shape × Shape × Shape)) : Set (Probe rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.tri p.1.cylinder p.2.1.cylinder p.2.2.cylinder)
@[stamp_simp] def cover.mix (S : Set (UnOp × Shape)) : Set (Probe rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.mix p.1 p.2.cylinder)
@[stamp_simp] def cover.scr (S : Set Shape) : Set (Probe rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.scr s.cylinder Set.univ)
@[stamp_simp] def cover.quad (S : Set (Shape × Shape × Shape × Shape)) : Set (Probe rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.quad p.1.cylinder p.2.1.cylinder p.2.2.1.cylinder p.2.2.2.cylinder)

/-! ### §15 Shape.cylinder_hasMeasurableLeaves -/

theorem Shape.cylinder_hasMeasurableLeaves [MeasurableSpace rT] (s : Shape) :
    (s.cylinder (rT := rT)).HasMeasurableLeaves := by
  induction s <;> constructor <;> measurability

/-! ### §16 Shape.cylinder_preimage_shape -/

@[simp] theorem Shape.cylinder_preimage_shape (s : Shape) :
    (s.cylinder (rT := rT)).flatten = Probe.shape ⁻¹' {s} :=
  Stamp.cylinder_preimage_shape (cShape := Cylinder.shape)
    (fun {_ _} h => Cylinder.shape_of_mem_flatten h)
    (fun s => by induction s <;> simp_all)
    (fun p => by induction p <;> simp_all) s

/-! ### §17 flatten_measurable -/

@[measurability]
theorem flatten_measurable [MeasurableSpace rT] {c : Cylinder rT}
    (hc : c.HasMeasurableLeaves) : MeasurableSet c.flatten :=
  Stamp.flatten_measurable rfl hc

/-! ### §18 aesop attributes -/

attribute [aesop safe constructors (rule_sets := [Measurable])]
  ProbLang.StampTest.Cylinder.HasMeasurableLeaves
attribute [aesop safe apply (rule_sets := [Measurable])]
  Shape.cylinder_hasMeasurableLeaves

/-! ### §19–§20 π-system + countably-spanning -/

theorem Cylinder.flatten_isPiSystem [MeasurableSpace rT] :
    IsPiSystem ({S : Set (Probe rT) | ∃ c : Cylinder rT, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S}) :=
  Stamp.flatten_isPiSystem Cylinder.flatten_inter
    (fun {_ _ _} => Cylinder.hasMeasurableLeaves_inter)

theorem Cylinder.flatten_isCountablySpanning [MeasurableSpace rT] :
    IsCountablySpanning ({S : Set (Probe rT) | ∃ c : Cylinder rT, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S}) :=
  Stamp.flatten_isCountablySpanning Shape.cylinder_hasMeasurableLeaves
    Shape.cylinder_preimage_shape .nil .nil

/-! ### §21 cover measurability -/

@[measurability] theorem cover.nil.measurable [MeasurableSpace rT] (S : Set Unit) :
    MeasurableSet (nil (rT := rT) S) := by solve_cover_measurable
@[measurability] theorem cover.tag.measurable [MeasurableSpace rT] (S : Set Nat) :
    MeasurableSet (tag (rT := rT) S) := by solve_cover_measurable
@[measurability] theorem cover.dat.measurable [MeasurableSpace rT] {S : Set (BaseLit rT)}
    (hS : MeasurableSet S) : MeasurableSet (dat (rT := rT) S) :=
  flatten_measurable (.dat _ hS)
@[measurability] theorem cover.box.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (box (rT := rT) S) := by solve_cover_measurable
@[measurability] theorem cover.pr.measurable [MeasurableSpace rT] (S : Set (Shape × Shape)) :
    MeasurableSet (pr (rT := rT) S) := by solve_cover_measurable
@[measurability] theorem cover.tri.measurable [MeasurableSpace rT] (S : Set (Shape × Shape × Shape)) :
    MeasurableSet (tri (rT := rT) S) := by solve_cover_measurable
@[measurability] theorem cover.mix.measurable [MeasurableSpace rT] (S : Set (UnOp × Shape)) :
    MeasurableSet (mix (rT := rT) S) := by solve_cover_measurable
@[measurability] theorem cover.scr.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (scr (rT := rT) S) := by solve_cover_measurable
@[measurability] theorem cover.quad.measurable [MeasurableSpace rT]
    (S : Set (Shape × Shape × Shape × Shape)) :
    MeasurableSet (quad (rT := rT) S) := by solve_cover_measurable

/-! ### §22 cover eq lemmas -/

theorem cover.nil_eq_image (S : Set Unit) :
    cover.nil (rT := rT) S = (fun _ : Unit => (Probe.nil : Probe rT)) '' S := by
  solve_cover_eq_image cover.nil
theorem cover.tag_eq_image (S : Set Nat) :
    cover.tag (rT := rT) S = Probe.tag '' S := by solve_cover_eq_image cover.tag
theorem cover.dat_eq_image (S : Set (BaseLit rT)) :
    cover.dat (rT := rT) S = Probe.dat '' S := by solve_cover_eq_image cover.dat
theorem cover.box_univ_eq_range :
    cover.box (rT := rT) Set.univ = .range (Probe.box : Probe rT → Probe rT) := by
  solve_cover_eq_image cover.box
theorem cover.pr_univ_eq_range :
    cover.pr (rT := rT) Set.univ = .range (Function.uncurry Probe.pr) := by
  solve_cover_eq_image cover.pr
theorem cover.tri_univ_eq_range :
    cover.tri (rT := rT) Set.univ
      = .range (fun p : Probe rT × Probe rT × Probe rT => Probe.tri p.1 p.2.1 p.2.2) := by
  solve_cover_eq_image cover.tri
theorem cover.mix_univ_eq_range :
    cover.mix (rT := rT) Set.univ
      = .range (fun p : UnOp × Probe rT => Probe.mix p.1 p.2) := by
  solve_cover_eq_image cover.mix
theorem cover.scr_univ_eq_range :
    cover.scr (rT := rT) Set.univ
      = .range (fun p : Probe rT × BaseLit rT => Probe.scr p.1 p.2) := by
  solve_cover_eq_image cover.scr
theorem cover.quad_univ_eq_range :
    cover.quad (rT := rT) Set.univ
      = .range (fun p : Probe rT × Probe rT × Probe rT × Probe rT =>
          Probe.quad p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  solve_cover_eq_image cover.quad

/-! ### §23 `.ι.measurable` -/

@[fun_prop] theorem nil.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (Probe.nil.ι (rT := rT)) := (by measurability)
@[fun_prop] theorem tag.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (Probe.tag.ι (rT := rT)) := (by measurability)
@[fun_prop] theorem mix.ι.measurable [MeasurableSpace rT] :
    Measurable (Probe.mix.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @mix c op h =>
    suffices heq : Probe.mix.ι ⁻¹' Cylinder.flatten (.mix op c)
                = ({op} : Set UnOp) ×ˢ Cylinder.flatten c by
      rw [heq]; exact (MeasurableSet.singleton op).prod (flatten_measurable h)
    ext ⟨u, p⟩
    simp only [Set.mem_preimage, Cylinder.flatten, Set.mem_image, Set.mem_prod,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, hh⟩; injection hh with hu hpx; subst hu; subst hpx; exact ⟨rfl, hx⟩
    · rintro ⟨rfl, hp⟩; exact ⟨p, hp, rfl⟩
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop] theorem dat.ι.measurable [MeasurableSpace rT] :
    Measurable (Probe.dat.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @dat S hS =>
    suffices h : Probe.dat.ι ⁻¹' Cylinder.flatten (.dat S) = S by rw [h]; exact hS
    ext b; simp
  | _ => convert MeasurableSet.empty; ext b; simp

@[fun_prop] theorem box.ι.measurable [MeasurableSpace rT] :
    Measurable (Probe.box.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @box c h =>
    suffices heq : Probe.box.ι ⁻¹' Cylinder.flatten (.box c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext p; simp
  | _ => convert MeasurableSet.empty; ext p; simp

@[fun_prop] theorem pr.ι.measurable [MeasurableSpace rT] :
    Measurable (Probe.pr.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @pr c1 c2 h1 h2 =>
    suffices h : Probe.pr.ι ⁻¹' Cylinder.flatten (.pr c1 c2)
                = Cylinder.flatten c1 ×ˢ Cylinder.flatten c2 by rw [h]; measurability
    ext ⟨_, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop] theorem tri.ι.measurable [MeasurableSpace rT] :
    Measurable (Probe.tri.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @tri c1 c2 c3 h1 h2 h3 =>
    suffices h : Probe.tri.ι ⁻¹' Cylinder.flatten (.tri c1 c2 c3)
                = Cylinder.flatten c1 ×ˢ Cylinder.flatten c2 ×ˢ Cylinder.flatten c3 by
      rw [h]; measurability
    ext ⟨_, _, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _, _⟩; simp

@[fun_prop] theorem scr.ι.measurable [MeasurableSpace rT] :
    Measurable (Probe.scr.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @scr c S hc hS =>
    suffices h : Probe.scr.ι ⁻¹' Cylinder.flatten (.scr c S)
                = Cylinder.flatten c ×ˢ S by rw [h]; exact (flatten_measurable hc).prod hS
    ext ⟨_, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop] theorem quad.ι.measurable [MeasurableSpace rT] :
    Measurable (Probe.quad.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @quad c1 c2 c3 c4 h1 h2 h3 h4 =>
    suffices h : Probe.quad.ι ⁻¹' Cylinder.flatten (.quad c1 c2 c3 c4)
                = Cylinder.flatten c1 ×ˢ Cylinder.flatten c2 ×ˢ Cylinder.flatten c3 ×ˢ
                    Cylinder.flatten c4 by rw [h]; measurability
    ext ⟨_, _, _, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _, _, _⟩; simp

/-! ### §24 raw-constructor relays -/

@[fun_prop] theorem nil.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (fun _ : Unit => (Probe.nil : Probe rT)) := nil.ι.measurable
@[fun_prop] theorem tag.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (Probe.tag : Nat → Probe rT) := tag.ι.measurable
@[fun_prop] theorem dat.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (Probe.dat : BaseLit rT → Probe rT) := dat.ι.measurable
@[fun_prop] theorem box.measurable [MeasurableSpace rT] :
    Measurable (Probe.box : Probe rT → Probe rT) := box.ι.measurable
@[fun_prop] theorem pr.measurable [MeasurableSpace rT] :
    Measurable (Function.uncurry (Probe.pr : Probe rT → Probe rT → Probe rT)) := pr.ι.measurable
@[fun_prop] theorem tri.measurable [MeasurableSpace rT] :
    Measurable (fun p : Probe rT × Probe rT × Probe rT => Probe.tri p.1 p.2.1 p.2.2) :=
  tri.ι.measurable
@[fun_prop] theorem mix.measurable [MeasurableSpace rT] :
    Measurable (Function.uncurry (Probe.mix : UnOp → Probe rT → Probe rT)) := mix.ι.measurable
@[fun_prop] theorem scr.measurable [MeasurableSpace rT] :
    Measurable (Function.uncurry (Probe.scr : Probe rT → BaseLit rT → Probe rT)) := scr.ι.measurable
@[fun_prop] theorem quad.measurable [MeasurableSpace rT] :
    Measurable (fun p : Probe rT × Probe rT × Probe rT × Probe rT =>
      Probe.quad p.1 p.2.1 p.2.2.1 p.2.2.2) := quad.ι.measurable

/-! ### §25 measurableEmbeddings -/

theorem nil.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (fun _ : Unit => (Probe.nil : Probe rT)) := by
  apply MeasurableEmbedding.of_measurable_inverse (g := fun _ => ())
  · exact measurable_const
  · rw [show Set.range (fun _ : Unit => (Probe.nil : Probe rT)) = cover.nil .univ from by
             rw [cover.nil_eq_image]; ext; simp]
    exact cover.nil.measurable _
  · exact measurable_const
  · intro; rfl

theorem tag.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Probe.tag : Nat → Probe rT) := by
  solve_discrete_ME cover.tag_eq_image, cover.tag.measurable

theorem dat.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Probe.dat : BaseLit rT → Probe rT) :=
  ⟨fun _ _ h => by injection h, dat.ι.measurable,
    fun _ hS => flatten_measurable (.dat _ hS)⟩

theorem box.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Probe.box : Probe rT → Probe rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := box.ι.inj) (h_meas := box.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.box hc))
    (h_cov_meas := cover.box.measurable _) (h_cov_range := cover.box_univ_eq_range)

theorem pr.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Function.uncurry (Probe.pr : Probe rT → Probe rT → Probe rT)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := pr.ι.inj) (h_meas := pr.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl rfl
                Cylinder.flatten_isCountablySpanning Cylinder.flatten_isCountablySpanning).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩; exact flatten_measurable (.pr hc₁ hc₂))
    (h_cov_meas := cover.pr.measurable _) (h_cov_range := cover.pr_univ_eq_range)

theorem tri.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (fun (p : Probe rT × Probe rT × Probe rT) => Probe.tri p.1 p.2.1 p.2.2) :=
  measurableEmbedding_of_piSystem₃
    (h_inj := tri.ι.inj) (h_meas := tri.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl
                (generateFrom_eq_prod rfl rfl
                  Cylinder.flatten_isCountablySpanning Cylinder.flatten_isCountablySpanning)
                Cylinder.flatten_isCountablySpanning
                (Cylinder.flatten_isCountablySpanning.prod Cylinder.flatten_isCountablySpanning)).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod
              (Cylinder.flatten_isPiSystem.prod Cylinder.flatten_isPiSystem))
    (h_basic := by
      rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩ _ ⟨c₃, hc₃, rfl⟩
      rw [show ((fun p : Probe rT × Probe rT × Probe rT => Probe.tri p.1 p.2.1 p.2.2)
            '' (Cylinder.flatten c₁ ×ˢ Cylinder.flatten c₂ ×ˢ Cylinder.flatten c₃))
            = Cylinder.flatten (.tri c₁ c₂ c₃) from by ext e; cases e <;> simp]
      exact flatten_measurable (.tri hc₁ hc₂ hc₃))
    (h_cov_meas := cover.tri.measurable _) (h_cov_range := cover.tri_univ_eq_range)

theorem mix.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Function.uncurry (Probe.mix : UnOp → Probe rT → Probe rT)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := mix.ι.inj) (h_meas := mix.ι.measurable)
    (h_gen := (generateFrom_eq_prod singletonsAndUniv_generateFrom rfl
                singletonsAndUniv_isCountablySpanning Cylinder.flatten_isCountablySpanning).symm)
    (h_pi := singletonsAndUniv_isPiSystem.prod Cylinder.flatten_isPiSystem)
    (h_basic := by
      rintro A hA _ ⟨c, hc, rfl⟩
      rcases hA with rfl | ⟨u, rfl⟩
      · rw [show ((Function.uncurry Probe.mix) '' (Set.univ ×ˢ Cylinder.flatten c) : Set (Probe rT))
              = ⋃ u : UnOp, Probe.mix u '' Cylinder.flatten c from by
            ext e; simp [Function.uncurry]]
        exact .iUnion fun u => flatten_measurable (.mix (op := u) hc)
      · rw [show ((Function.uncurry Probe.mix) '' (({u} : Set UnOp) ×ˢ Cylinder.flatten c) :
                Set (Probe rT))
              = Cylinder.flatten (.mix u c) from by ext e; cases e <;> simp [Function.uncurry]]
        exact flatten_measurable (.mix hc))
    (h_cov_meas := cover.mix.measurable _) (h_cov_range := cover.mix_univ_eq_range)

theorem scr.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Function.uncurry (Probe.scr : Probe rT → BaseLit rT → Probe rT)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := scr.ι.inj) (h_meas := scr.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl MeasurableSpace.generateFrom_measurableSet
                Cylinder.flatten_isCountablySpanning isCountablySpanning_measurableSet).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod
              (fun S (hS : MeasurableSet S) T (hT : MeasurableSet T) _ => hS.inter hT))
    (h_basic := by
      rintro _ ⟨c, hc, rfl⟩ S (hS : MeasurableSet S)
      rw [show ((Function.uncurry Probe.scr) '' (Cylinder.flatten c ×ˢ S) : Set (Probe rT))
            = Cylinder.flatten (.scr c S) from by ext e; cases e <;> simp [Function.uncurry]]
      exact flatten_measurable (.scr _ hc hS))
    (h_cov_meas := cover.scr.measurable _) (h_cov_range := cover.scr_univ_eq_range)

theorem quad.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (fun (p : Probe rT × Probe rT × Probe rT × Probe rT) =>
      Probe.quad p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  measurableEmbedding_of_piSystem₄
    (h_inj := quad.ι.inj) (h_meas := quad.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl
                (generateFrom_eq_prod rfl
                  (generateFrom_eq_prod rfl rfl
                    Cylinder.flatten_isCountablySpanning Cylinder.flatten_isCountablySpanning)
                  Cylinder.flatten_isCountablySpanning
                  (Cylinder.flatten_isCountablySpanning.prod Cylinder.flatten_isCountablySpanning))
                Cylinder.flatten_isCountablySpanning
                (Cylinder.flatten_isCountablySpanning.prod
                  (Cylinder.flatten_isCountablySpanning.prod
                    Cylinder.flatten_isCountablySpanning))).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod
              (Cylinder.flatten_isPiSystem.prod
                (Cylinder.flatten_isPiSystem.prod Cylinder.flatten_isPiSystem)))
    (h_basic := by
      rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩ _ ⟨c₃, hc₃, rfl⟩ _ ⟨c₄, hc₄, rfl⟩
      rw [show ((fun p : Probe rT × Probe rT × Probe rT × Probe rT =>
              Probe.quad p.1 p.2.1 p.2.2.1 p.2.2.2)
            '' (Cylinder.flatten c₁ ×ˢ Cylinder.flatten c₂ ×ˢ Cylinder.flatten c₃ ×ˢ
                Cylinder.flatten c₄))
            = Cylinder.flatten (.quad c₁ c₂ c₃ c₄) from by ext e; cases e <;> simp]
      exact flatten_measurable (.quad hc₁ hc₂ hc₃ hc₄))
    (h_cov_meas := cover.quad.measurable _) (h_cov_range := cover.quad_univ_eq_range)

/-! ### Uncurried-projection measurability (§36).

The four production CoreMeasures inductives (`BaseLit`/`Pat`/`Exp`/`EctxItem`) stamp one
`<ctor>.π.measurable` per field-carrying constructor via `Stamp.proj_measurable` and
`ext; cases <;> simp [<ctor>.π …]`. The toy `Probe` is declared **in this same module**,
so `simp [Probe.<ctor>.π]` trips Lean's `enableRealizationsForConst` guard (the projection's
equation lemmas are only realized for *imported* constants). Real stamping always imports
its inductive from `Syntax.lean`, so this never bites in practice; the section is therefore
omitted for the toy. See `Exp.<ctor>.π.measurable` (incl. ternary `cond`/`case`, mixed
`unop`/`binop`, `scrut`) for the full worked battery the toy would otherwise mirror. -/

/-! ### §26 casesOn_preimage_decomp -/

/-- Per-constructor cell family for the `casesOn` preimage decomposition. -/
def decompCell
    {rT : Type _} {α : Type _} (S : Set α)
    (f_nil : Unit → α) (f_tag : Nat → α) (f_dat : BaseLit rT → α)
    (f_box : Probe rT → α) (f_pr : Probe rT × Probe rT → α)
    (f_tri : Probe rT × Probe rT × Probe rT → α)
    (f_mix : UnOp × Probe rT → α) (f_scr : Probe rT × BaseLit rT → α)
    (f_quad : Probe rT × Probe rT × Probe rT × Probe rT → α) : Fin 9 → Set (Probe rT) :=
  ![ Probe.nil.ι  '' (f_nil  ⁻¹' S)
   , Probe.tag.ι  '' (f_tag  ⁻¹' S)
   , Probe.dat.ι  '' (f_dat  ⁻¹' S)
   , Probe.box.ι  '' (f_box  ⁻¹' S)
   , Probe.pr.ι   '' (f_pr   ⁻¹' S)
   , Probe.tri.ι  '' (f_tri  ⁻¹' S)
   , Probe.mix.ι  '' (f_mix  ⁻¹' S)
   , Probe.scr.ι  '' (f_scr  ⁻¹' S)
   , Probe.quad.ι '' (f_quad ⁻¹' S) ]

theorem casesOn_preimage_decomp
    {rT : Type _} {α : Type _} (S : Set α)
    (f_nil : Unit → α) (f_tag : Nat → α) (f_dat : BaseLit rT → α)
    (f_box : Probe rT → α) (f_pr : Probe rT × Probe rT → α)
    (f_tri : Probe rT × Probe rT × Probe rT → α)
    (f_mix : UnOp × Probe rT → α) (f_scr : Probe rT × BaseLit rT → α)
    (f_quad : Probe rT × Probe rT × Probe rT × Probe rT → α) :
    (fun p : Probe rT => Probe.casesOn (motive := fun _ => α) p
        (f_nil ()) f_tag f_dat f_box
        (fun p1 p2 => f_pr (p1, p2))
        (fun p1 p2 p3 => f_tri (p1, p2, p3))
        (fun u p => f_mix (u, p))
        (fun p b => f_scr (p, b))
        (fun p1 p2 p3 p4 => f_quad (p1, p2, p3, p4))) ⁻¹' S
      = ⋃ i, decompCell S f_nil f_tag f_dat f_box f_pr f_tri f_mix f_scr f_quad i := by
  ext p
  simp only [Set.mem_preimage, Set.mem_iUnion, decompCell]
  constructor
  · intro hp; cases p
    · exact ⟨0, (), hp, rfl⟩
    · exact ⟨1, _, hp, rfl⟩
    · exact ⟨2, _, hp, rfl⟩
    · exact ⟨3, _, hp, rfl⟩
    · exact ⟨4, ⟨_, _⟩, hp, rfl⟩
    · exact ⟨5, ⟨_, _, _⟩, hp, rfl⟩
    · exact ⟨6, ⟨_, _⟩, hp, rfl⟩
    · exact ⟨7, ⟨_, _⟩, hp, rfl⟩
    · exact ⟨8, ⟨_, _, _, _⟩, hp, rfl⟩
  · rintro ⟨i, hi⟩; fin_cases i <;>
      · obtain ⟨q, hq, hp⟩ := hi; cases hp; simpa using hq

/-! ### §27 measurable_rec -/

@[fun_prop]
theorem measurable_rec
    {rT : Type _} [MeasurableSpace rT]
    {α : Type _} [MeasurableSpace α]
    (f_nil : Unit → α) (f_tag : Nat → α) (f_dat : BaseLit rT → α)
    (f_box : Probe rT → α) (f_pr : Probe rT × Probe rT → α)
    (f_tri : Probe rT × Probe rT × Probe rT → α)
    (f_mix : UnOp × Probe rT → α) (f_scr : Probe rT × BaseLit rT → α)
    (f_quad : Probe rT × Probe rT × Probe rT × Probe rT → α)
    (h_dat : Measurable f_dat)
    (h_box : Measurable f_box) (h_pr : Measurable f_pr)
    (h_tri : Measurable f_tri) (h_mix : Measurable f_mix)
    (h_scr : Measurable f_scr) (h_quad : Measurable f_quad) :
    Measurable (fun p : Probe rT =>
      Probe.casesOn (motive := fun _ => α) p
        (f_nil ()) f_tag f_dat f_box
        (fun p1 p2 => f_pr (p1, p2))
        (fun p1 p2 p3 => f_tri (p1, p2, p3))
        (fun u p => f_mix (u, p))
        (fun p b => f_scr (p, b))
        (fun p1 p2 p3 p4 => f_quad (p1, p2, p3, p4))) := by
  intro S hS
  rw [StampTest.casesOn_preimage_decomp]
  refine .iUnion fun i => ?_
  fin_cases i
  · exact nil.measurableEmbedding.measurableSet_image'  (by measurability)
  · exact tag.measurableEmbedding.measurableSet_image'  (by measurability)
  · exact dat.measurableEmbedding.measurableSet_image'  (h_dat hS)
  · exact box.measurableEmbedding.measurableSet_image'  (h_box hS)
  · exact pr.measurableEmbedding.measurableSet_image'   (h_pr hS)
  · exact tri.measurableEmbedding.measurableSet_image'  (h_tri hS)
  · exact mix.measurableEmbedding.measurableSet_image'  (h_mix hS)
  · exact scr.measurableEmbedding.measurableSet_image'  (h_scr hS)
  · exact quad.measurableEmbedding.measurableSet_image' (h_quad hS)

/-! ### §28 casesOn_preimage_decomp_param (Fin-indexed cells, uniform with the plain form) -/

/-- Per-constructor cell family for the `β`-parameterised decomposition. -/
def decompCell_param
    {rT : Type _} {α β : Type _} (S : Set α)
    (f_nil : β × Unit → α) (f_tag : β × Nat → α) (f_dat : β × BaseLit rT → α)
    (f_box : β × Probe rT → α) (f_pr : β × Probe rT × Probe rT → α)
    (f_tri : β × Probe rT × Probe rT × Probe rT → α)
    (f_mix : β × UnOp × Probe rT → α) (f_scr : β × Probe rT × BaseLit rT → α)
    (f_quad : β × Probe rT × Probe rT × Probe rT × Probe rT → α) :
    Fin 9 → Set (Probe rT × β) :=
  ![ (fun q : β × Unit => (Probe.nil, q.1))           '' (f_nil  ⁻¹' S)
   , (fun q : β × Nat => (Probe.tag q.2, q.1))        '' (f_tag  ⁻¹' S)
   , (fun q : β × BaseLit rT => (Probe.dat q.2, q.1)) '' (f_dat  ⁻¹' S)
   , (fun q : β × Probe rT => (Probe.box q.2, q.1))   '' (f_box  ⁻¹' S)
   , (fun q : β × Probe rT × Probe rT => (Probe.pr q.2.1 q.2.2, q.1)) '' (f_pr ⁻¹' S)
   , (fun q : β × Probe rT × Probe rT × Probe rT =>
        (Probe.tri q.2.1 q.2.2.1 q.2.2.2, q.1)) '' (f_tri ⁻¹' S)
   , (fun q : β × UnOp × Probe rT => (Probe.mix q.2.1 q.2.2, q.1)) '' (f_mix ⁻¹' S)
   , (fun q : β × Probe rT × BaseLit rT => (Probe.scr q.2.1 q.2.2, q.1)) '' (f_scr ⁻¹' S)
   , (fun q : β × Probe rT × Probe rT × Probe rT × Probe rT =>
        (Probe.quad q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2, q.1)) '' (f_quad ⁻¹' S) ]

theorem casesOn_preimage_decomp_param
    {rT : Type _} {α β : Type _} (S : Set α)
    (f_nil : β × Unit → α) (f_tag : β × Nat → α) (f_dat : β × BaseLit rT → α)
    (f_box : β × Probe rT → α) (f_pr : β × Probe rT × Probe rT → α)
    (f_tri : β × Probe rT × Probe rT × Probe rT → α)
    (f_mix : β × UnOp × Probe rT → α) (f_scr : β × Probe rT × BaseLit rT → α)
    (f_quad : β × Probe rT × Probe rT × Probe rT × Probe rT → α) :
    (fun p : Probe rT × β => Probe.casesOn (motive := fun _ => α) p.1
        (f_nil (p.2, ())) (fun n => f_tag (p.2, n)) (fun b => f_dat (p.2, b))
        (fun e => f_box (p.2, e))
        (fun e1 e2 => f_pr (p.2, e1, e2))
        (fun e1 e2 e3 => f_tri (p.2, e1, e2, e3))
        (fun u e => f_mix (p.2, u, e))
        (fun e b => f_scr (p.2, e, b))
        (fun e1 e2 e3 e4 => f_quad (p.2, e1, e2, e3, e4))) ⁻¹' S
      = ⋃ i, decompCell_param S f_nil f_tag f_dat f_box f_pr f_tri f_mix f_scr f_quad i := by
  ext ⟨e, b⟩
  simp only [Set.mem_preimage, Set.mem_iUnion, decompCell_param]
  constructor
  · intro he; cases e
    · exact ⟨0, (b, ()), he, rfl⟩
    · exact ⟨1, (b, _), he, rfl⟩
    · exact ⟨2, (b, _), he, rfl⟩
    · exact ⟨3, (b, _), he, rfl⟩
    · exact ⟨4, (b, _, _), he, rfl⟩
    · exact ⟨5, (b, _, _, _), he, rfl⟩
    · exact ⟨6, (b, _, _), he, rfl⟩
    · exact ⟨7, (b, _, _), he, rfl⟩
    · exact ⟨8, (b, _, _, _, _), he, rfl⟩
  · rintro ⟨i, hi⟩; fin_cases i <;>
      · obtain ⟨q, hq, hp⟩ := hi; cases hp; simpa using hq

/-! ### §29 measurable_rec_param -/

@[fun_prop]
theorem measurable_rec_param
    {rT : Type _} [MeasurableSpace rT]
    {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    (c_nil : β × Unit → α) (c_tag : β × Nat → α) (c_dat : β × BaseLit rT → α)
    (c_box : β × Probe rT → α) (c_pr : β × Probe rT × Probe rT → α)
    (c_tri : β × Probe rT × Probe rT × Probe rT → α)
    (c_mix : β × UnOp × Probe rT → α) (c_scr : β × Probe rT × BaseLit rT → α)
    (c_quad : β × Probe rT × Probe rT × Probe rT × Probe rT → α)
    (h_nil : Measurable c_nil) (h_tag : Measurable c_tag) (h_dat : Measurable c_dat)
    (h_box : Measurable c_box) (h_pr : Measurable c_pr) (h_tri : Measurable c_tri)
    (h_mix : Measurable c_mix) (h_scr : Measurable c_scr) (h_quad : Measurable c_quad) :
    Measurable (fun p : Probe rT × β =>
      Probe.casesOn (motive := fun _ => α) p.1
        (c_nil (p.2, ())) (fun n => c_tag (p.2, n)) (fun b => c_dat (p.2, b))
        (fun e => c_box (p.2, e))
        (fun e1 e2 => c_pr (p.2, e1, e2))
        (fun e1 e2 e3 => c_tri (p.2, e1, e2, e3))
        (fun u e => c_mix (p.2, u, e))
        (fun e b => c_scr (p.2, e, b))
        (fun e1 e2 e3 e4 => c_quad (p.2, e1, e2, e3, e4))) := by
  intro S hS
  rw [casesOn_preimage_decomp_param]
  refine .iUnion fun i => ?_
  fin_cases i
  · exact ((nil.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_nil hS)
  · exact ((tag.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_tag hS)
  · exact ((dat.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_dat hS)
  · exact ((box.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_box hS)
  · exact ((pr.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_pr hS)
  · exact ((tri.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_tri hS)
  · exact ((mix.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_mix hS)
  · exact ((scr.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_scr hS)
  · exact ((quad.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_quad hS)

/-! ### §30 the keystone `measurable_struct_rec` -/

section StructRec

variable {rT α : Type _} [MeasurableSpace rT] [MeasurableSpace α]
variable {f : Probe rT → α}

variable {c_nil  : α}
variable {c_tag  : Nat → α}
variable {c_dat  : BaseLit rT → α}
variable {c_box  : α → α}
variable {c_pr   : α → α → α}
variable {c_tri  : α → α → α → α}
variable {c_mix  : UnOp → α → α}
variable {c_scr  : α → BaseLit rT → α}
variable {c_quad : α → α → α → α → α}
variable (eq_nil  : f .nil = c_nil)
variable (eq_tag  : ∀ n, f (.tag n) = c_tag n)
variable (eq_dat  : ∀ b, f (.dat b) = c_dat b)
variable (eq_box  : ∀ p, f (.box p) = c_box (f p))
variable (eq_pr   : ∀ p1 p2, f (.pr p1 p2) = c_pr (f p1) (f p2))
variable (eq_tri  : ∀ p1 p2 p3, f (.tri p1 p2 p3) = c_tri (f p1) (f p2) (f p3))
variable (eq_mix  : ∀ u p, f (.mix u p) = c_mix u (f p))
variable (eq_scr  : ∀ p b, f (.scr p b) = c_scr (f p) b)
variable (eq_quad : ∀ p1 p2 p3 p4, f (.quad p1 p2 p3 p4) = c_quad (f p1) (f p2) (f p3) (f p4))
variable (h_dat  : Measurable c_dat)
variable (h_box  : Measurable c_box)
variable (h_pr   : Measurable (Function.uncurry c_pr))
variable (h_tri  : Measurable (fun q : α × α × α => c_tri q.1 q.2.1 q.2.2))
variable (h_mix  : Measurable (Function.uncurry c_mix))
variable (h_scr  : Measurable (Function.uncurry c_scr))
variable (h_quad : Measurable (fun q : α × α × α × α => c_quad q.1 q.2.1 q.2.2.1 q.2.2.2))

include eq_nil eq_tag eq_dat eq_box eq_pr eq_tri eq_mix eq_scr eq_quad
        h_dat h_box h_pr h_tri h_mix h_scr h_quad in
/-- **The keystone** for `Probe`. -/
theorem measurable_struct_rec : Measurable f := by
  apply _root_.StructRec.measurable_of_cells Probe.shape; intro s
  induction s with
  | nil =>
    intro U hU
    exact _root_.StructRec.cell_nullary Probe.shape (ctor := .nil)
      (fun p => by cases p <;> simp) eq_nil (flatten_measurable .nil)
  | tag n =>
    intro U hU
    exact _root_.StructRec.cell_nullary Probe.shape (ctor := .tag n)
      (fun p => by cases p <;> simp) (eq_tag n) (flatten_measurable .tag)
  | dat =>
    intro U hU
    exact _root_.StructRec.cell_dataLeaf Probe.shape dat.measurableEmbedding
      (fun p => by cases p <;> simp) eq_dat h_dat hU
  | box _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary Probe.shape box.measurableEmbedding
      (fun p => by cases p <;> simp) eq_box h_box @ih hU
  | pr _ _ ih1 ih2 =>
    intro U hU
    exact _root_.StructRec.cell_binary Probe.shape (ctor := Probe.pr)
      pr.measurableEmbedding (fun p => by cases p <;> simp) eq_pr h_pr @ih1 @ih2 hU
  | tri _ _ _ ih1 ih2 ih3 =>
    intro U hU
    exact _root_.StructRec.cell_ternary Probe.shape (ctor := Probe.tri)
      tri.measurableEmbedding (fun p => by cases p <;> simp) eq_tri h_tri @ih1 @ih2 @ih3 hU
  | mix u _ ih =>
    intro U hU
    have h_emb_u : MeasurableEmbedding (Probe.mix u : Probe rT → Probe rT) :=
      .of_uncurry_fixed_left mix.measurableEmbedding (MeasurableSet.singleton u)
    have h_c_u : Measurable (c_mix u) :=
      h_mix.comp (by fun_prop : Measurable (fun x : α => (u, x)))
    exact _root_.StructRec.cell_unary Probe.shape (ctor := (Probe.mix u : Probe rT → Probe rT))
      h_emb_u (fun p => by cases p <;> simp) (eq_mix u) h_c_u @ih hU
  | scr _ ih =>
    intro U hU
    exact _root_.StructRec.cell_scrutLike Probe.shape (ctor := Probe.scr)
      scr.measurableEmbedding (fun p => by cases p <;> simp) eq_scr h_scr @ih hU
  | quad _ _ _ _ ih1 ih2 ih3 ih4 =>
    intro U hU
    exact _root_.StructRec.cell_quaternary Probe.shape (ctor := Probe.quad)
      quad.measurableEmbedding (fun p => by cases p <;> simp) eq_quad h_quad
      @ih1 @ih2 @ih3 @ih4 hU

end StructRec

/-! ### §31 the param-threaded keystone `measurable_struct_rec_param` -/

section StructRecParam

variable {rT α β : Type _} [MeasurableSpace rT] [MeasurableSpace α] [MeasurableSpace β]
variable [Inhabited β]
variable {g : β → Probe rT → α}

variable {c_nil  : β → α}
variable {c_tag  : β → Nat → α}
variable {c_dat  : β → BaseLit rT → α}
variable {c_box  : β → α → α}
variable {c_pr   : β → α → α → α}
variable {c_tri  : β → α → α → α → α}
variable {c_mix  : β → UnOp → α → α}
variable {c_scr  : β → α → BaseLit rT → α}
variable {c_quad : β → α → α → α → α → α}
variable (eq_nil  : ∀ b, g b .nil = c_nil b)
variable (eq_tag  : ∀ b n, g b (.tag n) = c_tag b n)
variable (eq_dat  : ∀ b l, g b (.dat l) = c_dat b l)
variable (eq_box  : ∀ b p, g b (.box p) = c_box b (g b p))
variable (eq_pr   : ∀ b p1 p2, g b (.pr p1 p2) = c_pr b (g b p1) (g b p2))
variable (eq_tri  : ∀ b p1 p2 p3, g b (.tri p1 p2 p3) = c_tri b (g b p1) (g b p2) (g b p3))
variable (eq_mix  : ∀ b u p, g b (.mix u p) = c_mix b u (g b p))
variable (eq_scr  : ∀ b p l, g b (.scr p l) = c_scr b (g b p) l)
variable (eq_quad : ∀ b p1 p2 p3 p4,
  g b (.quad p1 p2 p3 p4) = c_quad b (g b p1) (g b p2) (g b p3) (g b p4))
variable (h_nil  : Measurable c_nil)
variable (h_tag  : Measurable (Function.uncurry c_tag))
variable (h_dat  : Measurable (Function.uncurry c_dat))
variable (h_box  : Measurable (Function.uncurry c_box))
variable (h_pr   : Measurable (fun q : β × α × α => c_pr q.1 q.2.1 q.2.2))
variable (h_tri  : Measurable (fun q : β × α × α × α => c_tri q.1 q.2.1 q.2.2.1 q.2.2.2))
variable (h_mix  : Measurable (fun q : β × UnOp × α => c_mix q.1 q.2.1 q.2.2))
variable (h_scr  : Measurable (fun q : β × α × BaseLit rT => c_scr q.1 q.2.1 q.2.2))
variable (h_quad : Measurable
  (fun q : β × α × α × α × α => c_quad q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2))

include eq_nil eq_tag eq_dat eq_box eq_pr eq_tri eq_mix eq_scr eq_quad
        h_nil h_tag h_dat h_box h_pr h_tri h_mix h_scr h_quad in
/-- **Param-threaded keystone** for `Probe`. -/
theorem measurable_struct_rec_param : Measurable (Function.uncurry g) := by
  apply _root_.StructRec.measurable_of_cells_param Probe.shape; intro s
  induction s with
  | nil =>
    intro U hU
    exact _root_.StructRec.cell_nullary_param Probe.shape (ctor := .nil)
      (fun p => by cases p <;> simp) eq_nil h_nil hU (flatten_measurable .nil)
  | tag n =>
    intro U hU
    exact _root_.StructRec.cell_nullary_param Probe.shape (ctor := .tag n)
      (fun p => by cases p <;> simp) (fun b => eq_tag b n)
      (h_tag.comp (by fun_prop : Measurable (fun b : β => (b, n)))) hU (flatten_measurable .tag)
  | dat =>
    intro U hU
    exact _root_.StructRec.cell_dataLeaf_param Probe.shape dat.measurableEmbedding
      (fun p => by cases p <;> simp) eq_dat h_dat hU
  | box _ ih =>
    intro U hU
    exact _root_.StructRec.cell_unary_param Probe.shape box.measurableEmbedding
      (fun p => by cases p <;> simp) eq_box h_box @ih hU
  | pr _ _ ih1 ih2 =>
    intro U hU
    exact _root_.StructRec.cell_binary_param Probe.shape (ctor := Probe.pr)
      pr.measurableEmbedding (fun p => by cases p <;> simp) eq_pr h_pr @ih1 @ih2 hU
  | tri _ _ _ ih1 ih2 ih3 =>
    intro U hU
    exact _root_.StructRec.cell_ternary_param Probe.shape (ctor := Probe.tri)
      tri.measurableEmbedding (fun p => by cases p <;> simp) eq_tri h_tri @ih1 @ih2 @ih3 hU
  | mix u _ ih =>
    intro U hU
    have h_emb_u : MeasurableEmbedding (Probe.mix u : Probe rT → Probe rT) :=
      .of_uncurry_fixed_left mix.measurableEmbedding (MeasurableSet.singleton u)
    have h_c_u : Measurable (Function.uncurry (fun (b : β) (a : α) => c_mix b u a)) :=
      h_mix.comp (by fun_prop : Measurable (fun q : β × α => (q.1, u, q.2)))
    exact _root_.StructRec.cell_unary_param Probe.shape (ctor := (Probe.mix u : Probe rT → Probe rT))
      h_emb_u (fun p => by cases p <;> simp) (fun b p => eq_mix b u p) h_c_u @ih hU
  | scr _ ih =>
    intro U hU
    exact _root_.StructRec.cell_scrutLike_param Probe.shape (ctor := Probe.scr)
      scr.measurableEmbedding (fun p => by cases p <;> simp) eq_scr h_scr @ih hU
  | quad _ _ _ _ ih1 ih2 ih3 ih4 =>
    intro U hU
    exact _root_.StructRec.cell_quaternary_param Probe.shape (ctor := Probe.quad)
      quad.measurableEmbedding (fun p => by cases p <;> simp) eq_quad h_quad
      @ih1 @ih2 @ih3 @ih4 hU

end StructRecParam

/-! ### §33 synthetic smoke-test battery -/

/-- Test 1: discrete codomain (`tagDepth : Probe rT → Nat`). -/
@[simp] def tagDepth : Probe rT → Nat
  | .nil          => 0
  | .tag _        => 0
  | .dat _        => 0
  | .box p        => tagDepth p + 1
  | .pr p1 p2     => max (tagDepth p1) (tagDepth p2) + 1
  | .tri p1 p2 p3 => max (max (tagDepth p1) (tagDepth p2)) (tagDepth p3) + 1
  | .mix _ p      => tagDepth p + 1
  | .scr p _      => tagDepth p + 1
  | .quad p1 p2 p3 p4 =>
      max (max (tagDepth p1) (tagDepth p2)) (max (tagDepth p3) (tagDepth p4)) + 1

theorem tagDepth.measurable [MeasurableSpace rT] :
    Measurable (tagDepth : Probe rT → Nat) := by
  apply measurable_struct_rec (f := tagDepth)
    (c_nil := 0) (c_tag := fun _ => 0) (c_dat := fun _ => 0)
    (c_box := (· + 1)) (c_pr := fun n1 n2 => max n1 n2 + 1)
    (c_tri := fun n1 n2 n3 => max (max n1 n2) n3 + 1)
    (c_mix := fun _ n => n + 1) (c_scr := fun n _ => n + 1)
    (c_quad := fun n1 n2 n3 n4 => max (max n1 n2) (max n3 n4) + 1)
  all_goals first | (intros; rfl) | fun_prop

/-- Test 2: data-leaf dependent (`countLeaves : Probe rT → Nat`). -/
@[simp] def countLeaves : Probe rT → Nat
  | .nil          => 0
  | .tag _        => 0
  | .dat _        => 1
  | .box p        => countLeaves p
  | .pr p1 p2     => countLeaves p1 + countLeaves p2
  | .tri p1 p2 p3 => countLeaves p1 + countLeaves p2 + countLeaves p3
  | .mix _ p      => countLeaves p
  | .scr p _      => countLeaves p + 1
  | .quad p1 p2 p3 p4 => countLeaves p1 + countLeaves p2 + countLeaves p3 + countLeaves p4

theorem countLeaves.measurable [MeasurableSpace rT] :
    Measurable (countLeaves : Probe rT → Nat) := by
  apply measurable_struct_rec (f := countLeaves)
    (c_nil := 0) (c_tag := fun _ => 0) (c_dat := fun _ => 1)
    (c_box := id) (c_pr := (· + ·))
    (c_tri := fun n1 n2 n3 => n1 + n2 + n3)
    (c_mix := fun _ n => n) (c_scr := fun n _ => n + 1)
    (c_quad := fun n1 n2 n3 n4 => n1 + n2 + n3 + n4)
  all_goals first | (intros; rfl) | fun_prop

/-- Test 3: endo-map (`Probe rT → Probe rT`, non-discrete codomain). -/
@[simp] def endoMap : Probe rT → Probe rT
  | .nil          => .nil
  | .tag n        => .tag n
  | .dat b        => .dat b
  | .box p        => .box (.box (endoMap p))
  | .pr p1 p2     => .pr (endoMap p1) (endoMap p2)
  | .tri p1 p2 p3 => .tri (endoMap p1) (endoMap p2) (endoMap p3)
  | .mix u p      => .mix u (endoMap p)
  | .scr p b      => .scr (endoMap p) b
  | .quad p1 p2 p3 p4 => .quad (endoMap p1) (endoMap p2) (endoMap p3) (endoMap p4)

theorem endoMap.measurable [MeasurableSpace rT] :
    Measurable (endoMap : Probe rT → Probe rT) := by
  apply measurable_struct_rec (f := endoMap)
    (c_nil := .nil) (c_tag := Probe.tag) (c_dat := Probe.dat)
    (c_box := fun p => .box (.box p)) (c_pr := fun p1 p2 => .pr p1 p2)
    (c_tri := fun p1 p2 p3 => .tri p1 p2 p3)
    (c_mix := fun u p => .mix u p) (c_scr := fun p b => .scr p b)
    (c_quad := fun p1 p2 p3 p4 => .quad p1 p2 p3 p4)
  all_goals first | (intros; rfl) | fun_prop

/-- Test 4: param-threaded (`addAcc : Nat → Probe rT → Nat`, the `β` is the running
accumulator threaded unchanged into every recursive call). -/
@[simp] def addAcc : Nat → Probe rT → Nat
  | acc, .nil          => acc
  | acc, .tag n        => acc + n
  | acc, .dat _        => acc
  | acc, .box p        => addAcc acc p
  | acc, .pr p1 p2     => addAcc acc p1 + addAcc acc p2
  | acc, .tri p1 p2 p3 => addAcc acc p1 + addAcc acc p2 + addAcc acc p3
  | acc, .mix _ p      => addAcc acc p
  | acc, .scr p _      => addAcc acc p
  | acc, .quad p1 p2 p3 p4 => addAcc acc p1 + addAcc acc p2 + addAcc acc p3 + addAcc acc p4

theorem addAcc.measurable [MeasurableSpace rT] :
    Measurable (Function.uncurry (addAcc : Nat → Probe rT → Nat)) := by
  apply measurable_struct_rec_param (g := addAcc)
    (c_nil := fun acc => acc) (c_tag := fun acc n => acc + n) (c_dat := fun acc _ => acc)
    (c_box := fun _ n => n) (c_pr := fun _ n1 n2 => n1 + n2)
    (c_tri := fun _ n1 n2 n3 => n1 + n2 + n3)
    (c_mix := fun _ _ n => n) (c_scr := fun _ n _ => n)
    (c_quad := fun _ n1 n2 n3 n4 => n1 + n2 + n3 + n4)
  all_goals first | (intros; rfl) | fun_prop

/-! ### §34–§35 singleton class -/

@[simp] def singletonCyl {rT : Type _} : Probe rT → Cylinder rT
  | .nil          => .nil
  | .tag n        => .tag n
  | .dat b        => .dat {b}
  | .box p        => .box (singletonCyl p)
  | .pr p1 p2     => .pr (singletonCyl p1) (singletonCyl p2)
  | .tri p1 p2 p3 => .tri (singletonCyl p1) (singletonCyl p2) (singletonCyl p3)
  | .mix u p      => .mix u (singletonCyl p)
  | .scr p b      => .scr (singletonCyl p) {b}
  | .quad p1 p2 p3 p4 =>
      .quad (singletonCyl p1) (singletonCyl p2) (singletonCyl p3) (singletonCyl p4)

theorem singletonCyl_flatten {rT : Type _} (p : Probe rT) :
    (singletonCyl p).flatten = {p} := by
  induction p with
  | nil => simp
  | tag n => simp
  | dat b => simp
  | box p ih => simp [ih]
  | pr p1 p2 ih1 ih2 => simp [ih1, ih2]
  | tri p1 p2 p3 ih1 ih2 ih3 => simp [ih1, ih2, ih3]
  | mix u p ih => simp [ih]
  | scr p b ih => simp [ih]
  | quad p1 p2 p3 p4 ih1 ih2 ih3 ih4 => simp [ih1, ih2, ih3, ih4]

theorem singletonCyl_hasMeasurableLeaves
    {rT : Type _} [MeasurableSpace rT] [MeasurableSingletonClass rT] (p : Probe rT) :
    (singletonCyl p).HasMeasurableLeaves := by
  induction p with
  | nil => exact .nil
  | tag n => exact .tag
  | dat b => exact .dat _ (MeasurableSet.singleton b)
  | box p ih => exact .box ih
  | pr p1 p2 ih1 ih2 => exact .pr ih1 ih2
  | tri p1 p2 p3 ih1 ih2 ih3 => exact .tri ih1 ih2 ih3
  | mix u p ih => exact .mix ih
  | scr p b ih => exact .scr _ ih (MeasurableSet.singleton b)
  | quad p1 p2 p3 p4 ih1 ih2 ih3 ih4 => exact .quad ih1 ih2 ih3 ih4

instance instMeasurableSingletonClass
    {rT : Type _} [MeasurableSpace rT] [MeasurableSingletonClass rT] :
    MeasurableSingletonClass (Probe rT) where
  measurableSet_singleton :=
    Stamp.measurableSet_singleton rfl singletonCyl_flatten singletonCyl_hasMeasurableLeaves

end StampTest
end ProbLang
end ProbLangMeasures
