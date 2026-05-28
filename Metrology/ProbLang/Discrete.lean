module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.CoreMeasures

@[expose] public section

/-! # Discreteness lifting for ProbLang measure spaces

If the real-type `rT` (or, for the syntactic types built on top of it, the parameter `α`) is
discrete in the sense of `MeasurableSingletonClass`, then the measure spaces built in
`CoreMeasures` are also discrete.

The proofs all share the same shape: build a "singleton cylinder" that has the given inhabitant
as its sole flatten-image, observe it has measurable leaves (singletons are measurable in a
`MeasurableSingletonClass`), and conclude via `MeasurableSpace.measurableSet_generateFrom`.

The chain is BaseLit → Pat → Exp → Val → EctxItem. -/

noncomputable section ProbLangDiscrete

open Classical MeasureTheory ProbabilityTheory ProbLang

namespace ProbLang

/-! ## BaseLit -/

namespace BaseLit

/-- Cylinder over `b` that singletons every `real` leaf. -/
@[simp] def singletonCyl {rT : Type _} : BaseLit rT → Cylinder rT
  | .int z      => .int z
  | .bool b     => .bool b
  | .unit       => .unit
  | .loc l      => .loc l
  | .lbl l      => .lbl l
  | .real r     => .real {r}

theorem singletonCyl_flatten {rT : Type _} (b : BaseLit rT) :
    (singletonCyl b).flatten = {b} := by
  induction b with
  | int z => simp
  | bool b => simp
  | unit => simp
  | loc l => simp
  | lbl l => simp
  | real r => simp

theorem singletonCyl_hasMeasurableLeaves
    {rT : Type _} [MeasurableSpace rT] [MeasurableSingletonClass rT] (b : BaseLit rT) :
    (singletonCyl b).HasMeasurableLeaves := by
  induction b with
  | int z => exact .int
  | bool b => exact .bool
  | unit => exact .unit
  | loc l => exact .loc
  | lbl l => exact .lbl
  | real r => exact .real _ (MeasurableSet.singleton r)

instance instMeasurableSingletonClass
    {rT : Type _} [MeasurableSpace rT] [MeasurableSingletonClass rT] :
    MeasurableSingletonClass (BaseLit rT) where
  measurableSet_singleton b := by
    rw [← singletonCyl_flatten b]
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨singletonCyl b, singletonCyl_hasMeasurableLeaves b, rfl⟩

end BaseLit

/-! ## Pat -/

namespace Pat

@[simp] def singletonCyl {rT : Type _} : Pat rT → Cylinder rT
  | .wildcard   => .wildcard
  | .lit b      => .lit {b}
  | .pair p1 p2 => .pair (singletonCyl p1) (singletonCyl p2)
  | .inl p      => .inl (singletonCyl p)
  | .inr p      => .inr (singletonCyl p)

theorem singletonCyl_flatten {rT : Type _} (p : Pat rT) :
    (singletonCyl p).flatten = {p} := by
  induction p with
  | wildcard => simp
  | lit b => simp
  | pair p1 p2 ih1 ih2 => simp [ih1, ih2]
  | inl p ih => simp [ih]
  | inr p ih => simp [ih]

theorem singletonCyl_hasMeasurableLeaves
    {rT : Type _} [MeasurableSpace rT] [MeasurableSingletonClass rT] (p : Pat rT) :
    (singletonCyl p).HasMeasurableLeaves := by
  induction p with
  | wildcard => exact .wildcard
  | lit b => exact .lit _ (MeasurableSet.singleton b)
  | pair p1 p2 ih1 ih2 => exact .pair ih1 ih2
  | inl p ih => exact .inl ih
  | inr p ih => exact .inr ih

instance instMeasurableSingletonClass
    {rT : Type _} [MeasurableSpace rT] [MeasurableSingletonClass rT] :
    MeasurableSingletonClass (Pat rT) where
  measurableSet_singleton p := by
    rw [← singletonCyl_flatten p]
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨singletonCyl p, singletonCyl_hasMeasurableLeaves p, rfl⟩

end Pat

/-! ## Exp -/

namespace Exp

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
  | scrut e p ih => exact .scrut _ ih (MeasurableSet.singleton p)

instance instMeasurableSingletonClass
    {rT : Type _} [MeasurableSpace rT] [MeasurableSingletonClass rT] :
    MeasurableSingletonClass (Exp rT) where
  measurableSet_singleton e := by
    rw [← singletonCyl_flatten e]
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨singletonCyl e, singletonCyl_hasMeasurableLeaves e, rfl⟩

end Exp

/-! ## Val

`Val α = Σ e : Exp α, IsVal e` with the Sigma σ-algebra. `IsVal` carries `⊤`, so every set is
measurable there; combined with discreteness of `Exp α`, singletons of `Val α` are measurable. -/

namespace Val

instance instMeasurableSingletonClass
    {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Val α) where
  measurableSet_singleton := fun _ => by sorry

end Val

/-! ## EctxItem -/

namespace EctxItem

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

end EctxItem

end ProbLang

/-! ## Sanity check: `DiscreteMeasurableSpace` synthesizes -/

section SynthCheck
variable {rT : Type _} [MeasurableSpace rT] [MeasurableSingletonClass rT] [Countable rT]

example : DiscreteMeasurableSpace (ProbLang.BaseLit rT) := inferInstance
example : DiscreteMeasurableSpace (ProbLang.Pat rT)     := inferInstance
example : DiscreteMeasurableSpace (ProbLang.Exp rT)     := inferInstance
example : DiscreteMeasurableSpace (ProbLang.Val rT)     := inferInstance
example : DiscreteMeasurableSpace (ProbLang.EctxItem rT) := inferInstance
end SynthCheck

/-! ## Default `ProbLangℝ` instance on `Int`

Downstream Iris / Approxis / TotalEris layers currently instantiate `rT := Int`. Provide a
single canonical `ProbLangℝ Int` instance here so they all share one definition (avoiding
duplicate-name collisions when one file transitively imports two of them). -/
instance instProbLangℝInt : ProbLang.ProbLangℝ Int where
  instDecidableEq := inferInstance

end ProbLangDiscrete
