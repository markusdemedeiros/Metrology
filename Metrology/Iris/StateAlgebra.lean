module

public import Mathlib.Data.ENNReal.Basic
public import Iris
public import Iris.Algebra.HeapView
public import Iris.Instances.IProp.Instance
public import Iris.Std.HeapInstances
public import Metrology.Iris.Algebra
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.Discrete

@[expose] public section

/-!
# Algebra for ProbLang program state

The CMRAs used to model the heap and tapes (`HeapView` over `Agree`), the
discreteness instances for `Exp`/`Val`/`Tape` they rest on, and the
`LocHeap.asAgree` bridge between a plain `LocHeap` and its agreement-lifted
form. The ghost state built on top of these lives in `AppProgram.lean`.
-/

section StateRA
open Std Iris Iris.Std COFE ProbLang

variable {rT : Type _} [ProbLang.ProbLangℝ rT]

instance : COFE (Exp rT) := COFE.ofDiscrete _
instance : OFE.Discrete (Exp rT) := ⟨id⟩
instance (x : Exp rT) : OFE.DiscreteE x := ⟨OFE.Discrete.discrete_0⟩

instance : COFE Tape := COFE.ofDiscrete _
instance : OFE.Discrete Tape := ⟨id⟩
instance (x : Tape) : OFE.DiscreteE x := ⟨OFE.Discrete.discrete_0⟩

instance : COFE (Val rT) := COFE.ofDiscrete _
instance : OFE.Discrete (Val rT) := ⟨id⟩
instance (x : Val rT) : OFE.DiscreteE x := ⟨OFE.Discrete.discrete_0⟩

abbrev SpecHeap (rT : Type _) [ProbLang.ProbLangℝ rT] :=
  HeapView Loc (Agree (Val rT)) LocHeap
abbrev SpecTapes := HeapView Loc (Agree Tape) LocHeap

def LocHeap.asAgree [OFE V] (h : LocHeap V) : LocHeap (Agree V) :=
  PartialMap.map LocHeap toAgree h

theorem LocHeap.asAgree_get? [OFE V] (h : LocHeap V) (l : Loc) :
    PartialMap.get? (LocHeap.asAgree h) l = (PartialMap.get? h l).map toAgree := by
  show PartialMap.get? _ _ = _
  simp only [LocHeap.asAgree, PartialMap.map, LawfulPartialMap.get?_bindAlter]
  cases PartialMap.get? h l <;> rfl

theorem LocHeap.asAgree_insert [OFE V] (h : LocHeap V) (l : Loc) (v : V) :
    LocHeap.asAgree (PartialMap.insert h l v) =
      PartialMap.insert (LocHeap.asAgree h) l (toAgree v) := by
  refine LawfulPartialMap.equiv_iff_eq.mp fun k => ?_
  by_cases hk : l = k
  · subst hk
    rw [LocHeap.asAgree_get?, LawfulPartialMap.get?_insert_eq rfl,
        LawfulPartialMap.get?_insert_eq rfl]
    rfl
  · rw [LocHeap.asAgree_get?, LawfulPartialMap.get?_insert_ne hk,
        LawfulPartialMap.get?_insert_ne hk, LocHeap.asAgree_get?]

/-- `ExtTreeMap.insert` agrees with the `PartialMap` interface's `insert`. -/
theorem ExtTreeMap.insert_eq_PartialMap_insert {V : Type _}
    (h : LocHeap V) (l : Loc) (v : V) :
    h.insert l v = PartialMap.insert h l v :=
  ExtTreeMap.ext_getElem? fun k => by
    show (h.insert l v)[k]? = (h.alter l (fun _ => some v))[k]?
    simp [ExtTreeMap.getElem?_insert, ExtTreeMap.getElem?_alter]

end StateRA
