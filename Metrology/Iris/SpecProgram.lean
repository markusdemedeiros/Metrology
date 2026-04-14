import Mathlib.Data.ENNReal.Basic
import Iris
import Iris.Algebra.HeapView
import Iris.Instances.IProp.Instance
import Iris.Std.HeapInstances
import Metrology.Iris.Algebra
import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

section SpecRA
open Std Iris Iris.Std COFE ProbLang

instance : COFE Exp := COFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete Exp := ⟨id⟩
instance (x : Exp) : OFE.DiscreteE x := ⟨OFE.Discrete.discrete_0⟩

instance : COFE Tape := COFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete Tape := ⟨id⟩
instance (x : Tape) : OFE.DiscreteE x := ⟨OFE.Discrete.discrete_0⟩

instance : COFE Val := COFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete Val := ⟨id⟩
instance (x : Val) : OFE.DiscreteE x := ⟨OFE.Discrete.discrete_0⟩

instance : LawfulPartialMap LocHeap Loc := sorry

abbrev SpecProg := Option (Excl Exp)
abbrev SpecHeap := HeapView ℕ+ Loc (Agree Val) LocHeap
abbrev SpecTapes := HeapView ℕ+ Loc (Agree Tape) LocHeap

class SpecPreGS (GF : BundledGFunctors) where
  prog : ElemG GF (constOF SpecProg)
  heap : ElemG GF (constOF SpecHeap)
  tapes : ElemG GF (constOF SpecTapes)

attribute [reducible, instance] SpecPreGS.prog SpecPreGS.heap SpecPreGS.tapes

class SpecGS (GF : BundledGFunctors) extends SpecPreGS GF where
  γprog : GName
  γheap : GName
  γtapes : GName

section Resources

variable {GF : BundledGFunctors} [ISpec : SpecGS GF]

end Resources

end SpecRA
