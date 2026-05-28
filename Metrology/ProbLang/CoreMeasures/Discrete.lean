module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax

meta import Metrology.Meta

@[expose] public section

noncomputable section ProbLangMeasures

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

instance instMeasurableSpaceVar : MeasurableSpace Var := ⊤

instance instMeasurableSpaceLoc : MeasurableSpace Loc := ⊤

instance instMeasurableSpaceLbl : MeasurableSpace Lbl := ⊤

instance instMeasurableSpaceUnOp : MeasurableSpace UnOp := ⊤

instance instMeasurableSpaceBinOp : MeasurableSpace BinOp := ⊤

instance instMeasurableSpaceTy : MeasurableSpace Ty := ⊤

end ProbLangMeasures
