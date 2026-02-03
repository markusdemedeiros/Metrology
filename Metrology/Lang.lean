import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Data.Real.Basic
import Metrology.Projections

-- Operational semantics of continuous PPL

abbrev Ident : Type _ := String

-- /- Typeclass containing all of the information necessary to perform the cylinder
--     construction on syntax. -/
class MeasurableSyntax (Syntax : Type _) (Gen : outParam (Type _)) where
  base : Set Gen
  flatten : Gen → Set Syntax

def MeasurableSyntax.cylinder [I : MeasurableSyntax Syntax Gen] : Set (Set Syntax) :=
  I.flatten '' I.base

instance MeasurableSyntax.instMeasurableSpace [MeasurableSyntax Syntax Gen] : MeasurableSpace Syntax :=
  MeasurableSpace.generateFrom cylinder

@[projections, constructors]
inductive LitSyntax (R Z B : Type _) where
| real (r : R)
| int (z : Z)
| bool (b : B)

-- For any base argument (one of the Sets mentioned as a paramater to the inductive),
-- take the image of the constructor
def LitSyntax.flatten : LitSyntax (Set R) (Set Z) (Set B) → Set (LitSyntax R Z B)
| .real S => LitSyntax.real.ι '' S
| .int S => LitSyntax.int.ι '' S
| .bool S => LitSyntax.bool.ι '' S

def LitSyntax.base [MeasurableSpace R] [MeasurableSpace Z] [MeasurableSpace B] :
  Set (LitSyntax (Set R) (Set Z) (Set B))
| .real S => MeasurableSet S
| .int S => MeasurableSet S
| .bool S => MeasurableSet S

instance [MeasurableSpace R] [MeasurableSpace Z] [MeasurableSpace B] :
    MeasurableSyntax (LitSyntax R Z B) (LitSyntax (Set R) (Set Z) (Set B)) where
  base := LitSyntax.base
  flatten := LitSyntax.flatten

-- abbrev LitSyntax.Shape : Type _ := LitSyntax Unit Unit Unit
-- abbrev LitSyntax.Pre (R Z B : Type _) : Type _ := LitSyntax (Set R) (Set Z) (Set B)

@[projections, constructors]
inductive ExprSyntax R Z B where
| rand
| lit (l : LitSyntax R Z B)
| var (x : Ident)
| app (rator rand : ExprSyntax R Z B)
| lam (x : Ident) (body : ExprSyntax R Z B)

def ExprSyntax.flatten : ExprSyntax (Set R) (Set Z) (Set B) → Set (ExprSyntax R Z B)
-- Because rand has no arguments, its flattening is the image of the singleton unit set.
| rand => ExprSyntax.rand.ι '' { () }
-- To flatten lit, whose argument is a LitSyntax, which also has a flattening procedure.
-- So first, we flatten its argument, and then take the preimage under the lit projection.
| lit l => ExprSyntax.lit.ι '' (LitSyntax.flatten l)
-- Variables do not have flattening. So we take the image of a singleton set.
| var x => ExprSyntax.var.ι '' { x }
-- Applications have two flattenable arguments. We take their product, before taking their image.
| app fn arg => ExprSyntax.app.ι '' (Set.prod (ExprSyntax.flatten fn) (ExprSyntax.flatten arg))
-- The first argument is not flattenable, the second argument is. So it's the image of the
-- product of the singleton set and the flattened set.
| lam x body => Set.image ExprSyntax.lam.ι (Set.prod { x } (ExprSyntax.flatten body))

def ExprSyntax.base [MeasurableSpace R] [MeasurableSpace Z] [MeasurableSpace B] :
  Set (ExprSyntax (Set R) (Set Z) (Set B))
| rand => True
| lit S => MeasurableSyntax.base (LitSyntax R Z B) S
| var _ => True
| app fn arg => base fn ∧ base arg
| lam _ body => base body

instance [MeasurableSpace R] [MeasurableSpace Z] [MeasurableSpace B] :
    MeasurableSyntax (ExprSyntax R Z B) (ExprSyntax (Set R) (Set Z) (Set B)) where
  base := ExprSyntax.base
  flatten := ExprSyntax.flatten

open ExprSyntax
example (ident_body : Ident × ExprSyntax R Z B) : lam.π (lam.ι ident_body) = some ident_body := rfl
example (ident_body : Ident × ExprSyntax R Z B) : app.π (lam.ι ident_body) = none := rfl
