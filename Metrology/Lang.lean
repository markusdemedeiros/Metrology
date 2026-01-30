import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Data.Real.Basic
import Metrology.Projections

-- Operational semantics of continuous PPL

abbrev Ident : Type _ := String

@[projections, constructors]
inductive LitSyntax (R Z B : Type _) where
| real (r : R)
| int (z : Z)
| bool (b : B)
deriving Repr

@[projections, constructors]
inductive ExprSyntax R Z B where
| rand
| lit (l : LitSyntax R Z B)
| var (x : Ident)
| app (rator rand : ExprSyntax R Z B)
| lam (x : Ident) (body : ExprSyntax R Z B)
deriving Repr

open ExprSyntax
example (ident_body : Ident × ExprSyntax R Z B) : lam.π (lam.ι ident_body) = some ident_body := rfl
example (ident_body : Ident × ExprSyntax R Z B) : app.π (lam.ι ident_body) = none := rfl

-- For any base argument (one of the Sets mentioned as a paramater to the inductive),
-- take the image of the constructor
def LitSyntax.flatten : LitSyntax (Set R) (Set Z) (Set B) → Set (LitSyntax R Z B)
| real S => Set.image LitSyntax.real.ι S
| int S => Set.image LitSyntax.int.ι S
| bool S => Set.image LitSyntax.bool.ι S

def ExprSyntax.flatten : ExprSyntax (Set R) (Set Z) (Set B) → Set (ExprSyntax R Z B)
-- Because rand has no arguments, its flattening is the image of the singleton unit set.
| rand => Set.image ExprSyntax.rand.ι { () }
-- To flatten lit, whose argument is a LitSyntax, which also has a flattening procedure.
-- So first, we flatten its argument, and then take the preimage under the lit projection.
| lit l => Set.image ExprSyntax.lit.ι (LitSyntax.flatten l)
-- Variables do not have flattening. So we take the image of a singleton set.
| var x => Set.image ExprSyntax.var.ι { x }
-- Applications have two flattenable arguments. We take their product, before taking their image.
| app fn arg => Set.image ExprSyntax.app.ι (Set.prod (ExprSyntax.flatten fn) (ExprSyntax.flatten arg))
-- The first argument is not flattenable, the second argument is. So it's the image of the
-- product of the singleton set and the flattened set.
| lam x body => Set.image ExprSyntax.lam.ι (Set.prod { x } (ExprSyntax.flatten body))
