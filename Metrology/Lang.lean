import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Data.Real.Basic
import Metrology.Projections

-- Operational semantics of continuous PPL

abbrev Ident : Type _ := String

@[projections]
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
example (ident_body : Ident × ExprSyntax R Z B) : lam.π (lam.ctor ident_body) = some ident_body := rfl
example (ident_body : Ident × ExprSyntax R Z B) : app.π (lam.ctor ident_body) = none := rfl



-- Define a measure space on these things by lifting

-- def ExprSyntax.lit.ctor (x : LitSyntax R Z B) : ExprSyntax R Z B := .lit x
-- def ExprSyntax.var.ctor (x : Ident) : ExprSyntax R Z B := .var x
-- def ExprSyntax.rand.ctor (_ : Unit) : ExprSyntax R Z B := .rand
-- def ExprSyntax.app.ctor (x : ExprSyntax R Z B × ExprSyntax R Z B) : ExprSyntax R Z B := .app x.1 x.2
-- def ExprSyntax.lam.ctor (x : Ident × ExprSyntax R Z B) : ExprSyntax R Z B := .lam x.1 x.2

-- @[projections]
-- inductive E3 where
-- | ct (x y z : ℝ)
--
-- #check E3.ct.π
-- #check fun (x : ℝ × ℝ × ℝ) => E3.ct x.1 x.2.1 x.2.2





-- -- Automatically define these uncurried constructors (should be easy)
-- -- If we want to use Function.uncurry, we should reassociate the product back to the foldl direction.
-- def MyTree'.nil.ctor : Unit → MyTree' L1 L2 := Function.const _ .nil
-- def MyTree'.leaf1.ctor  : L1 → MyTree' L1 L2 := .leaf1
-- def MyTree'.leaf2.ctor  : L1 × L2 → MyTree' L1 L2 := Function.uncurry .leaf2
-- def MyTree'.branch.ctor  : MyTree' L1 L2 × MyTree' L1 L2 × Nat  → MyTree' L1 L2 :=
--   -- This is why we need to reassociate
--   -- Function.uncurry (Function.uncurry MyTree'.branch)
--   fun (x, y, z) => .branch x y z
--
-- -- The ctor and π functions should be inverses
-- -- #check fun {L1 L2 }(x : MyTree' L1 L2) => (MyTree'.branch.π x) |>.map MyTree'.branch.ctor
--
-- -- #check MyTree'.leaf1
-- -- #check Function.uncurry (Function.uncurry MyTree'.branch)
--
-- def MyTree'.flatten {L1 L2} (ts : MyTree' (Set L1) (Set L2)) : Set (MyTree' L1 L2) :=
--     let π_nil : Set (MyTree' L1 L2) :=
--       MyTree'.nil.π ts |>.map (fun _ => {nil}) |>.getD ∅
--     let π_leaf1 : Set (MyTree' L1 L2):=
--       MyTree'.leaf1.π ts |>.map (fun f1 => sorry) |>.getD ∅
--
--
--     -- let π_leaf1 := MyTree'.leaf1.π go
--     -- let π_leaf2 := MyTree'.leaf2.π go
--     -- let π_branch := MyTree'.branch.π go
--
--     -- If it's none, then return Set.empty
--     -- If it's some, then
--     --     - Apply flatten to all recursive cases
--     --     - Take the singleton set for all non-recursive, non-parameter cases
--     --     - Take the set itself for all parameter cases
--     --     - Define the preimage of (Some (prod. of sets.)) under the projection function
--     -- The preimage is the union of these sets
--     -- Could also do a dummy match on the go arguent
--
--     sorry
--     -- Set.union { nil } <|
--     -- Set.union { leaf1 l | l ∈ Set.univ } <|
--     -- Set.union { leaf1 l | l ∈ Set.univ } <|
--   --           { leaf1 l | l ∈ Set.univ }
