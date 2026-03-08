import Metrology.ProbLang.Syntax

/-! # Fragment abstraction for ProbLang

A `Fragment` is a Type-valued predicate on `Exp`. Pairing an expression with
a witness (`FragExp F`) auto-eliminates impossible match branches.

Based on experiments in `Scratch/Sublang3.lean`.

`IsVal` (the first concrete fragment) and `Val := FragExp IsVal` live in
`Syntax.lean` since they are used pervasively.
-/

namespace ProbLang

-------------------------------------------------------------------------------
-- Fragment = Type-valued predicate on Exp
-------------------------------------------------------------------------------

abbrev Fragment := Exp → Type

-- A "fragment expression" is an Exp paired with a witness
abbrev FragExp (F : Fragment) := (e : Exp) × F e

-------------------------------------------------------------------------------
-- Combinators
-------------------------------------------------------------------------------

-- Intersection: e must be in both F and G
def Both (F G : Fragment) : Fragment := fun e => F e × G e

-- Union: e must be in at least one of F or G
-- (Sum is Type-valued, so eliminable)
def Either (F G : Fragment) : Fragment := fun e => F e ⊕ G e

-- Trivially true fragment: everything is in it
def Any : Fragment := fun _ => Unit

-- Empty fragment: nothing is in it
def None : Fragment := fun _ => Empty

-- Overlay: adds metadata on top of another fragment
def Overlay (F : Fragment) (M : Exp → Type) : Fragment := fun e => F e × M e

-------------------------------------------------------------------------------
-- Morphisms between fragments
-------------------------------------------------------------------------------

-- A fragment morphism: F is a subfragment of G
def SubFrag (F G : Fragment) := ∀ e, F e → G e

-- Notation
scoped infixr:25 " ⊆f " => SubFrag

-- Identity
def SubFrag.id : F ⊆f F := fun _ x => x

-- Composition
def SubFrag.comp (f : F ⊆f G) (g : G ⊆f H) : F ⊆f H := fun e x => g e (f e x)

-- Lift a morphism to FragExp
def SubFrag.map (f : F ⊆f G) : FragExp F → FragExp G
  | ⟨e, w⟩ => ⟨e, f e w⟩

-------------------------------------------------------------------------------
-- Erasure and checked injection
-------------------------------------------------------------------------------

def FragExp.erase : FragExp F → Exp := Sigma.fst

class Checkable (F : Fragment) where
  check? : (e : Exp) → Option (F e)

def FragExp.mk? [Checkable F] (e : Exp) : Option (FragExp F) :=
  (Checkable.check? e).map (⟨e, ·⟩)

instance [Checkable F] [Checkable G] : Checkable (Both F G) where
  check? e := do return (← Checkable.check? e, ← Checkable.check? e)

-------------------------------------------------------------------------------
-- IsVal as a fragment (defined in Syntax.lean, instances here)
-------------------------------------------------------------------------------

instance : Checkable IsVal where check? := IsVal.check?

end ProbLang
