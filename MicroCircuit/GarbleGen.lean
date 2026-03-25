import MicroCircuit.Circuits

/-! ## Generic garbling scheme interface

A `GarblingScheme` abstracts over:
- The wire label type (held by the evaluator)
- An opaque garble state type (held by the garbler)
- How to garble, evaluate, encode inputs, and decode outputs
-/

structure GarblingScheme (Label : Type) (State : Type) where
  /-- Preprocess a circuit before garbling (e.g. optimization passes). -/
  preprocess : Nat → Circuit → Circuit := fun _ => id

  /-- Garble an entire circuit with `numInputs` input wires. -/
  garble : Circuit → Nat → IO State

  /-- Get the input label for a given wire and truth value (garbler-side). -/
  inputLabel : State → Nat → Bool → Label

  /-- Evaluate a garbled circuit given input labels (evaluator-side). -/
  eval : State → Circuit → Array Label → Array Label

  /-- Decode the truth value of an output wire (garbler-side). -/
  decodeOutput : State → Nat → Label → Bool

  /-- Number of ciphertexts in the garbled circuit. -/
  numCiphertexts : State → Nat

def GarblingScheme.withPP (s : GarblingScheme L S) (f : Nat → Circuit → Circuit) : GarblingScheme L S :=
  { s with preprocess := fun n c => f n (s.preprocess n c) }
