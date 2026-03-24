import MicroCircuit.Circuits

/-! ## Generic garbling scheme interface

A `GarblingScheme` abstracts over:
- The wire label type (held by the evaluator)
- An opaque garble state type (held by the garbler)
- How to garble, evaluate, encode inputs, and decode outputs
-/

class GarblingScheme (Label : Type) (State : Type) where
  /-- Garble an entire circuit with `numInputs` input wires. -/
  garble (c : Circuit) (numInputs : Nat) : IO State

  /-- Get the input label for a given wire and truth value (garbler-side). -/
  inputLabel (s : State) (wireId : Nat) (v : Bool) : Label

  /-- Evaluate a garbled circuit given input labels (evaluator-side). -/
  eval (s : State) (c : Circuit) (inputLabels : Array Label) : Array Label

  /-- Decode the truth value of an output wire (garbler-side). -/
  decodeOutput (s : State) (wireId : Nat) (label : Label) : Bool

  /-- Number of ciphertexts in the garbled circuit. -/
  numCiphertexts (s : State) : Nat
