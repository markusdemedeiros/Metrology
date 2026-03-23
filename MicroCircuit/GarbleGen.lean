import MicroCircuit.Circuits

/-! ## Generic garbling scheme interface

A `GarblingScheme` abstracts over:
- The wire label type (keys held by the evaluator)
- The garbled table type (one per gate)
- How to garble a circuit, evaluate a garbled circuit, and read outputs
-/

/-- State for garbling a circuit under any scheme. -/
structure GenGarbleState (Label GTable : Type) where
  key_false : Array Label
  key_true  : Array Label
  tables    : Array GTable

def GenGarbleState.keyFor [Inhabited Label] (s : GenGarbleState Label GTable) (wireId : Nat) (b : Bool) : Label :=
  if b then s.key_true[wireId]! else s.key_false[wireId]!

/-- A garbling scheme parameterized by the wire label and garbled table types. -/
class GarblingScheme (Label : Type) (GTable : Type) where
  /-- Garble an entire circuit, producing the garble state (keys + tables).
      `numInputs` is the number of input wires (keys are generated for these first). -/
  garble (c : Circuit) (numInputs : Nat) : IO (GenGarbleState Label GTable)

  /-- Evaluate a garbled circuit given input labels and the garbled tables. -/
  eval (c : Circuit) (tables : Array GTable) (inputLabels : Array Label) : Array Label

  /-- Determine the truth value of an output wire by comparing the label
      against the true-label. -/
  readOutput (label trueLabel : Label) : Bool
