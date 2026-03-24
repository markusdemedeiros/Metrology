import MicroCircuit.GarbleGen
import MicroCircuit.Common

namespace BasicGarbling

/-! ## Base implementation for circuit garbling
- Point-and-permute
- OTP Encryption
-/

inductive GarbledGate
| And (t : Table Key)
| Xor (t : Table Key)
| Not (t : Table Key)
| Const0 (t : Table Key)
| Const1 (t : Table Key)

structure GarbleState where
  /-- Keys representing False -/
  key_false : Array Key
  /-- Keys representing True -/
  key_true : Array Key
  /-- List of garbled tables so far -/
  tables : Array GarbledGate
  /-- Running count of ciphertexts emitted -/
  numCiphertexts : Nat := 0

abbrev GarbleM := StateT GarbleState IO

/-- Generate a key pair for a specific wire ID (may be called in any order). -/
def GarbleM.genKeysFor (wireId : Nat) : GarbleM Unit := do
  let (kf, kt) ← Key.gen_colour_pair
  modify fun s => { s with
    key_false := s.key_false.set! wireId kf
    key_true := s.key_true.set! wireId kt }

/-- (Secret) Get the true or false key for a given WireId -/
def GarbleState.keyFor (s : GarbleState) (wireId : Nat) (b : Bool) : Key :=
  if b then s.key_true[wireId]! else s.key_false[wireId]!

/-- Garble a single gate's truth table f. ki, kj, kk are functions mapping truth values to keys.
The table is arranged by the colour bits of the keys. -/
def garbleGateTable4 (ki kj kk : Bool → Key) (f : Bool → Bool → Bool) : Table Key := Id.run do
  let mut t : Table Key := ⟨0, 0, 0, 0⟩
  for vi in [false, true] do
    for vj in [false, true] do
      let ci := (ki vi).colour
      let cj := (kj vj).colour
      t := t.set ci cj <| (ki vi).encrypt <| (kj vj).encrypt <| kk (f vi vj)
  return t

def garbleGateTable2 (ki kk : Bool → Key) (f : Bool → Bool) : Table Key := Id.run do
  let mut t : Table Key := ⟨0, 0, 0, 0⟩
  for vi in [false, true] do
    let ci := (ki vi).colour
    t := t.set ci false <| (ki vi).encrypt <| kk (f vi)
  return t

/-- Evaluate one garbled gate: indexing by the color bits of the input labels. -/
def evalGarbledGate (li lj : Key) (t : Table Key) : Key :=
  li.decrypt <| lj.decrypt <| t.get li.colour lj.colour

def pushTable (t : GarbledGate) (ct : Nat) : GarbleM Unit :=
  modify fun s => { s with tables := s.tables.push t, numCiphertexts := s.numCiphertexts + ct }

/-- Garble an entire circuit. -/
def garbleCircuit (c : Circuit) (numInputs : Nat) : GarbleM Unit := do
  let mut outWire := numInputs
  for g in c do
    -- Generate the keys for the current output wire
    GarbleM.genKeysFor outWire
    let s ← get
    let kk := s.keyFor outWire
    outWire := outWire + 1
    -- Garble the gate and push it to the circuit.
    match g.prim with
    | .And wA wB => pushTable (.And <| garbleGateTable4 (s.keyFor wA) (s.keyFor wB) kk (· && ·)) 4
    | .Xor wA wB => pushTable (.Xor <| garbleGateTable4 (s.keyFor wA) (s.keyFor wB) kk (· ^^ ·)) 4
    | .Not wA    => pushTable (.Not <| garbleGateTable2 (s.keyFor wA) kk (! ·)) 2
    | .Const0    => pushTable (.Const0 <| ⟨kk false, 0, 0, 0⟩) 1
    | .Const1    => pushTable (.Const1 <| ⟨kk true, 0, 0, 0⟩) 1

instance : Inhabited Gate := ⟨{ prim := .Const0, id := 0 }⟩
instance : Inhabited (Table Key) := ⟨(0, 0, 0, 0)⟩
instance : Inhabited GarbledGate := ⟨.And default⟩

/-- Given input labels, iteratively decrypt the table to obtain the final array of keys -/
def evalGarbledCircuit (c : Circuit) (tables : Array GarbledGate) (inputLabels : Array Key) :
    Array Key := Id.run do
  let mut wireStates := inputLabels
  for i in [:c.size] do
    let g := c[i]!
    let t : Table Key :=
      match (tables[i]! : GarbledGate)  with | .And t | .Xor t | .Not t | .Const0 t | .Const1 t => t
    let lk := match g.prim with
      | GateT.And wA wB => evalGarbledGate wireStates[wA]! wireStates[wB]! t
      | GateT.Xor wA wB => evalGarbledGate wireStates[wA]! wireStates[wB]! t
      | GateT.Not wA => evalGarbledGate wireStates[wA]! .nil t
      | GateT.Const0 => t.get false false
      | GateT.Const1 => t.get false false
    wireStates := wireStates.push lk
  return wireStates

/-- Point-and-permute garbling with XOR one-time pad. -/
instance : GarblingScheme Key GarbleState where
  garble c numInputs := do
    let pairs ← (Array.range numInputs).mapM (fun _ => Key.gen_colour_pair)
    let initState : GarbleState :=
      { key_false := pairs.map (·.1) ++ Array.replicate c.size 0
        key_true  := pairs.map (·.2) ++ Array.replicate c.size 0
        tables := #[] }
    let (_, s) ← (garbleCircuit c numInputs) |>.run initState
    return s

  inputLabel s wireId v := s.keyFor wireId v

  eval s c inputLabels := evalGarbledCircuit c s.tables inputLabels

  decodeOutput s wireId label := label == s.keyFor wireId true

  numCiphertexts s := s.numCiphertexts

end BasicGarbling
