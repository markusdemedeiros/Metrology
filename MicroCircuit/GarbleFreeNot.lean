import MicroCircuit.GarbleGen
import MicroCircuit.Common

namespace FreeNotGarbling

/-! ## Base implementation for circuit garbling
- Point-and-permute
- OTP Encryption
- Free NOT optimization
-/

inductive GarbledGate
| And (t : Table Key)
| Xor (t : Table Key)
| Not
| Const (k : Key)

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
    if let .Not wA := g.prim
      then
        -- For a not gate, set the keys to be the swapped keys for the input wire
        let kA := (← get).keyFor wA
        modify fun s => { s with
          key_false := s.key_false.set! outWire (kA true)
          key_true := s.key_true.set! outWire (kA false) }
      else
        -- Generate new keys for the current output wire
        GarbleM.genKeysFor outWire

    let s ← get
    let kk := s.keyFor outWire
    outWire := outWire + 1

    -- Garble the gate and push it to the circuit.
    match g.prim with
    | .And wA wB => pushTable (.And <| garbleGateTable4 (s.keyFor wA) (s.keyFor wB) kk (· && ·)) 4
    | .Xor wA wB => pushTable (.Xor <| garbleGateTable4 (s.keyFor wA) (s.keyFor wB) kk (· ^^ ·)) 4
    | .Not _     => pushTable .Not 0
    | .Const0    => pushTable (.Const (kk false)) 1
    | .Const1    => pushTable (.Const (kk true)) 1

instance : Inhabited Gate := ⟨{ prim := .Const0, id := 0 }⟩
instance : Inhabited (Table Key) := ⟨(0, 0, 0, 0)⟩
instance : Inhabited GarbledGate := ⟨.And default⟩

/-- Given input labels, iteratively decrypt the table to obtain the final array of keys -/
def evalGarbledCircuit (c : Circuit) (tables : Array GarbledGate) (inputLabels : Array Key) :
    Array Key := Id.run do
  let mut wireStates := inputLabels
  for i in [:c.size] do
    let g := c[i]!
    let lk := match g.prim, tables[i]! with
      | GateT.And wA wB, .And t => evalGarbledGate wireStates[wA]! wireStates[wB]! t
      | GateT.Xor wA wB, .Xor t => evalGarbledGate wireStates[wA]! wireStates[wB]! t
      -- Not evaluates by id, because from here on out, any gates will have been garbled
      -- as if this meant the opposite of what it did before.
      | GateT.Not wA, .Not => wireStates[wA]!
      | GateT.Const0, .Const k => k
      | GateT.Const1, .Const k => k
      | _, _ => panic! "Bad circuit"
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

end FreeNotGarbling
