import MicroCircuit.GarbleGen

/-! ## Base implementation for circuit garbling
- Point-and-permute
- OTP Encryption
-/

abbrev Key := Nat

namespace Key

def colour (k : Key) : Bool := k &&& 1 == 1

def set_colour (k : Key) (b : Bool) : Key :=
  (0xFFFFFFFE &&& k) ||| b.toNat

/-- Generate a random 128-bit key. -/
def gen : IO Key := IO.rand 0 ((2 ^ 128) - 1)

/-- Generate a key pair for a wire: two 128-bit keys with opposite LSBs. -/
def gen_colour_pair : IO (Key × Key) := do
  let ka ← gen
  let kb ← gen
  return (ka, kb.set_colour !ka.colour)

def encrypt (k : Key) (p : Nat) : Nat := k ^^^ p

def decrypt (k : Key) (c : Nat) : Nat := k ^^^ c

def nil : Key := 0

end Key

def Table (α : Type _) : Type _ := α × α × α × α

namespace Table

def set (t : Table α) (ci cj : Bool) (v : α) : Table α :=
  let ⟨t00, t01, t10, t11⟩ := t
  match ci, cj with
  | false, false => ⟨v, t01, t10, t11⟩
  | false, true  => ⟨t00, v, t10, t11⟩
  | true, false  => ⟨t00, t01, v, t11⟩
  | true, true   => ⟨t00, t01, t10, v⟩

def get (t : Table α) (ci cj : Bool) : α :=
  let ⟨t00, t01, t10, t11⟩ := t
  match ci, cj with
  | false, false => t00
  | false, true  => t01
  | true, false  => t10
  | true, true   => t11

end Table

section Garbling

structure GarbleState where
  /-- Keys representing False -/
  key_false : Array Key
  /-- Keys representing True -/
  key_true : Array Key
  /-- List of garbled tables so far -/
  tables : Array (Table Key)

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

def pushTable (t : Table Key) : GarbleM Unit :=
  modify fun s => { s with tables := s.tables.push t }

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
    | .And wA wB => pushTable <| garbleGateTable4 (s.keyFor wA) (s.keyFor wB) kk (· && ·)
    | .Xor wA wB => pushTable <| garbleGateTable4 (s.keyFor wA) (s.keyFor wB) kk (· ^^ ·)
    | .Not wA    => pushTable <| garbleGateTable2 (s.keyFor wA) kk (! ·)
    | .Const0    => pushTable <| ⟨kk false, 0, 0, 0⟩
    | .Const1    => pushTable <| ⟨kk true, 0, 0, 0⟩

instance : Inhabited Gate := ⟨{ prim := .Const0, id := 0 }⟩
instance : Inhabited (Table Key) := ⟨(0, 0, 0, 0)⟩

/-- Given input labels, iteratively decrypt the table to obtain the final array of keys -/
def evalGarbledCircuit (c : Circuit) (tables : Array (Table Key)) (inputLabels : Array Key) :
    Array Key := Id.run do
  let mut wireStates := inputLabels
  for i in [:c.size] do
    let g := c[i]!
    let t := tables[i]!
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

end Garbling
