import MicroCircuit.GarbleGen

/-! ## Circuit garbling with point-and-permute (BMR90)

The permute bit is derived as the LSB of each wire key.
Keys for a wire are chosen so that key_true and key_false have opposite LSBs.
Encryption is XOR one-time pad: ciphertext = plaintext XOR k1 XOR k2.
-/

/-- A 128-bit key. -/
abbrev Key := Nat

/-- The permute (color) bit of a key is its LSB. -/
def Key.color (k : Key) : Bool := k &&& 1 == 1

/-- Generate a random 128-bit key. -/
def keygen : IO Key := IO.rand 0 ((2 ^ 128) - 1)

/-- Generate a key pair for a wire: two 128-bit keys with opposite LSBs. -/
def keygenPair : IO (Key × Key) := do
  let ka ← keygen
  let kb ← keygen
  -- Strip off the last bit of kb, and replace it with the negated last bit of ka.
  return (ka, (0xFFFFFFFE &&& kb) ||| (0x1 ^^^ (0x1 &&& ka)))

section Garbling

/-- A wire label: just the key. The permute bit is `key.color` (the LSB). -/
abbrev WireLabel := Key

/-- Encrypt a 128-bit payload under two keys using XOR one-time pad. -/
def encrypt (k1 k2 : Key) (payload : Key) : Key :=
  payload ^^^ k1 ^^^ k2

def decrypt (k1 k2 : Key) (cipher : Key) : Key :=
  cipher ^^^ k1 ^^^ k2

def Table (α : Type _) : Type _ := α × α × α × α

def Table.set (t : Table α) (ci cj : Bool) (v : α) : Table α :=
  let ⟨t00, t01, t10, t11⟩ := t
  match ci, cj with
  | false, false => ⟨v, t01, t10, t11⟩
  | false, true  => ⟨t00, v, t10, t11⟩
  | true, false  => ⟨t00, t01, v, t11⟩
  | true, true   => ⟨t00, t01, t10, v⟩

def Table.get (t : Table α) (ci cj : Bool) : α :=
  let ⟨t00, t01, t10, t11⟩ := t
  match ci, cj with
  | false, false => t00
  | false, true  => t01
  | true, false  => t10
  | true, true   => t11

structure GarbleState where
  /-- Keys representing False -/
  key_false : Array Key
  /-- Keys representing True -/
  key_true : Array Key
  /-- Garbled tables, one per gate -/
  tables : Array (Table Key)

abbrev GarbleM := StateT GarbleState IO

def GarbleState.keyFor (s : GarbleState) (wireId : Nat) (b : Bool) : Key :=
  if b then s.key_true[wireId]! else s.key_false[wireId]!

/-- Garble a single gate's truth table.
    ki, kj : functions returning the key for input wires given the truth value
    kk : function returning the key for the output wire given the truth value
    f : the gate's boolean function -/
def garbleGateTable (ki kj kk : Bool → Key) (f : Bool → Bool → Bool) : Table Key := Id.run do
  let mut t : Table Key := ⟨0, 0, 0, 0⟩
  for vi in [false, true] do
    for vj in [false, true] do
      let ci := (ki vi).color
      let cj := (kj vj).color
      let vk := f vi vj
      let payload := kk vk
      t := t.set ci cj (encrypt (ki vi) (kj vj) payload)
  return t

/-- Evaluate one garbled gate: use the color bits of the input labels
    to index into the table, then decrypt. -/
def evalGarbledGate (li lj : WireLabel) (t : Table Key) : WireLabel :=
  decrypt li lj (t.get li.color lj.color)

/-- Garble an entire circuit. -/
def garbleCircuit (c : Circuit) : GarbleM Unit := do
  for g in c do
    let (kf, kt) ← keygenPair
    -- Record keys for the output wire
    modify fun s => { s with
      key_false := s.key_false.push kf
      key_true := s.key_true.push kt }
    let s ← get
    -- Build the garbled table
    match g.prim with
    | .And wA wB =>
      let ki := s.keyFor wA
      let kj := s.keyFor wB
      let kk := s.keyFor g.id
      let t := garbleGateTable ki kj kk (· && ·)
      modify fun s => { s with tables := s.tables.push t }
    | .Xor wA wB =>
      let ki := s.keyFor wA
      let kj := s.keyFor wB
      let kk := s.keyFor g.id
      let t := garbleGateTable ki kj kk (· ^^ ·)
      modify fun s => { s with tables := s.tables.push t }
    | .Not wA =>
      -- NOT as a 1-input gate: we make a degenerate 2×1 table
      -- Index by color of wA only; second index is always false
      let ki := s.keyFor wA
      let kk := s.keyFor g.id
      let mut t : Table Key := ⟨0, 0, 0, 0⟩
      for vi in [false, true] do
        let ci := (ki vi).color
        let payload := kk (!vi)
        t := t.set ci false (encrypt (ki vi) 0 payload)
      modify fun s => { s with tables := s.tables.push t }
    | .Const0 =>
      -- No table needed, but push a dummy to keep indexing aligned
      let kk := s.keyFor g.id
      -- The "garbled table" for a constant is just the false-key encrypted with nothing
      modify fun s => { s with tables := s.tables.push ⟨kk false, 0, 0, 0⟩ }
    | .Const1 =>
      let kk := s.keyFor g.id
      modify fun s => { s with tables := s.tables.push ⟨kk true, 0, 0, 0⟩ }

/-- Evaluate a garbled circuit given input wire labels. -/
instance : Inhabited Gate := ⟨{ prim := .Const0, id := 0 }⟩
instance : Inhabited (Table Key) := ⟨(0, 0, 0, 0)⟩

def evalGarbledCircuit (c : Circuit) (tables : Array (Table Key))
    (inputLabels : Array WireLabel) : Array WireLabel := Id.run do
  let mut labels := inputLabels
  for i in [:c.size] do
    let g := c[i]!
    let t := tables[i]!
    let lk := match g.prim with
      | GateT.And wA wB => evalGarbledGate labels[wA]! labels[wB]! t
      | GateT.Xor wA wB => evalGarbledGate labels[wA]! labels[wB]! t
      | GateT.Not wA =>
        let la := labels[wA]!
        decrypt la 0 (t.get (Key.color la) false)
      | GateT.Const0 => t.get false false
      | GateT.Const1 => t.get false false
    labels := labels.push lk
  return labels

/-- Read an output wire's truth value by checking which key it matches. -/
def readOutput (s : GarbleState) (wireId : Nat) (label : WireLabel) : Bool :=
  label == s.keyFor wireId true

/-- Point-and-permute garbling with XOR one-time pad. -/
instance : GarblingScheme Key (Table Key) where
  garble c numInputs := do
    let mut initState : GarbleState := { key_false := #[], key_true := #[], tables := #[] }
    for _ in [:numInputs] do
      let (k0, k1) ← keygenPair
      initState := { initState with
        key_false := initState.key_false.push k0
        key_true := initState.key_true.push k1 }
    let ((), s) ← garbleCircuit c |>.run initState
    return { key_false := s.key_false, key_true := s.key_true, tables := s.tables }

  eval c tables inputLabels :=
    evalGarbledCircuit c tables inputLabels

  readOutput label trueLabel :=
    label == trueLabel

end Garbling
