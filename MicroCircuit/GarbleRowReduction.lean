import MicroCircuit.GarbleGen
import MicroCircuit.Common

namespace GRR3Garbling

/-! ## Base implementation for circuit garbling
- Point-and-permute
- OTP Encryption
- Free NOT optimization
- Free XOR optimization
- GRR3 Row Reduction
-/

inductive GarbledGate
| And (t : Table Key)
| Xor
| Not
| Const (k : Key)

structure GarbleState where
  key_true : Array Key
  key_Δ : Key
  tables : Array GarbledGate
  numCiphertexts : Nat := 0

abbrev GarbleM := StateT GarbleState IO

def GarbleM.genKeysFor (wireId : Nat) : GarbleM Unit := do
  let kt ← Key.gen
  modify fun s => { s with key_true := s.key_true.set! wireId kt }

def GarbleState.keyFor (s : GarbleState) (wireId : Nat) (b : Bool) : Key :=
  let k := s.key_true[wireId]!
  if b then k else k ^^^ s.key_Δ

/-- Select the key that has colour `true` -/
def GarbleState.keyColourTrue (s : GarbleState) (wireId : Nat) : Key :=
  let k := s.keyFor wireId true
  if k.colour == true then k else s.keyFor wireId false

def garbleGateTable4 (ki kj kk : Bool → Key) (f : Bool → Bool → Bool) : Table Key := Id.run do
  let mut t : Table Key := ⟨0, 0, 0, 0⟩
  for vi in [false, true] do
    for vj in [false, true] do
      let ci := (ki vi).colour
      let cj := (kj vj).colour
      t := t.set ci cj <| (ki vi).encrypt <| (kj vj).encrypt <| kk (f vi vj)
  return t

def garbleReducedAnd (ki kj kk : Bool → Key) (f : Bool → Bool → Bool) : Table Key := Id.run do
  let mut t : Table Key := ⟨.nil, .nil, .nil, .nil⟩
  for vi in [false, true] do
    for vj in [false, true] do
      let ci := (ki vi).colour
      let cj := (kj vj).colour
      -- The (true, true) colour entry is the eliminated row — leave as nil
      if !(ci && cj) then
        t := t.set ci cj <| (ki vi).encrypt <| (kj vj).encrypt <| kk (f vi vj)
  return t

def evalGarbledGate (li lj : Key) (t : Table Key) : Key :=
  li.decrypt <| lj.decrypt <| t.get li.colour lj.colour

-- When evaluating a reduced AND table, the (true, true) colour entry stores Key.nil;
-- decrypt it normally (the garbler chose the output key to make this work).
def evalReducedAnd (li lj : Key) (t : Table Key) : Key :=
  li.decrypt <| lj.decrypt <| t.get li.colour lj.colour

def pushTable (t : GarbledGate) (ct : Nat) : GarbleM Unit :=
  modify fun s => { s with tables := s.tables.push t, numCiphertexts := s.numCiphertexts + ct }

/-- Garble an entire circuit. -/
def garbleCircuit (c : Circuit) (numInputs : Nat) : GarbleM Unit := do
  let mut outWire := numInputs
  for g in c do
    match g.prim with
    | .Not wA => do
        let kA := (← get).keyFor wA
        modify fun s => { s with key_true := s.key_true.set! outWire (kA false) }
    | .Xor wA wB => do
        let s ← get
        let kC := s.key_true[wA]! ^^^ s.key_true[wB]! ^^^ s.key_Δ
        modify fun s => { s with key_true := s.key_true.set! outWire kC }
    | .And wA wB => do
        -- GRR3: Choose the output key so the (colour-true, colour-true) row decrypts to nil.
        let s ← get
        let kA := s.keyColourTrue wA
        let kB := s.keyColourTrue wB
        -- kC is the output key for the eliminated row
        let kC := kA.decrypt <| kB.decrypt Key.nil
        -- What truth values do the colour-true keys represent?
        let va := s.keyFor wA true == kA
        let vb := s.keyFor wB true == kB
        -- kC corresponds to output value (va && vb)
        -- Now we have to pick if kC means true or false.
        -- If kA and kB are both the keys for true, then kC is the key for true
        -- Otherwise, kC is the key for false, so the key for true is kC xor Δ.
        let kTrue := if va && vb then kC else kC ^^^ s.key_Δ
        modify fun s => { s with key_true := s.key_true.set! outWire kTrue }
    | _ =>  GarbleM.genKeysFor outWire

    let s ← get
    let kk := s.keyFor outWire
    outWire := outWire + 1

    -- Garble the gate and push it to the circuit.
    match g.prim with
    | .And wA wB => pushTable (.And <| garbleReducedAnd (s.keyFor wA) (s.keyFor wB) kk (· && ·)) 3
    | .Xor _ _   => pushTable .Xor 0
    | .Not _     => pushTable .Not 0
    | .Const0    => pushTable (.Const (kk false)) 1
    | .Const1    => pushTable (.Const (kk true)) 1

instance : Inhabited Gate := ⟨{ prim := .Const0, id := 0 }⟩
instance : Inhabited (Table Key) := ⟨(0, 0, 0, 0)⟩
instance : Inhabited GarbledGate := ⟨.And default⟩

def evalGarbledCircuit (c : Circuit) (tables : Array GarbledGate) (inputLabels : Array Key) :
    Array Key := Id.run do
  let mut wireStates := inputLabels
  for i in [:c.size] do
    let g := c[i]!
    let lk := match g.prim, tables[i]! with
      | GateT.And wA wB, .And t => evalReducedAnd wireStates[wA]! wireStates[wB]! t
      -- Here, the output key is simply the xor of the input keys
      | GateT.Xor wA wB, .Xor => wireStates[wA]! ^^^ wireStates[wB]!
      | GateT.Not wA, .Not => wireStates[wA]!
      | GateT.Const0, .Const k => k
      | GateT.Const1, .Const k => k
      | _, _ => panic! "Bad circuit"
    wireStates := wireStates.push lk
  return wireStates

instance : GarblingScheme Key GarbleState where
  garble c numInputs := do
    -- Generate the key difference, with first bit set to 1 so it switches colours as well
    let key_Δ := (← Key.gen).set_colour true
    let key_true ← (Array.range numInputs).mapM (fun _ => Key.gen)
    let initState : GarbleState :=
      { key_true := key_true  ++ Array.replicate c.size 0
        key_Δ := key_Δ,
        tables := #[] }
    let (_, s) ← (garbleCircuit c numInputs) |>.run initState
    return s

  inputLabel s wireId v := s.keyFor wireId v

  eval s c inputLabels := evalGarbledCircuit c s.tables inputLabels

  decodeOutput s wireId label := label == s.keyFor wireId true

  numCiphertexts s := s.numCiphertexts

end GRR3Garbling
