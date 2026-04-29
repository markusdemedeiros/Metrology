module

public import MicroCircuit.GarbleGen
public import MicroCircuit.Common

@[expose] public section

namespace HalfGateGarbling

/-! ## Base implementation for circuit garbling
- Point-and-permute
- OTP Encryption
- Free NOT optimization
- Free XOR optimization
- Half gates optimization with row-reduction
-/

inductive GarbledGate
| And (kG0 kEv0 : Key) -- Row-reduced half gate
| Xor
| Not
| Id
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
        outWire := outWire + 1
        pushTable .Not 0
    | .Id wA => do
        let kA := (← get).keyFor wA
        modify fun s => { s with key_true := s.key_true.set! outWire (kA true) }
        outWire := outWire + 1
        pushTable .Id 0
    | .Const0 => do
        GarbleM.genKeysFor outWire
        let kk := (← get).keyFor outWire
        outWire := outWire + 1
        pushTable (.Const (kk false)) 1
    | .Const1 => do
        GarbleM.genKeysFor outWire
        let kk := (← get).keyFor outWire
        outWire := outWire + 1
        pushTable (.Const (kk true)) 1
    | .Xor wA wB => do
        let s ← get
        let kC := s.key_true[wA]! ^^^ s.key_true[wB]! ^^^ s.key_Δ
        modify fun s => { s with key_true := s.key_true.set! outWire kC }
        outWire := outWire + 1
        pushTable .Xor 0
    | .And wA wB => do
      let Δ := (← get).key_Δ
      let kA := (← get).keyFor wA
      let kB := (← get).keyFor wB
      let p_a := (kA true).colour
      let p_b := (kB true).colour
      let keyBForColour (c : Bool) := if c == p_b then kB true else kB false
      let r := !p_b

      -- Row reduction: We want to pick a value for CEt such that kEv1 = Key.nil
      -- +  Suffices for (keyBForColour true).sha256FFI.encrypt (kCE false ^^^ kA false) = Key.nil
      --    Suffices for (keyBForColour true).sha256FFI = kCE false ^^^ kA false
      --    Suffices for (keyBForColour true).sha256FFI ^^^ kA false = kCE false
      --    Suffices for CEt = (keyBForColour true).sha256FFI ^^^ kA false ^^^ Δ
      let CEt := (keyBForColour true).sha256FFI ^^^ kA false ^^^ Δ

      -- Row reduction: We want to pick a value for CGt such that kG1 is Key.nil.
      -- + p_a = true: Requires ctAT to be Key.nil
      --   * Suffices for (if r then kCG true else kCG false) = (kA true).sha256FFI
      --   * r = true:
      --     + Suffices for (kCG true) = (kA true).sha256FFI
      --     + Set CGt = (kA true).sha256FFI
      --   * r = false
      --     + Suffices for (kCG false) = (kA true).sha256FFI
      --     + Set CGt = (kA true).sha256FFI ^^^ Δ
      -- + p_a = false: Requires ctAF to be Key.nil
      --   * Suffices for (kCG false) = (kA false).sha256FFI
      --   * Set CGt = (kA false).sha256FFI ^^^ Δ
      let CGt :=
        match p_a, r with
        | true, true  => (kA true).sha256FFI
        | true, false => (kA true).sha256FFI ^^^ Δ
        | false, _    => (kA false).sha256FFI ^^^ Δ

      -- Keys for internal wires
      let kCE (b : Bool) := if b then CEt else CEt ^^^ Δ
      let kCG (b : Bool) := if b then CGt else CGt ^^^ Δ

      let kCT := (kCE true) ^^^ (kCG true) ^^^ Δ
      modify fun s => { s with key_true := s.key_true.set! outWire kCT }
      outWire := outWire + 1

      let ctAT := (kA true).sha256FFI.encrypt (if r then kCG true else kCG false)
      let ctAF := (kA false).sha256FFI.encrypt (kCG false)

      let kG0 := if p_a then ctAF else ctAT

      let kEv0 := (keyBForColour false).sha256FFI.encrypt (kCE false)

      pushTable (.And kG0 kEv0) 2

instance : Inhabited Gate := ⟨{ prim := .Const0, id := 0 }⟩
instance : Inhabited (Table Key) := ⟨(0, 0, 0, 0)⟩
instance : Inhabited GarbledGate := ⟨.Xor⟩

def evalGarbledCircuit (c : Circuit) (tables : Array GarbledGate)
    (inputLabels : Array Key) : Array Key := Id.run do
  let mut wireStates := inputLabels
  for i in [:c.size] do
    let g := c[i]!
    let lk := match g.prim, tables[i]! with
      | GateT.And wA wB, .And kG0 kEv0 =>
        let lA := wireStates[wA]!
        let lB := wireStates[wB]!
        let hA := lA.sha256FFI
        let hB := lB.sha256FFI
        -- Garbler half-gate: pick row by colour_a (permuted), decrypt
        let gOut := hA.decrypt (if lA.colour then Key.nil else kG0)
        -- Evaluator half-gate: v = b⊕r = colour_b. Pick row by v, decrypt, XOR in lA if v=true
        let v := lB.colour
        let eRow := if v then Key.nil else kEv0
        let eOut := hB.decrypt eRow ^^^ (if v then lA else 0)
        -- Combine the two half-gate outputs (free XOR of the internal wires)
        gOut ^^^ eOut
      | GateT.Xor wA wB, .Xor => wireStates[wA]! ^^^ wireStates[wB]!
      | GateT.Not wA, .Not => wireStates[wA]!
      | GateT.Id wA, .Id => wireStates[wA]!
      | GateT.Const0, .Const k => k
      | GateT.Const1, .Const k => k
      | _, _ => panic! "Bad circuit"
    wireStates := wireStates.push lk
  return wireStates

def scheme : GarblingScheme Key GarbleState where
  garble c numInputs := do
    let key_Δ := (← Key.gen).set_colour true
    let key_true ← (Array.range numInputs).mapM (fun _ => Key.gen)
    let initState : GarbleState :=
      { key_true := key_true ++ Array.replicate c.size 0
        key_Δ := key_Δ
        tables := #[] }
    let (_, s) ← (garbleCircuit c numInputs) |>.run initState
    return s

  inputLabel s wireId v := s.keyFor wireId v
  eval s c inputLabels := evalGarbledCircuit c s.tables inputLabels
  decodeOutput s wireId label := label == s.keyFor wireId true
  numCiphertexts s := s.numCiphertexts

end HalfGateGarbling
