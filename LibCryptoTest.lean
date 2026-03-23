import Metrology.MicroCircuitLib

structure CircuitSpec where
  gates : Circuit
  numInputs : Nat
  numWires : Nat
  outputs : List Wire

def CircuitSpec.run (cs : CircuitSpec) (inputs : List Bool) : Array Bool :=
  let initState : CircuitState :=
    { pc := cs.numInputs, wires := inputs.toArray ++ (Array.replicate (cs.numWires - cs.numInputs) false) }
  (cs.gates.eval.run initState).2.wires

def CircuitSpec.evalOutputs (cs : CircuitSpec) (inputs : List Bool) : List Bool :=
  let wires := cs.run inputs
  cs.outputs.map (fun w => wires[w]!)

def buildSpec (m : CircuitBuilderM (List Wire)) : CircuitSpec :=
  let (outputs, σ) := m.run { pc := 0, id := 0, circuit := #[] }
  { gates := σ.circuit, numInputs := σ.pc - σ.circuit.size, numWires := σ.pc, outputs }

/- ## Circuit eval tests -/

section CircuitEvalTests

private def andGate := buildSpec do
  let a ← input1
  let b ← input1
  let c ← and1 a b
  return [c]

private def xorGate := buildSpec do
  let a ← input1
  let b ← input1
  let c ← xor1 a b
  return [c]

private def twoGate := buildSpec do
  let a ← input1
  let b ← input1
  let c ← and1 a b
  let d ← xor1 a c
  return [c, d]

#guard andGate.evalOutputs [true, true]   = [true]
#guard andGate.evalOutputs [true, false]  = [false]
#guard andGate.evalOutputs [false, true]  = [false]
#guard andGate.evalOutputs [false, false] = [false]

#guard xorGate.evalOutputs [true, true]   = [false]
#guard xorGate.evalOutputs [true, false]  = [true]
#guard xorGate.evalOutputs [false, true]  = [true]
#guard xorGate.evalOutputs [false, false] = [false]

#guard twoGate.evalOutputs [true, true]  = [true, false]
#guard twoGate.evalOutputs [true, false] = [false, true]

private def adder := buildSpec do
  let a ← input1
  let b ← input1
  let cin ← input1
  let (s, cout) ← fullAdder a b cin
  return [s, cout]

private def adderCorrect (a b cin : Bool) : Bool :=
  match adder.evalOutputs [a, b, cin] with
  | [s, cout] => cout.toNat * 2 + s.toNat == a.toNat + b.toNat + cin.toNat
  | _ => false

#guard adderCorrect false false false
#guard adderCorrect false false true
#guard adderCorrect false true  false
#guard adderCorrect false true  true
#guard adderCorrect true  false false
#guard adderCorrect true  false true
#guard adderCorrect true  true  false
#guard adderCorrect true  true  true

end CircuitEvalTests

/- ## Bundle-based tests -/

section BundleTests

private def nBitAdderSpec (n : Nat) := buildSpec do
  let a ← inputN n
  let b ← inputN n
  let cin ← input1
  let (sums, cout) ← rippleCarry a b cin
  return sums.toList ++ [cout]

private def bundleToNat (bs : List Bool) : Nat :=
  bs.foldr (fun b acc => acc * 2 + b.toNat) 0

private def nBitAdderCorrect (n : Nat) (aVal bVal : Nat) (cin : Bool) : Bool :=
  let spec := nBitAdderSpec n
  let aBits := List.range n |>.map (fun i => (aVal >>> i) &&& 1 == 1)
  let bBits := List.range n |>.map (fun i => (bVal >>> i) &&& 1 == 1)
  let inputs := aBits ++ bBits ++ [cin]
  let results := spec.evalOutputs inputs
  let sBits := results.take n
  let cout  := results[n]!
  let result := bundleToNat sBits + cout.toNat * (2 ^ n)
  result == aVal + bVal + cin.toNat

#guard nBitAdderCorrect 4 0 0 false
#guard nBitAdderCorrect 4 0 0 true
#guard nBitAdderCorrect 4 5 3 false
#guard nBitAdderCorrect 4 5 3 true
#guard nBitAdderCorrect 4 15 15 false
#guard nBitAdderCorrect 4 15 15 true
#guard nBitAdderCorrect 4 7 8 false
#guard nBitAdderCorrect 4 9 6 true
#guard nBitAdderCorrect 8 0 0 false
#guard nBitAdderCorrect 8 127 128 false
#guard nBitAdderCorrect 8 255 255 true
#guard nBitAdderCorrect 8 42 137 true

end BundleTests

/- ## SHA-256 circuit test -/

section SHA256Tests

-- Helper: convert UInt32 to big-endian bits as a list of bools (LSB first in each word)
private def uint32ToBools (v : UInt32) : List Bool :=
  List.range 32 |>.map (fun i => (v >>> i.toUInt32) &&& 1 == 1)

-- Helper: convert list of bools (LSB first) back to UInt32
private def boolsToUInt32 (bs : List Bool) : UInt32 :=
  bs.foldl (init := ((0 : UInt32), (0 : UInt32))) (fun ⟨acc, i⟩ b =>
    (acc ||| (b.toUInt32 <<< i), i + 1))
  |>.1

-- SHA-256("abc") padded to 512 bits (big-endian 32-bit words)
-- "abc" = 0x61626380 then zeros, with length 24 bits = 0x18 at the end
private def abcPaddedBlock : Array UInt32 := #[
  0x61626380, 0x00000000, 0x00000000, 0x00000000,
  0x00000000, 0x00000000, 0x00000000, 0x00000000,
  0x00000000, 0x00000000, 0x00000000, 0x00000000,
  0x00000000, 0x00000000, 0x00000000, 0x00000018
]

-- Expected: ba7816bf 8f01cfea 414140de 5dae2223 b00361a3 96177a9c b410ff61 f20015ad
private def abcExpected : Array UInt32 := #[
  0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223,
  0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad
]

private def sha256Spec : CircuitSpec := buildSpec do
  -- 16 input words × 32 bits = 512 input bits
  let mut msgWords : Array (Bundle 32) := #[]
  for _ in [:16] do
    msgWords := msgWords.push (← inputN 32)
  let hashWords ← sha256_block msgWords
  -- Output all 8 × 32 = 256 hash bits
  let mut outs : List Wire := []
  for w in hashWords do
    outs := outs ++ w.toList
  return outs

private def sha256Test : Bool :=
  -- Build input bits from the padded block
  let inputBits := abcPaddedBlock.foldl (init := ([] : List Bool)) (fun acc w => acc ++ uint32ToBools w)
  let outputBits := sha256Spec.evalOutputs inputBits
  -- Check each output word
  List.range 8 |>.all (fun i =>
    let wordBits := outputBits.drop (i * 32) |>.take 32
    boolsToUInt32 wordBits == abcExpected[i]!)

#guard sha256Test

end SHA256Tests

/-
/- ## LibCrypto / garbling tests (commented out pending garbling rewrite) -/

def test_encryption : IO Unit := do
  let text : Nat := 666
  let iv : Nat ← IO.rand 0 ((2 ^ 128) - 1)
  let key : Nat ← IO.rand 0 ((2 ^ 128) - 1)
  let etext : ByteArray := text.toByteArrayLE 32 |>.get!
  let eiv : ByteArray := iv.toByteArrayLE 16 |>.get!
  let ekey : ByteArray := key.toByteArrayLE 16 |>.get!
  let cipher : ByteArray := LibCrypto.encAes128 etext eiv ekey
  let edecode : ByteArray := LibCrypto.decAes128 cipher eiv ekey
  let decode := Nat.ofByteArrayLE edecode
  IO.println s!"[text]    {text}"
  IO.println s!"[iv]      {iv}"
  IO.println s!"[key]     {key}"
  IO.println s!"[etext]   {etext}"
  IO.println s!"[eiv]     {eiv}"
  IO.println s!"[ekey]    {ekey}"
  IO.println s!"[cipher]  {cipher}"
  IO.println s!"[edecode] {edecode}"
  IO.println s!"[decode]  {decode}"

def test_table_encrypt : IO Unit := do
  let k1 ← keygen
  let k2 ← keygen
  let k3 ← keygen
  let p ← permgen
  IO.println s!"[k1]  {k1}"
  IO.println s!"[k2]  {k2}"
  IO.println s!"[k3]  {k3}"
  IO.println s!"[p]   {p}"
  let payload : WireState := { key := k3, perm := p }
  let ent : ByteArray := encryptTableEntry k1 k2 payload
  IO.println s!"[ent] {ent}"
  let dec : WireState := decryptTableEntry k1 k2 ent
  IO.println s!"[dec k3] {dec.key}"
  IO.println s!"[dec p] {dec.perm}"
  if dec.perm == p && dec.key == k3
    then IO.println s!"=== test passed ==="
    else IO.println s!"=== test failed ==="

def test_gate_garble : IO Unit := do
  let f := GateT.Xor.eval
  let k1T ← keygen
  let k1F ← keygen
  let k2T ← keygen
  let k2F ← keygen
  let k3T ← keygen
  let k3F ← keygen
  let p1 ← permgen
  let p2 ← permgen
  let p3 ← permgen
  let t := encryptTable (cond · k1T k1F) (cond · k2T k2F) (cond · k3T k3F) p1 p2 p3 f

  let in1 : Bool → WireState := (cond · ⟨k1T, not p1⟩ ⟨k1F, p1⟩)
  let in2 : Bool → WireState := (cond · ⟨k2T, not p2⟩ ⟨k2F, p2⟩)
  let out (k : Key) : Bool := k = k3T

  for vi in [false, true] do
    for vj in [false, true] do
      let ws1 := in1 vi
      let ws2 := in2 vj
      let wsk := Id.run <| decryptTable ws1 ws2 t
      let vk := f vi vj
      let kk := if vk then k3T else k3F
      let pk := Bool.xor p3 vk
      unless (wsk.perm = pk) do panic s!"=== pk failure ==="
      unless (wsk.key = kk) do panic s!"=== kk failure ==="
      unless (out wsk.key = vk) do panic s!"=== vk failure ==="
  IO.println "gate garble: all passed"

def inputLabel (s : GarbleState) (wireId : Nat) (v : Bool) : WireState :=
  { key  := s.key v wireId
    perm := Bool.xor (s.perm_r[wireId]!) v }

def readOutput (s : GarbleState) (wireId : Nat) (ws : WireState) : Bool :=
  ws.key == s.key true wireId

def testGarbleCircuit (c : Circuit) (numInputs : Nat) (inputVals : List Bool) : IO Unit := do
  let mut initState : GarbleState := { key_true := [], key_false := [], perm_r := [], tables := [] }
  for _ in List.range numInputs do
    let kt ← keygen
    let kf ← keygen
    let r  ← permgen
    initState := {
      key_true  := initState.key_true ++ [kt]
      key_false := initState.key_false ++ [kf]
      perm_r    := initState.perm_r ++ [r]
      tables    := []
    }
  let ((), finalState) ← garbleCircuit c |>.run initState
  let numGates := c.length
  let inputWires := inputVals.mapIdx fun i v => inputLabel finalState (numGates + i) v
  let resultWires := evalGarbledCircuit c finalState.tables inputWires
  let plainResult := (c.eval.run inputVals).2
  for gIdx in List.range numGates do
    let garbledV := readOutput finalState gIdx (resultWires[gIdx]!)
    let plainV := plainResult[gIdx]!
    unless garbledV == plainV do
      panic s!"Garble test failed at gate {gIdx}: garbled={garbledV}, plain={plainV}"

def exhaustive2 (c : Circuit) : IO Unit := do
  for vi in [false, true] do
    for vj in [false, true] do
      testGarbleCircuit c 2 [vi, vj]

def exhaustive3 (c : Circuit) : IO Unit := do
  for a in [false, true] do
    for b in [false, true] do
      for c' in [false, true] do
        testGarbleCircuit c 3 [a, b, c']

def test_garble_and : IO Unit := do
  exhaustive2 (buildSpec do
    let a ← input1; let b ← input1; let c ← and1 a b; return [c]).gates
  IO.println "garble AND: all passed"

def test_garble_xor : IO Unit := do
  exhaustive2 (buildSpec do
    let a ← input1; let b ← input1; let c ← xor1 a b; return [c]).gates
  IO.println "garble XOR: all passed"

def test_garble_two_gate : IO Unit := do
  exhaustive2 (buildSpec do
    let a ← input1; let b ← input1
    let c ← and1 a b; let d ← xor1 a c; return [c, d]).gates
  IO.println "garble two-gate: all passed"

def test_garble_adder : IO Unit := do
  exhaustive3 (buildSpec do
    let a ← input1; let b ← input1; let cin ← input1
    let (s, cout) ← fullAdder a b cin; return [s, cout]).gates
  IO.println "garble adder: all passed"

def main : IO Unit := do
  test_gate_garble
  test_garble_and
  test_garble_xor
  test_garble_two_gate
  test_garble_adder
-/


def CircuitCount (c : Circuit) : IO Unit := do
  let mut numAnd : Nat := 0
  let mut numXor : Nat := 0
  let mut numNot : Nat := 0
  let mut numConst0 : Nat := 0
  let mut numConst1 : Nat := 0
  for g in c do
    match g.prim with
    | .And _ _ => do numAnd := numAnd + 1
    | .Xor _ _ => do numXor := numXor + 1
    | .Not _ => do numNot := numNot + 1
    | .Const0 => do numConst0 := numConst0 + 1
    | .Const1 => do numConst1 := numConst1 + 1
  let tot := numAnd + numXor + numNot + numConst0 + numConst1
  IO.println s!"[Gates] Tot {tot} / And {numAnd} / Xor {numXor} / Not {numNot} / Const {numConst0 + numConst1}"

def sha256Circuit : Circuit :=
  let (_, σ) := (do
    let mut msg : Array (Bundle 32) := #[]
    for _ in [:16] do
      msg := msg.push (← inputN 32)
    let _ ← sha256_block msg
    return ()
  : CircuitBuilderM Unit).run { pc := 0, id := 0, circuit := #[] }
  σ.circuit

def main : IO Unit := do
  IO.println "SHA-256 circuit:"
  CircuitCount sha256Circuit
