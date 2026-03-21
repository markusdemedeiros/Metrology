import Metrology.LibCrypto
import Metrology.MicroCircuit

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
  exhaustive2 (circuit( input A  input B  C ← and A B ))
  IO.println "garble AND: all passed"

def test_garble_xor : IO Unit := do
  exhaustive2 (circuit( input A  input B  C ← xor A B ))
  IO.println "garble XOR: all passed"

def test_garble_two_gate : IO Unit := do
  exhaustive2 (circuit( input A  input B  C ← and A B  D ← xor A C ))
  IO.println "garble two-gate: all passed"

def test_garble_adder : IO Unit := do
  exhaustive3 (circuit(
    input A
    input B
    input Cin
    AB   ← xor A B
    S    ← xor AB Cin
    AB2  ← and A B
    CAB  ← and Cin AB
    Cout ← xor AB2 CAB ))
  IO.println "garble adder: all passed"

def main : IO Unit := do
  test_gate_garble
  test_garble_and
  test_garble_xor
  test_garble_two_gate
  test_garble_adder
