import MicroCircuit

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

private def uint32ToBools (v : UInt32) : List Bool :=
  List.range 32 |>.map (fun i => (v >>> i.toUInt32) &&& 1 == 1)

private def boolsToUInt32 (bs : List Bool) : UInt32 :=
  bs.foldl (init := ((0 : UInt32), (0 : UInt32))) (fun ⟨acc, i⟩ b =>
    (acc ||| (b.toUInt32 <<< i), i + 1))
  |>.1

-- SHA-256("abc") padded to 512 bits (big-endian 32-bit words)
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
  let mut msgWords : Array (Bundle 32) := #[]
  for _ in [:16] do
    msgWords := msgWords.push (← inputN 32)
  let hashWords ← sha256_block msgWords
  let mut outs : List Wire := []
  for w in hashWords do
    outs := outs ++ w.toList
  return outs

private def sha256Test : Bool :=
  let inputBits := abcPaddedBlock.foldl (init := ([] : List Bool)) (fun acc w => acc ++ uint32ToBools w)
  let outputBits := sha256Spec.evalOutputs inputBits
  List.range 8 |>.all (fun i =>
    let wordBits := outputBits.drop (i * 32) |>.take 32
    boolsToUInt32 wordBits == abcExpected[i]!)

#guard sha256Test

end SHA256Tests

/- ## Gate count -/

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
