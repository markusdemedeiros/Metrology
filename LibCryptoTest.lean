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
  let ent : ByteArray ← encryptTableEntry k1 k2 payload
  IO.println s!"[ent] {ent}"
  let dec : WireState ← decryptTableEntry k1 k2 ent
  IO.println s!"[dec k3] {dec.key}"
  IO.println s!"[dec p] {dec.perm}"
  if dec.perm == p && dec.key == k3
    then IO.println s!"=== test passed ==="
    else IO.println s!"=== test failed ==="

-- Manually simulate the garbling and decryption process for a single gate
def test_gate_garble : IO Unit := do
  let f := GateT.Xor.eval
  let k1T ← keygen
  let k1F ← keygen
  let k2T ← keygen
  let k2F ← keygen
  let k3T ← keygen
  let k3F ← keygen
  IO.println s!"=== keys ==="
  IO.println s!"[k1 T]  {k1T}"
  IO.println s!"[k1 F]  {k1F}"
  IO.println s!"[k2 T]  {k2T}"
  IO.println s!"[k2 F]  {k2F}"
  IO.println s!"[k3 T]  {k3T}"
  IO.println s!"[k3 F]  {k3F}"
  let p1 ← permgen
  let p2 ← permgen
  let p3 ← permgen
  IO.println s!"=== perm ==="
  IO.println s!"[p1]    {p1}"
  IO.println s!"[p2]    {p2}"
  IO.println s!"[p3]    {p3}"
  let t := encryptTable (cond · k1T k1F) (cond · k2T k2F) (cond · k3T k3F) p1 p2 p3 f
  IO.println s!"=== table ==="
  IO.println s!"[00]    {t.get false false}"
  IO.println s!"[01]    {t.get false true}"
  IO.println s!"[10]    {t.get true false}"
  IO.println s!"[11]    {t.get true true}"

  -- Input functions
  let in1 : Bool → WireState := (cond · ⟨k1T, not p1⟩ ⟨k1F, p1⟩)
  let in2 : Bool → WireState := (cond · ⟨k2T, not p2⟩ ⟨k2F, p2⟩)

  -- Interpretation function
  let out (k : Key) : Bool := k = k3T

  let mut testC : Nat := 1
  for vi in [false, true] do
    for vj in [false, true] do
      IO.println s!""
      IO.println s!"=== {testC}/4 ==="
      testC := testC + 1
      IO.println s!"[true vi]  {vi}"
      IO.println s!"[true vj]  {vj}"
      let ws1 := in1 vi
      let ws2 := in2 vj
      IO.println s!"[recv ki]  {ws1.key}"
      IO.println s!"[recv kj]  {ws2.key}"
      IO.println s!"[recv pi]  {ws1.perm}"
      IO.println s!"[recv pj]  {ws2.perm}"
      let wsk := Id.run <| decryptTable ws1 ws2 t
      IO.println s!"[decrypt k]  {wsk.key}"
      IO.println s!"[decrypt p]  {wsk.perm}"

      let vk := f vi vj
      let kk := if vk then k3T else k3F
      let pk := Bool.xor p3 vk
      IO.println s!"[true vk]  {vk}"
      IO.println s!"[true pk]  {pk}"
      IO.println s!"[read vk]  {out wsk.key}"

      unless (wsk.perm = pk) do panic s!"=== pk failure ==="
      unless (wsk.key = kk) do panic s!"=== kk failure ==="
      unless (out wsk.key = vk) do panic s!"=== vk failure ==="
      IO.println s!"=== passed ==="

  return


def main : IO Unit := do
  test_gate_garble
