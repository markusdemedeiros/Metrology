import Metrology.LibCrypto

/-- ProbLang test runner.

The `#eval` tests in `EvalPrim` and the `example` proofs in `DetStep` all
execute at elaboration time, so if this file compiles the tests have passed. -/
def main : IO Unit := do
  let text : Nat := 666
  let iv : Nat ← IO.rand 0 ((2 ^ 16) - 1)
  let key : Nat ← IO.rand 0 ((2 ^ 16) - 1)

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
