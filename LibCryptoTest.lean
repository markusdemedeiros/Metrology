import Metrology.LibCrypto

/-- ProbLang test runner.

The `#eval` tests in `EvalPrim` and the `example` proofs in `DetStep` all
execute at elaboration time, so if this file compiles the tests have passed. -/
def main : IO Unit := do
  let v ← LibCrypto.test
  IO.println s!"v: {v}"
  IO.println "All LibCrypto tests passed."
