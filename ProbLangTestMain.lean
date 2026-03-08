import Metrology.ProbLang.Test

/-- ProbLang test runner.

The `#eval` tests in `EvalPrim` and the `example` proofs in `DetStep` all
execute at elaboration time, so if this file compiles the tests have passed. -/
def main : IO Unit :=
  IO.println "All ProbLang tests passed."
