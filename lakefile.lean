import Lake
open Lake DSL

package metrology where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]
  testDriver := "ProbLangTest"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.32.2"

require cslib from git
   "https://github.com/leanprover/cslib" @ "v4.32.2"

require iris from git
  "https://github.com/leanprover-community/iris-lean.git" / "Iris"

-- SampCert dropped in the iris-lean-bump branch: it has no v4.30.0 release.
-- The two dependent files Metrology/SampCert/{SLang,Samplers}.lean are excluded
-- from the build (orphan modules, not imported by the default target).
-- require sampcert from git
--   "https://github.com/leanprover/SampCert.git" @ "v4.29.0"


@[default_target]
lean_lib Metrology

lean_exe metrology where
  root := `Main

lean_exe ProbLangTest where
  root := `ProbLangTest

lean_exe CtxInterpTest where
  root := `CtxInterpTest
  supportInterpreter := true
