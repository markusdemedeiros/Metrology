import Lake
open Lake DSL System

package metrology where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]
  testDriver := "ProbLangTest"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"

require iris from git
  "https://github.com/leanprover-community/iris-lean.git" @ "master"

@[default_target]
lean_lib Metrology

lean_exe metrology where
  root := `Main

lean_exe ProbLangTest where
  root := `ProbLangTest

target LibCryptoFFI (pkg : NPackage __name__) : FilePath := do
  let oFile := pkg.buildDir / "ffi" / "FFI.o"
  let aFile := pkg.buildDir / "ffi" / "libCryptoFFI.a"
  let srcFile ← inputFile (pkg.dir / "Metrology" / "LibCrypto" / "LibCryptoBindings.c") false
  let lean ← getLeanInstall
  let oJob ← buildO oFile srcFile
    (weakArgs := #[s!"-I{lean.includeDir}", "-I/opt/local/include/openssl", "-I/opt/local/include"])
    (compiler := "cc")
  buildStaticLib aFile #[oJob]

def linkObjs : TargetArray FilePath := #[LibCryptoFFI]
def linkArgs : Array String := #["-L/opt/local/lib", "-lssl", "-lcrypto"]

lean_lib LibCrypto where
  srcDir := "Metrology"
  moreLinkObjs := linkObjs
  moreLinkArgs := linkArgs

lean_exe LibCryptoTest where
  root := `LibCryptoTest
  moreLinkObjs := linkObjs
  moreLinkArgs := linkArgs

lean_lib MicroCircuit

lean_exe MicroCircuitTest where
  root := `MicroCircuitTest

-- lake env lean --run MicroCircuitViz.lean sha256.dot
-- sfdp -Tpng sha256.dot -o sha256.png   
lean_exe MicroCircuitViz where
  root := `MicroCircuitViz
