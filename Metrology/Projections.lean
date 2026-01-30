import Lean
import Metrology.Inspect
import Lean.Meta.Constructions.CtorElim
import Lean.AuxRecursor

open Lean Elab Command Term Meta

def expectE (b : Bool) (s : String) : AttrM Unit :=
  if b then return () else throwError s

def List.foldlM' {m : Type _ → Type _} [Monad m] {α : Type _} :
    (d : α) → (f : α → α → m α) → List α → m α :=
  fun d f l =>
    match l with
    | [] => return d
    | l0::ls => ls.foldlM f l0

-- FIXME:
def List.foldrM' {m : Type _ → Type _} [Monad m] {α : Type _} :
    (d : α) → (f : α → α → m α) → List α → m α :=
  fun d f l =>
    match l with
    | [] => return d
    | _::_ =>
      let _ : Inhabited α := ⟨d⟩ -- Nonsense
      let l_last := l[l.length - 1]!
      let l_exceptlast := l.take (l.length - 1)
      List.foldrM f l_last l_exceptlast


def ProjectionName (cinfo : ConstructorVal) : Name := cinfo.name.str "π"

def ProjectionType (c : ConstructorVal) : MetaM Expr := do
  forallBoundedTelescope c.type (some c.numParams) fun univs e' => do
    forallTelescope e' (fun args core => do
      let argTyps ← args.toList.mapM (inferType)
      let projs ← argTyps.foldlM' (Expr.const ``Unit []) (fun x p => do mkAppM ``Prod #[x,p])
      let optionType ← mkAppM ``Option #[projs]
      let funType := mkForall .anonymous .default core optionType
      mkForallFVars univs funType)

def displayFVars (pref : String) (A : Array Expr) : MetaM Unit := do
  for a in A do logInfo s!"{pref} {a}: {← inferType a}"


def mkProjection (decl : Name) (ictor : Nat) (cinfo : ConstructorVal) : MetaM Unit := do
  -- Collect the casesOn information
  let ConstantInfo.inductInfo info ← getConstInfo decl | unreachable!
  let casesOnInfo ← getConstVal <| mkCasesOnName decl
  let (e, τ) ← forallTelescope casesOnInfo.type fun xs _ => do
    let params : Array Expr := xs[:info.numParams]
    let majorArg := xs[info.numParams + 1 + info.numIndices]!
    let target_arg := xs[info.numParams + 2 + ictor]!

    -- Construct the return type (optPair)
    let argtypes ← forallTelescope (← inferType target_arg) (fun args _ => args.mapM inferType)
    let projs ← argtypes.toList.foldrM' (Expr.const ``Unit []) (fun x p => do mkAppM ``Prod #[x,p])
    let retNone ← mkNone projs
    let returnType : Expr ← mkAppM ``Option #[projs]

    -- Construct the motive
    let motive := mkLambda .anonymous .default (← inferType majorArg) returnType

    -- Construct the cases
    let alts : Array Expr ← info.ctors.toArray.mapIdxM fun i ctorName => do
      let ctor ← mkAppOptM ctorName (params.map some)
      let ctorType ← inferType ctor
      forallTelescope ctorType fun ctorargs _ =>
        if (i = ictor)
          then do
            let ret_tup ← ctorargs.toList.foldrM' (Lean.mkConst `Unit.unit) (fun x p => do mkAppM ``Prod.mk #[x,p])
            mkLambdaFVars ctorargs (← mkSome projs ret_tup)
          else mkLambdaFVars ctorargs retNone

    -- Apply the cases to the parameters, motives, etc
    let e ← mkAppOptM casesOnInfo.name ((params ++ #[motive, majorArg] ++ alts).map some)
    let e ← mkLambdaFVars (params ++ #[majorArg]) e

    -- Apply the
    let eτ ← mkArrow (← inferType majorArg) returnType
    let eτ ← mkForallFVars params eτ
    return (e, eτ)

  addAndCompile <| .defnDecl {
    name := ProjectionName cinfo
    levelParams := casesOnInfo.levelParams.drop 1
    type := τ
    value := e
    hints := ReducibilityHints.abbrev
    safety := .safe
  }

syntax (name := projections) "projections" : attr

-- TODO: Add projection type itself to the context?
def projectionsImpl : AttributeImpl := {
    name  := `projections
    descr := "Automatically construct projection functions for a inductive datatype"
    add   := fun decl _stx _kind => do
      let env ← getEnv
      let some (.inductInfo info) := env.constants.find? decl | unreachable!
      expectE (info.numNested == 0) "expected inductive with no nesting"
      expectE (info.numIndices == 0) "expected inductive with no indexing"
      let _ ← info.ctors.toArray.mapIdxM fun x y => do
        let some (.ctorInfo cinfo) := env.constants.find? y | throwError "(internal) bad constructor"
        mkProjection decl x cinfo |>.run'
    }

initialize registerBuiltinAttribute projectionsImpl

def ConstructorName (cinfo : ConstructorVal) : Name := cinfo.name.str "ctor"

def mkConstructor (decl : Name) (ictor : Nat) (cinfo : ConstructorVal) : MetaM Unit := do
  let ConstantInfo.inductInfo info ← getConstInfo decl | unreachable!
  let _ ← forallTelescope cinfo.type fun xs typ => do
    let params : Array Expr := xs[:info.numParams]
    let args : Array Expr := xs[info.numParams:]

    -- Construct the uncurried constructor type
    let argtypes ← args.mapM inferType
    let projargtyp ← argtypes.toList.foldrM' (Expr.const ``Unit []) (fun x p => do mkAppM ``Prod #[x,p])
    let typOpen ← mkArrow projargtyp typ
    let typClosed ← mkForallFVars params typOpen

    -- Construct the uncurried constructor function
    let body : Expr ← withLocalDecl `x BinderInfo.default projargtyp λ x => do
      match args.size with
        | 0 => mkLambdaFVars #[x] (← mkAppOptM cinfo.name (params.map some))
        | 1 => mkLambdaFVars #[x] (← mkAppOptM cinfo.name (params.map some ++ [some x]))
        | n => do
          let rec mkAppProj' : Nat → MetaM Expr
            | .zero => do return x
            | .succ n => do
              let r ← mkAppProj' n
              mkAppM ``Prod.snd #[r]
          let mkAppProj (i N : Nat) : MetaM Expr := do
            if i = N - 1
              then do
                let r ← mkAppProj' (i-1)
                mkAppM ``Prod.snd #[r]
              else do
                let r ← mkAppProj' i
                mkAppM ``Prod.fst #[r]
          let mkAppArgs ← List.ofFnM (n := n) (fun i : Fin n => mkAppProj i n)
          mkLambdaFVars #[x] (← mkAppOptM cinfo.name (params.map some ++ mkAppArgs.map some))
    let bodyClosed ← mkLambdaFVars params body

    addAndCompile <| .defnDecl {
      name := ConstructorName cinfo
      levelParams := cinfo.levelParams
      type := typClosed
      value := bodyClosed
      hints := ReducibilityHints.abbrev
      safety := .safe
    }

syntax (name := constructors) "constructors" : attr

-- TODO: Add projection type itself to the context?
def constructorsImpl : AttributeImpl := {
    name  := `constructors
    descr := "Automatically construct constructor functions for a inductive datatype"
    add   := fun decl _stx _kind => do
      let env ← getEnv
      let some (.inductInfo info) := env.constants.find? decl | unreachable!
      expectE (info.numNested == 0) "expected inductive with no nesting"
      expectE (info.numIndices == 0) "expected inductive with no indexing"
      let _ ← info.ctors.toArray.mapIdxM fun x y => do
        let some (.ctorInfo cinfo) := env.constants.find? y | throwError "(internal) bad constructor"
        mkConstructor decl x cinfo |>.run'
    }

initialize registerBuiltinAttribute constructorsImpl
