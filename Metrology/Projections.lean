import Lean
import Metrology.Inspect
import Lean.Meta.Constructions.CtorElim
import Lean.AuxRecursor

open Lean Elab Command Term Meta

-- Helper to construct nested Prod types: A × B × C (right-associative)
-- For empty list: Unit
-- For non-empty list: uses last element as base, folds rest to build nested Prod
def mkNestedProdType (types : List Expr) : MetaM Expr :=
  match types with
  | [] => pure (Expr.const ``Unit [])
  | _ =>
    types.dropLast.foldrM (fun ty acc => mkAppM ``Prod #[ty, acc]) types.getLast!

-- Helper to construct nested Prod values: (a, (b, c)) (right-associative)
-- For empty list: ()
-- For non-empty list: uses last element as base, folds rest to build nested Prod
def mkNestedProdValue (exprs : List Expr) : MetaM Expr :=
  match exprs with
  | [] => pure (Lean.mkConst `Unit.unit)
  | _ =>
    exprs.dropLast.foldrM  (fun e acc => mkAppM ``Prod.mk #[e, acc]) exprs.getLast!


def ProjectionName (cinfo : ConstructorVal) : Name := cinfo.name.str "π"

def ProjectionType (c : ConstructorVal) : MetaM Expr := do
  forallBoundedTelescope c.type (some c.numParams) fun univs e' => do
    forallTelescope e' (fun args core => do
      let argTyps ← args.toList.mapM (inferType)
      let projs ← mkNestedProdType argTyps
      let optionType ← mkAppM ``Option #[projs]
      let funType := mkForall .anonymous .default core optionType
      mkForallFVars univs funType)

def displayFVars (pref : String) (A : Array Expr) : MetaM Unit := do
  for a in A do logInfo s!"{pref} {a}: {← inferType a}"

def mkProjection (decl : Name) (ictor : Nat) (cinfo : ConstructorVal) : MetaM Unit := do
  -- Collect the casesOn information
  let info ← getConstInfoInduct decl
  let casesOnInfo ← getConstVal <| mkCasesOnName decl
  let (e, τ) ← forallTelescope casesOnInfo.type fun xs _ => do
    let params : Array Expr := xs[:info.numParams]
    let majorIdx := info.numParams + 1 + info.numIndices
    let targetIdx := info.numParams + 2 + ictor
    unless xs.size > majorIdx && xs.size > targetIdx do
      throwError "unexpected arity in casesOn type"
    let majorArg := xs[majorIdx]!
    let target_arg := xs[targetIdx]!

    -- Construct the return type (optPair)
    let argtypes ← forallTelescope (← inferType target_arg) (fun args _ => args.mapM inferType)
    let projs ← mkNestedProdType argtypes.toList
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
            let ret_tup ← mkNestedProdValue ctorargs.toList
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
      let info ← getConstInfoInduct decl
      unless info.numNested == 0 do
        throwError "expected inductive with no nesting"
      unless info.numIndices == 0 do
        throwError "expected inductive with no indexing"
      let _ ← info.ctors.toArray.mapIdxM fun x y => do
        let cinfo ← getConstInfoCtor y
        mkProjection decl x cinfo |>.run'
    }

initialize registerBuiltinAttribute projectionsImpl

def ConstructorName (cinfo : ConstructorVal) : Name := cinfo.name.str "ctor"

def mkConstructor (decl : Name) (_ictor : Nat) (cinfo : ConstructorVal) : MetaM Unit := do
  let info ← getConstInfoInduct decl
  let _ ← forallTelescope cinfo.type fun xs typ => do
    let params : Array Expr := xs[:info.numParams]
    let args : Array Expr := xs[info.numParams:]

    -- Construct the uncurried constructor type
    let argtypes ← args.mapM inferType
    let projargtyp ← mkNestedProdType argtypes.toList
    let typOpen ← mkArrow projargtyp typ
    let typClosed ← mkForallFVars params typOpen

    -- Construct the uncurried constructor function
    let body : Expr ← withLocalDecl `x BinderInfo.default projargtyp λ x => do
      match args.size with
        | 0 => mkLambdaFVars #[x] (← mkAppOptM cinfo.name (params.map some))
        | 1 => mkLambdaFVars #[x] (← mkAppOptM cinfo.name (params.map some ++ [some x]))
        | n => do
          -- Extract the i-th component from nested Prod structure
          -- For structure (a, (b, (c, d))), we need to extract each component
          let mkAppProj (i : Nat) : MetaM Expr := do
            if i == n - 1 then
              -- Last element: apply snd repeatedly (i times)
              let mut result := x
              for _ in [:i] do
                result ← mkAppM ``Prod.snd #[result]
              return result
            else
              -- Other elements: apply snd (i times) then fst
              let mut result := x
              for _ in [:i] do
                result ← mkAppM ``Prod.snd #[result]
              mkAppM ``Prod.fst #[result]
          let mkAppArgs ← List.ofFnM (n := n) (fun i : Fin n => mkAppProj i.val)
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
      let info ← getConstInfoInduct decl
      unless info.numNested == 0 do
        throwError "expected inductive with no nesting"
      unless info.numIndices == 0 do
        throwError "expected inductive with no indexing"
      let _ ← info.ctors.toArray.mapIdxM fun x y => do
        let cinfo ← getConstInfoCtor y
        mkConstructor decl x cinfo |>.run'
    }

initialize registerBuiltinAttribute constructorsImpl
