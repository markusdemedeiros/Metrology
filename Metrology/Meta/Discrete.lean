module

public meta import Lean

@[expose] public section

open Lean Elab Command Term Meta

/-!
# The `@[discrete]` attribute

Mark a definition as belonging to the *discrete fragment*. A `@[discrete]`
declaration may only be referenced by other `@[discrete]` declarations; any
*non-discrete* client that references it triggers the `linter.discrete`
warning at the reference site.

The mechanism has three parts (Path B from the design discussion):

1. `discreteExt` — an environment extension holding the `NameSet` of all
   declarations marked `@[discrete]`. Populated by the attribute's `add`
   callback (bookkeeping only — `add` runs at the *definition* site and cannot
   see use sites).
2. `discreteUse` — a `Linter` that runs after each command, walks the command's
   `InfoTree` for constant references, and warns when a *discrete* constant is
   referenced from a *non-discrete* enclosing declaration.
3. `linter.discrete` — the option gating the warning, mirroring
   `linter.deprecated`.
-/

namespace Metrology.Discrete

/-- The set of declarations marked `@[discrete]`. -/
meta initialize discreteExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun es => es.foldl (fun s arr => arr.foldl (·.insert ·) s) {}
    addEntryFn    := fun s n => s.insert n
    toArrayFn     := fun es => es.toArray
  }

/-- Is `declName` marked `@[discrete]` in `env`? -/
meta def isDiscrete (env : Environment) (declName : Name) : Bool :=
  (discreteExt.getState env).contains declName

syntax (name := discrete) "discrete" : attr

meta initialize registerBuiltinAttribute {
  name  := `discrete
  descr := "Mark a definition as belonging to the discrete fragment. It may only be referenced by other discrete definitions; non-discrete clients get a `linter.discrete` warning."
  add   := fun decl _stx _kind => do
    modifyEnv fun env => discreteExt.addEntry env decl
}

/-- Whether to warn when a discrete declaration is referenced from a
non-discrete client. -/
meta register_option linter.discrete : Bool := {
  defValue := true
  descr    := "if true, warn when a `@[discrete]` declaration is referenced from a non-discrete declaration"
}

/-- Collect the names declared by command syntax `stx`, if any.

We look for a `declId` (the `name.{universes}` node following a declaration
keyword) anywhere in the command and return the underlying identifier. This is
deliberately tolerant: any command that declares a name we can recognize lets us
ask "is the *client* discrete?". -/
meta partial def declaredNames (stx : Syntax) : Array Name := Id.run do
  let mut acc := #[]
  if stx.getKind == ``Lean.Parser.Command.declId then
    if let some id := stx[0].identComponents.head?.map (·.getId) then
      acc := acc.push id
    else if stx[0].isIdent then
      acc := acc.push stx[0].getId
  for arg in stx.getArgs do
    acc := acc ++ declaredNames arg
  return acc

/-- The use-site linter: after each command, walk its `InfoTree`s for constant
references and warn when a discrete constant is referenced from a non-discrete
client. A reference is *fine* iff the enclosing declaration is itself discrete. -/
meta def discreteUse : Linter where
  run := fun cmdStx => do
    unless Linter.getLinterValue linter.discrete (← Linter.getLinterOptions) do
      return
    let env ← getEnv
    -- Is the client (this command's declaration) discrete?
    let clientDiscrete := (declaredNames cmdStx).any (isDiscrete env ·)
    if clientDiscrete then
      return
    -- Walk the InfoTree for constant references and warn on discrete ones.
    let trees := (← get).infoState.trees.toArray
    let warned : IO.Ref NameSet ← IO.mkRef {}
    for tree in trees do
      tree.visitM' (postNode := fun _ info _ => do
        let .ofTermInfo ti := info | return
        let .const declName _ := ti.expr | return
        unless isDiscrete env declName do return
        let some _ := info.range? | return
        let .original .. := info.stx.getHeadInfo | return
        if (← warned.get).contains declName then return
        warned.modify (·.insert declName)
        Linter.logLint linter.discrete info.stx
          m!"`{.ofConstName declName true}` is discrete and may only be referenced \
             from discrete declarations; this client is not marked `@[discrete]`")

meta initialize addLinter discreteUse

end Metrology.Discrete

end
