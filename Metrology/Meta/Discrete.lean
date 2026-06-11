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

/-- Collect the fully-qualified names *defined* by this command, by reading the
`isBinder` constant occurrences from its `InfoTree`s.

When a declaration is elaborated, its `declId` is recorded as a `TermInfo` whose
`expr` is the defining `.const` (fully qualified) with `isBinder := true` (see
`Lean.Elab.Declaration`). Reading these gives us the client's *resolved* name —
unlike parsing the surface `declId`, which yields the unqualified name and so
fails to match the fully-qualified names stored in `discreteExt`. -/
meta def definedNames (trees : Array Elab.InfoTree) : IO NameSet := do
  let acc : IO.Ref NameSet ← IO.mkRef {}
  for tree in trees do
    tree.visitM' (postNode := fun _ info _ => do
      let .ofTermInfo ti := info | return
      unless ti.isBinder do return
      let .const declName _ := ti.expr | return
      acc.modify (·.insert declName))
  acc.get

/-- The use-site linter: after each command, walk its `InfoTree`s for constant
references and warn when a discrete constant is referenced from a non-discrete
client. A reference is *fine* iff the enclosing declaration is itself discrete. -/
meta def discreteUse : Linter where
  run := fun _cmdStx => do
    unless Linter.getLinterValue linter.discrete (← Linter.getLinterOptions) do
      return
    let env ← getEnv
    let trees := (← get).infoState.trees.toArray
    -- The names this command defines (fully qualified). If any is discrete, the
    -- client is discrete and every reference it makes is allowed.
    let defined ← definedNames trees
    if defined.any (isDiscrete env ·) then
      return
    -- Walk the InfoTree for constant *references* (non-binder occurrences) and
    -- warn on discrete ones. Binders are the declaration's own defining
    -- occurrences, so excluding them prevents a decl warning about itself.
    let warned : IO.Ref NameSet ← IO.mkRef {}
    for tree in trees do
      tree.visitM' (postNode := fun _ info _ => do
        let .ofTermInfo ti := info | return
        if ti.isBinder then return
        let .const declName _ := ti.expr | return
        unless isDiscrete env declName do return
        let some _ := info.range? | return
        let .original .. := info.stx.getHeadInfo | return
        if (← warned.get).contains declName then return
        warned.modify (·.insert declName)
        logWarningAt info.stx
          (.tagged linter.discrete.name
            m!"`{.ofConstName declName true}` is discrete and may only be referenced by discrete declarations."))

meta initialize addLinter discreteUse

end Metrology.Discrete

end
