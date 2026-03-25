import Init.Data.Nat.Bitwise.Basic

/-! # Circuit representation and monadic builder

A simple boolean circuit library with typed wire bundles
and a monadic construction DSL.
-/

abbrev Wire := Nat

inductive GateT (α : Type _)
  | And (wA wB : α)
  | Xor (wA wB : α)
  | Not (wA : α)
  | Id (wA : α)
  | Const0
  | Const1
  deriving Repr

def GateT.eval : GateT Bool → Bool
  | .And wA wB => and wA wB
  | .Xor wA wB => xor wA wB
  | .Not wA => !wA
  | .Id wA => wA
  | .Const0 => false
  | .Const1 => true

structure Gate where
  prim : GateT Wire
  id : Nat
  deriving Repr

abbrev Circuit := Array Gate

/- ## Monadic circuit builders -/

section Construction

structure CircuitBuilderState where
  pc : Nat
  id : Nat
  circuit : Circuit

abbrev CircuitBuilderM := StateT CircuitBuilderState Id

def freshWire : CircuitBuilderM Wire :=
  modifyGet (fun σ => (σ.pc, { σ with pc := σ.pc + 1 }))

def input1 : CircuitBuilderM Wire := freshWire

def emitGate (g : GateT Wire) : CircuitBuilderM Wire := do
  let w ← freshWire
  modify (fun σ => { σ with circuit := σ.circuit.push { prim := g, id := w } })
  return w

def and1 (a b : Wire) : CircuitBuilderM Wire := emitGate (.And a b)
def xor1 (a b : Wire) : CircuitBuilderM Wire := emitGate (.Xor a b)
def not1 (a : Wire) : CircuitBuilderM Wire := emitGate (.Not a)

def buildCircuit (m : CircuitBuilderM α) : α × Circuit :=
  let (a, σ) := m.run { pc := 0, id := 0, circuit := #[] }
  (a, σ.circuit)

structure Bundle (n : Nat) where
  wires : Array Wire
  deriving Inhabited

instance : GetElem (Bundle n) Nat Wire (fun _ i => i < n) where
  getElem b i _ := b.wires[i]!

def Bundle.toList (b : Bundle n) : List Wire := b.wires.toList

def inputN (n : Nat) : CircuitBuilderM (Bundle n) := do
  let mut b : Array Wire := #[]
  for _ in [:n] do
    b := b.push (← freshWire)
  return ⟨b⟩

def andN (a b : Bundle n) : CircuitBuilderM (Bundle n) := do
  let mut out : Array Wire := #[]
  for i in [:n] do
    out := out.push (← and1 a.wires[i]! b.wires[i]!)
  return ⟨out⟩

def xorN (a b : Bundle n) : CircuitBuilderM (Bundle n) := do
  let mut out : Array Wire := #[]
  for i in [:n] do
    out := out.push (← xor1 a.wires[i]! b.wires[i]!)
  return ⟨out⟩

def notN (a : Bundle n) : CircuitBuilderM (Bundle n) := do
  let mut out : Array Wire := #[]
  for i in [:n] do
    out := out.push (← not1 a.wires[i]!)
  return ⟨out⟩

/-- Right rotation by a constant — pure wire permutation, no gates. -/
def rotrN (a : Bundle n) (k : Nat) : Bundle n :=
  ⟨Array.ofFn (n := n) (fun i => a.wires[(i.val + k) % n]!)⟩

/-- Right shift by a constant — shifted-in positions filled with zeroW. -/
def shrN (a : Bundle n) (k : Nat) (zeroW : Wire) : Bundle n :=
  ⟨Array.ofFn (n := n) (fun i => if i.val + k < n then a.wires[(i.val + k)]! else zeroW)⟩

def const0 : CircuitBuilderM Wire := emitGate .Const0
def const1 : CircuitBuilderM Wire := emitGate .Const1

def const32 (v : UInt32) : CircuitBuilderM (Bundle 32) := do
  let mut out : Array Wire := #[]
  for i in [:32] do
    if (v >>> i.toUInt32) &&& 1 == 1
    then out := out.push (← const1)
    else out := out.push (← const0)
  return ⟨out⟩

end Construction

/- ## Spec evaluation of a circuit -/

section Evaluation

structure CircuitState where
  pc : Nat
  wires : Array Bool

abbrev CircuitEvalM := StateT CircuitState Id

def setWireVal (i : Nat) (b : Bool) : CircuitEvalM Unit :=
  modifyGet (fun σ => ((), { σ with wires := σ.wires.set! i b }))

def getWireVal (i : Nat) : CircuitEvalM Bool := do
  let σ ← get
  return σ.wires[i]!

def getFreshWire : CircuitEvalM Wire := do
  modifyGet (fun σ => (σ.pc, { σ with pc := σ.pc + 1 }))

def Gate.eval (g : Gate) : CircuitEvalM Bool :=
  match g.prim with
  | .And wA wB => do
    let vA ← getWireVal wA
    let vB ← getWireVal wB
    return GateT.eval (.And vA vB)
  | .Xor wA wB => do
    let vA ← getWireVal wA
    let vB ← getWireVal wB
    return GateT.eval (.Xor vA vB)
  | .Not wA => do
    let vA ← getWireVal wA
    return GateT.eval (.Not vA)
  | .Id wA => do
    let vA ← getWireVal wA
    return vA
  | .Const0 => return false
  | .Const1 => return true

def Circuit.eval (c : Circuit) : CircuitEvalM Unit := do
  for g in c do
    let v ← g.eval
    let w ← getFreshWire
    setWireVal w v

end Evaluation

/- ## Circuit stats -/

structure GateCounts where
  ands : Nat := 0
  xors : Nat := 0
  nots : Nat := 0
  ids : Nat := 0
  const0s : Nat := 0
  const1s : Nat := 0
  deads : Nat := 0
  deriving Repr

def GateCounts.total (gc : GateCounts) : Nat :=
  gc.ands + gc.xors + gc.nots + gc.ids + gc.const0s + gc.const1s + gc.deads

instance : ToString GateCounts where
  toString gc :=
    s!"AND: {gc.ands}, XOR: {gc.xors}, NOT: {gc.nots}, ID: {gc.ids}, Const0: {gc.const0s}, Const1: {gc.const1s}, Dead: {gc.deads}, Total: {gc.total}"

def Circuit.gateCounts (c : Circuit) : GateCounts :=
  c.foldl (init := {}) fun gc g =>
    match g.prim with
    | .And _ _  => { gc with ands := gc.ands + 1 }
    | .Xor _ _  => { gc with xors := gc.xors + 1 }
    | .Not _    => { gc with nots := gc.nots + 1 }
    | .Id _     => { gc with ids := gc.ids + 1 }
    | .Const0   => { gc with const0s := gc.const0s + 1 }
    | .Const1   => { gc with const1s := gc.const1s + 1 }

/- ## CircuitSpec for testing -/

structure CircuitSpec where
  gates : Circuit
  numInputs : Nat
  numWires : Nat
  outputs : List Wire

def CircuitSpec.run (cs : CircuitSpec) (inputs : List Bool) : Array Bool :=
  let initState : CircuitState :=
    { pc := cs.numInputs, wires := inputs.toArray ++ (Array.replicate (cs.numWires - cs.numInputs) false) }
  (cs.gates.eval.run initState).2.wires

def CircuitSpec.evalOutputs (cs : CircuitSpec) (inputs : List Bool) : List Bool :=
  let wires := cs.run inputs
  cs.outputs.map (fun w => wires[w]!)

def buildSpec (m : CircuitBuilderM (List Wire)) : CircuitSpec :=
  let (outputs, σ) := m.run { pc := 0, id := 0, circuit := #[] }
  { gates := σ.circuit, numInputs := σ.pc - σ.circuit.size, numWires := σ.pc, outputs }


/-! ## Constant and equality propagation optimization in a circuit.
  disequality constraints to increase the number of gates that are eliminated. -/

namespace ConstantProp

inductive AbstractValue where
  | Cst (b : Bool)
  | Unk
  deriving Inhabited

structure AbstractState where
  pc : Nat
  wires : Array AbstractValue
  optimized : Circuit

abbrev CPEvalM := StateT AbstractState Id

def setWire (i : Nat) (b : AbstractValue) : CPEvalM Unit :=
  modifyGet (fun σ => ((), { σ with wires := σ.wires.set! i b }))

def getWire (i : Nat) : CPEvalM AbstractValue := do
  let σ ← get
  return σ.wires[i]!

def getFreshWire : CPEvalM Wire := do
  modifyGet (fun σ => (σ.pc, { σ with pc := σ.pc + 1 }))

def pushGate (g : Gate) : CPEvalM Unit :=
  modifyGet (fun σ => ((), { σ with optimized := σ.optimized.push g }))

def pushGateAs (g : Gate) (p : GateT Wire) : CPEvalM Unit :=
  pushGate { g with prim := p}

def toConst : Bool → GateT Wire | true => .Const1 | false => .Const0

-- Read the state, push an optimized gate, and return the new abstract value
def Gate.constPropGate (g : Gate) : CPEvalM AbstractValue :=
  match g.prim with
  | .And wA wB => do
    let vA ← getWire wA
    let vB ← getWire wB
    match vA, vB with
    | .Unk,       .Unk        => do pushGate g; return .Unk
    | .Cst true,  .Unk        => do pushGateAs g (.Id wB); return .Unk
    | .Cst false, .Unk        => do pushGateAs g (toConst false); return .Cst false
    | .Unk,       .Cst true   => do pushGateAs g (.Id wA); return .Unk
    | .Unk,       .Cst false  => do pushGateAs g (toConst false); return .Cst false
    | .Cst bA,    .Cst bB     => do pushGateAs g (toConst <| bA && bB); return .Cst (bA && bB)
  | .Xor wA wB => do
    let vA ← getWire wA
    let vB ← getWire wB
    match vA, vB with
    | .Unk,       .Unk        => do pushGate g; return .Unk
    | .Cst true,  .Unk        => do pushGateAs g (.Not wB); return .Unk
    | .Cst false, .Unk        => do pushGateAs g (.Id wB); return .Unk
    | .Unk,       .Cst true   => do pushGateAs g (.Not wA); return .Unk
    | .Unk,       .Cst false  => do pushGateAs g (.Id wA); return .Unk
    | .Cst bA,    .Cst bB     => do pushGateAs g (toConst <| bA ^^ bB); return .Cst (bA ^^ bB)
  | .Not wA => do
    let vA ← getWire wA
    match vA with
    | .Unk                    => do pushGate g; return .Unk
    | .Cst b                  => do pushGateAs g (toConst !b); return .Cst !b
  | .Id wA => do
    let vA ← getWire wA
    match vA with
    | .Unk                    => do pushGate g; return .Unk
    | .Cst b                  => do pushGateAs g (toConst b); return .Cst b
  | .Const0                   => do pushGate g; return .Cst false
  | .Const1                   => do pushGate g; return .Cst true

def constantPropM (c : Circuit) : CPEvalM Unit := do
  for g in c do
    let v ← Gate.constPropGate g
    let w ← getFreshWire
    setWire w v

end ConstantProp

def constProp (numInputs : Nat) (c : Circuit) (outs : List Wire) : Circuit × List Wire :=
  let initWires := Array.replicate (numInputs + c.size) .Unk
  let ((), s) := ConstantProp.constantPropM c |>.run ⟨numInputs, initWires, #[]⟩
  (s.optimized, outs)

/-- Delete constant gates and compact wire IDs. -/
def constElim (numInputs : Nat) (c : Circuit) (outs : List Wire) : Circuit × List Wire := Id.run do
  let mut wireMap : Array Nat := Array.ofFn (n := numInputs) (fun i => i.val)
  let mut nextId := numInputs
  for g in c do
    match g.prim with
    | .Const0 | .Const1 => wireMap := wireMap.push 0
    | _ => wireMap := wireMap.push nextId; nextId := nextId + 1
  let r (w : Wire) : Wire := wireMap[w]!
  let mut out : Circuit := #[]
  for g in c do
    match g.prim with
    | .Const0 | .Const1 => pure ()
    | .And wA wB => out := out.push { prim := .And (r wA) (r wB), id := r g.id }
    | .Xor wA wB => out := out.push { prim := .Xor (r wA) (r wB), id := r g.id }
    | .Not wA    => out := out.push { prim := .Not (r wA),         id := r g.id }
    | .Id wA     => out := out.push { prim := .Id (r wA),          id := r g.id }
  return (out, outs.map r)

/-- Inline Id gates: replace references with the Id's input, then delete. -/
def idElim (numInputs : Nat) (c : Circuit) (outs : List Wire) : Circuit × List Wire := Id.run do
  let mut wireMap : Array Nat := Array.ofFn (n := numInputs) (fun i => i.val)
  let mut nextId := numInputs
  for g in c do
    match g.prim with
    | .Id wA => wireMap := wireMap.push wireMap[wA]!
    | _ => wireMap := wireMap.push nextId; nextId := nextId + 1
  let r (w : Wire) : Wire := wireMap[w]!
  let mut out : Circuit := #[]
  for g in c do
    match g.prim with
    | .Id _ => pure ()
    | .And wA wB => out := out.push { prim := .And (r wA) (r wB), id := r g.id }
    | .Xor wA wB => out := out.push { prim := .Xor (r wA) (r wB), id := r g.id }
    | .Not wA    => out := out.push { prim := .Not (r wA),         id := r g.id }
    | .Const0    => out := out.push { prim := .Const0,              id := r g.id }
    | .Const1    => out := out.push { prim := .Const1,              id := r g.id }
  return (out, outs.map r)

