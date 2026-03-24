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
  | Const0
  | Const1
  deriving Repr

def GateT.eval : GateT Bool → Bool
  | .And wA wB => and wA wB
  | .Xor wA wB => xor wA wB
  | .Not wA => !wA
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
  const0s : Nat := 0
  const1s : Nat := 0
  deriving Repr

def GateCounts.total (gc : GateCounts) : Nat :=
  gc.ands + gc.xors + gc.nots + gc.const0s + gc.const1s

instance : ToString GateCounts where
  toString gc :=
    s!"AND: {gc.ands}, XOR: {gc.xors}, NOT: {gc.nots}, Const0: {gc.const0s}, Const1: {gc.const1s}, Total: {gc.total}"

def Circuit.gateCounts (c : Circuit) : GateCounts :=
  c.foldl (init := {}) fun gc g =>
    match g.prim with
    | .And _ _  => { gc with ands := gc.ands + 1 }
    | .Xor _ _  => { gc with xors := gc.xors + 1 }
    | .Not _    => { gc with nots := gc.nots + 1 }
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


/-
/-! ## Constant propagation optimization in a circuit -/

section ConstantProp

structure CPAbstractCircuitState where
  pc : Nat
  wires : Array (Option Bool)

abbrev CPAbstractCircuitEvalM := StateT CPAbstractCircuitState Id

def CPsetWireVal (i : Nat) (b : Bool) : CPAbstractCircuitEvalM Unit :=
  modifyGet (fun σ => ((), { σ with wires := σ.wires.set! i b }))

def CPgetWireVal (i : Nat) : CircuitEvalM Bool := do
  let σ ← get
  return σ.wires[i]!

-- Read the state, return a gate that does the same thing.
def Gate.constProp (g : Gate) : CPAbstractCircuitEvalM Gate :=
  match g.prim with
  | .And wA wB => do
    sorry
    -- let vA ← getWireVal wA
    -- let vB ← getWireVal wB
    -- return GateT.eval (.And vA vB)
  | .Xor wA wB => do
    sorry
    -- let vA ← getWireVal wA
    -- let vB ← getWireVal wB
    -- return GateT.eval (.Xor vA vB)
  | .Not wA => do
    sorry
    -- let vA ← getWireVal wA
    -- return GateT.eval (.Not vA)
  | .Const0 =>
    sorry
    -- return false
  | .Const1 =>
    sorry
    -- return true
--
-- def Circuit.eval (c : Circuit) : CircuitEvalM Unit := do
--   for g in c do
--     let v ← g.eval
--     let w ← getFreshWire
--     setWireVal w v

end ConstantProp

/-! ## Dead code elimination through a circuit -/

section DeadCodeProp

end DeadCodeProp
-/
