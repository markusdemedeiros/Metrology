import LibCrypto
import Init.Data.Nat.Bitwise.Basic

/-! # Toy implementation of some circuit garbling protocols

This roughly will follow the paper
  Two Halves Make a Whole
  Reducing Data Transfer in Garbled Circuits using Half Gates
  Samee Zahur, Mike Rosulek, and David Evans
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

/-- A circuit is a list of gates.
Each gate pushes its result to a list of wires, and each wire is indexed from the end of the list. -/
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

/-- Right shift by a constant — shifted-in positions become wire 0 from a constant-zero bundle.
    Requires a bundle of constant-zero wires to fill the top bits. -/
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


/-

/-- Generate a 16-byte key -/
def keygen : IO Nat := IO.rand 0 ((2 ^ 128) - 1)

/-- Generate a permutation bit -/
def permgen : IO Bool := do
  let n ← (IO.rand 0 1)
  return n = 1

-- It's not good practice, but I'm going to use a constant IV for all encryptions
-- while I figure out how these things work
abbrev IV := Nat
def GARBLE_IV : IV := 0xBEEF
#guard GARBLE_IV < 2^16

/-! ## A basic circuit garbling procedure, using the point-and-premute technique. -/

section BasicGarbling

-- Each wire in the circuit gets:
--    A "truth" key
--    A "false" key
--    A permutation bit, chosen at random
--
-- Each gate is turned into a table.
--    Arrange the table entrues in order, then permute groups according to if the permutation
--    bits on the input lines are set.
--    Table entries are encrypted with the appropriate A key, then the B key, and as text they
--    contain the truth/falsity key for the output, plus the permutation bit of the output.


-- The payload we encrypt/decrypt is meant to be a key/bit pair
-- To support this we add encode/decode functions

/-- A 16 byte key -/
abbrev Key := Nat

structure WireState where
  /-- A truthity or falsity key associated to the current wire -/
  key : Key
  /-- The permute bit associated to the wire's truthity/falsity wire -/
  perm : Bool

-- Every encoding should fit in 256 bytes
abbrev Encoding := Nat

-- Encode a WireState as a 256-byte number
def WireState.encode (w : WireState) : Encoding :=
  w.key + (w.perm.toNat <<< 128)

def Encoding.decode (e : Encoding) : WireState where
  key := e &&& (2^128 - 1)
  perm := (e >>> 128) == 1

theorem WireState.encode_decode {w : WireState} (Hk : w.key < 2^128) :
    w.encode.decode = w := by
  obtain ⟨k, p⟩ := w
  simp only [WireState.encode, Encoding.decode, Nat.shiftLeft_eq, mk.injEq] at Hk ⊢
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  cases p <;> simp [Bool.toNat, Nat.add_mod_right, Nat.mod_eq_of_lt Hk,
    Nat.add_div_right _ (by omega : (0:Nat) < 2^128), Nat.div_eq_of_lt Hk] <;> omega

-- #eval Encoding.decode (WireState.encode ⟨2^128-1, false⟩)

def Table (α : Type _ ) : Type _ := α × α × α × α

def Table.set (t : Table α) (ci cj : Bool) (v : α) : Table α :=
  let ⟨t00, t01, t10, t11⟩ := t
  match ci, cj with
  | false, false => ⟨v, t01, t10, t11⟩
  | false, true  => ⟨t00, v, t10, t11⟩
  | true, false  => ⟨t00, t01, v, t11⟩
  | true, true   => ⟨t00, t01, t10, v⟩

def Table.get (t : Table α) (ci cj : Bool) : α :=
  let ⟨t00, t01, t10, t11⟩ := t
  match ci, cj with
  | false, false => t00
  | false, true  => t01
  | true, false  => t10
  | true, true   => t11

-- def Table.πA : Table α → Table α | ⟨t1, t2, t3, t4⟩ => ⟨t3, t4, t1, t2⟩
-- def Table.πB : Table α → Table α | ⟨t1, t2, t3, t4⟩ => ⟨t2, t1, t4, t3⟩
-- def Table.permA (t : Table α) (b : Bool) : Table α := if b then t.πA else t
-- def Table.permB (t : Table α) (b : Bool) : Table α := if b then t.πB else t

/--
Each wire gets a key for its truthity and falsity.
It also gets a random permute bit: Each label gets (perm_r xor t) where t is its truthity.
-/
structure GarbleState where
  key_true : List Nat
  key_false : List Nat
  perm_r : List Bool
  tables : List (Table ByteArray)

/-- The `select` bit in the payload. The select bit is the same as the global perm_true
bit when the wire represents truth.

(Check?) the location of a row in the table depends both on the truthity of the inputs
and the random permute bits, we can leak the select bits without leaking information?
-/
def select (permute truth : Bool) : Bool :=
  if truth then permute else ¬ permute

def GarbleState.key (g : GarbleState) (b : Bool) (id : Nat) : Nat :=
  if b then g.key_true[id]! else g.key_false[id]!

abbrev GarbleM := StateT GarbleState IO

-- Encrypt a WireState by two keys
def encryptTableEntry (k1 k2 : Key) (payload : WireState) : ByteArray :=
  let enc_256 := payload.encode.toByteArrayLE 32 |>.get!
  let iv_128  := GARBLE_IV.toByteArrayLE 16 |>.get!
  let k1_128  := k1.toByteArrayLE 16 |>.get!
  let k2_128  := k2.toByteArrayLE 16 |>.get!
  let cipher2 := LibCrypto.encAes128 enc_256 iv_128 k2_128
  let cipher1 := LibCrypto.encAes128 cipher2 iv_128 k1_128
  cipher1

def decryptTableEntry (k1 k2 : Key) (cipher1 : ByteArray) : WireState :=
  let iv_128  := GARBLE_IV.toByteArrayLE 16 |>.get!
  let k1_128  := k1.toByteArrayLE 16 |>.get!
  let k2_128  := k2.toByteArrayLE 16 |>.get!
  let cipher2 := LibCrypto.decAes128 cipher1 iv_128 k1_128
  let plaintx := LibCrypto.decAes128 cipher2 iv_128 k2_128
  Encoding.decode (Nat.ofByteArrayLE plaintx)


/--
  k1 k2 k3 : functions returning the true/false keys for wires 1, 2 and output
  r1 r2 r3 : permutation bits for wires 1, 2 and output
  f : function describing the gate

  Produces a table of encrypted, and permuted values.

  This is a fairly naive imperative implementation and could be simplified with
  eg. the swap primitive.
-/
def encryptTable (ki kj kk : Bool → Key) (ri rj rk : Bool) (f : Bool → Bool → Bool) :
    Id (Table ByteArray) := do
  let mut t : Table ByteArray := ⟨.empty, .empty, .empty, .empty⟩
  for vi in [false, true] do
    for vj in [false, true] do
      let pi := xor vi ri
      let pj := xor vj rj
      let vk := f vi vj
      let pk := xor vk rk
      let E : WireState := { key := kk vk, perm := pk }
      t := t.set pi pj (encryptTableEntry (ki vi) (kj vj) E)
  return t

def decryptTable (wi wj : WireState) (t : Table ByteArray) : Id WireState := do
  let ⟨ki, si⟩ := wi
  let ⟨kj, sj⟩ := wj
  decryptTableEntry ki kj (t.get si sj)


/-- Garble an entire circuit. For each gate, generate fresh keys and a permutation bit
for the output wire, then encrypt the gate's truth table. -/
instance : Inhabited WireState := ⟨{ key := 0, perm := false }⟩

def garbleCircuit (c : Circuit) : GarbleM Unit :=
  match c with
  | [] => return
  | (g :: c) => do
    let s ← StateT.get
    let kt ← keygen
    let kf ← keygen
    let r  ← permgen
    let ki := fun b => s.key b g.wA
    let kj := fun b => s.key b g.wB
    let ri := s.perm_r[g.wA]!
    let rj := s.perm_r[g.wB]!
    let kk := fun b => if b then kt else kf
    let t : Table ByteArray := encryptTable ki kj kk ri rj r g.prim.eval
    StateT.set {
      key_true  := kt :: s.key_true
      key_false := kf :: s.key_false
      perm_r    := r  :: s.perm_r
      tables    := s.tables ++ [t]
    }
    garbleCircuit c

/-- Evaluate a garbled circuit. Given initial wire labels and garbled tables,
decrypt each gate's table using the two input wire labels to obtain the output label. -/
def evalGarbledCircuit (c : Circuit) (tables : List (Table ByteArray))
    (wires : List WireState) : List WireState :=
  match c, tables with
  | [], _ => wires
  | (g :: c), (t :: tables) =>
    let wi := wires[g.wA]!
    let wj := wires[g.wB]!
    let wk : WireState := decryptTable wi wj t
    evalGarbledCircuit c tables (wk :: wires)
  | (_ :: _), [] => wires  -- shouldn't happen if tables match circuit

end BasicGarbling
-/
