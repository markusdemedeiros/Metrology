import LibCrypto
import Init.Data.Nat.Bitwise.Basic

/-! # Toy implementation of some circuit garbling protocols

This roughly will follow the paper
  Two Halves Make a Whole
  Reducing Data Transfer in Garbled Circuits using Half Gates
  Samee Zahur, Mike Rosulek, and David Evans
-/

abbrev Wire := Nat

inductive GateT | And | Xor
  deriving Repr

def GateT.eval : GateT → Bool → Bool → Bool
| .And => and
| .Xor => xor

structure Gate where
  prim : GateT
  wA : Wire
  wB : Wire
  deriving Repr

/-- A circuit is a list of gates.
Each gate pushes its result to a list of wires, and each wire is indexed from the end of the list. -/
abbrev Circuit := List Gate


/- ## Spec evaluation of a circuit -/

section Evaluation

abbrev CircuitEvalM := StateT (List Bool) Id

def Gate.eval (g : Gate) (l : List Bool) : Bool :=
  let vA := l[g.wA]!
  let vB := l[g.wB]!
  g.prim.eval vA vB

def Circuit.eval (c : Circuit) : CircuitEvalM Unit :=
  match c with
  | [] => return
  | (g :: c) => do
    let l ← StateT.get
    StateT.set (g.eval l :: l)
    Circuit.eval c

end Evaluation

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




/- ## DSL for circuits with friendlier names -/

section CircuitDSL

declare_syntax_cat gate_type
declare_syntax_cat circuit_stmt

syntax "and" : gate_type
syntax "xor" : gate_type
syntax "input" ident : circuit_stmt
syntax ident " ← " gate_type ident ident : circuit_stmt

syntax "circuit(" circuit_stmt* ")" : term

private def findWire : List (String × Nat) → String → Option Nat
  | [], _ => none
  | (n, idx) :: rest, name => if n == name then some idx else findWire rest name

open Lean in
macro_rules
  | `(circuit( $stmts* )) => do
    let mut numInputs := 0
    for stmt in stmts do
      if let `(circuit_stmt| input $_:ident) := stmt then numInputs := numInputs + 1
    let mut inputIdx := 0
    let mut map : List (String × Nat) := []
    let mut gates : Array (TSyntax `term) := #[]
    for stmt in stmts do
      match stmt with
      | `(circuit_stmt| input $name:ident) =>
        map := map ++ [(toString name.getId, numInputs - 1 - inputIdx)]
        inputIdx := inputIdx + 1
      | `(circuit_stmt| $out:ident ← $gt:gate_type $a:ident $b:ident) =>
        let nA := toString a.getId
        let nB := toString b.getId
        let some idxA := findWire map nA | Macro.throwError s!"unknown wire: {nA}"
        let some idxB := findWire map nB | Macro.throwError s!"unknown wire: {nB}"
        let gtSyn ← match gt with
          | `(gate_type| and) => `(GateT.And)
          | `(gate_type| xor) => `(GateT.Xor)
          | _ => Macro.throwError "unknown gate type"
        gates := gates.push (← `({ prim := $gtSyn, wA := $(quote idxA), wB := $(quote idxB) : Gate}))
        map := map.map fun (n, idx) => (n, idx + 1)
        map := (toString out.getId, 0) :: map
      | _ => Macro.throwError "unknown circuit statement"
    `([$gates,*])

end CircuitDSL


/- ## Tests

`runCircuit c inputs` returns the full wire state after evaluation.
The input list is positional (index 0, 1, …).  The circuit DSL assigns inputs
in *reverse* declaration order, so `input A  input B` maps A → idx 1, B → idx 0.
Passing `[true, false]` therefore sets B = true, A = false.

Each gate prepends its result, so the output list reads newest-first:
for `input A  input B  C ← and A B  D ← xor A C`, the result is `[D, C, B, A]`. -/

section Tests

private def runCircuit (c : Circuit) (inputs : List Bool) : List Bool :=
  (c.eval.run inputs).2

private def andGate : Circuit := circuit(
  input A
  input B
  C ← and A B )

private def xorGate : Circuit := circuit(
  input A
  input B
  C ← xor A B )

private def twoGate : Circuit := circuit(
  input A
  input B
  C ← and A B
  D ← xor A C )

private def shadowGate : Circuit := circuit(
  input A
  input B
  A ← xor A B
  A ← and A B )

#guard
  ((Circuit.eval [{ prim := GateT.Xor, wA := 1, wB := 0 },
                 { prim := GateT.And, wA := 0, wB := 1 }]).run [true, true]).2 =
  [false, false, true, true]


#guard runCircuit andGate [true, true]   = [true, true, true]
#guard runCircuit andGate [true, false]  = [false, true, false]
#guard runCircuit andGate [false, true]  = [false, false, true]
#guard runCircuit andGate [false, false] = [false, false, false]

#guard runCircuit xorGate [true, true]   = [false, true, true]
#guard runCircuit xorGate [true, false]  = [true, true, false]
#guard runCircuit xorGate [false, true]  = [true, false, true]
#guard runCircuit xorGate [false, false] = [false, false, false]

#guard runCircuit twoGate [true, true]   = [false, true, true, true]
#guard runCircuit twoGate [true, false]  = [false, false, true, false]
#guard runCircuit twoGate [false, true]  = [true, false, false, true]
#guard runCircuit twoGate [false, false] = [false, false, false, false]

#guard runCircuit shadowGate [true, true]   = [false, false, true, true]
#guard runCircuit shadowGate [true, false]  = [true, true, true, false]
#guard runCircuit shadowGate [false, true]  = [false, true, false, true]
#guard runCircuit shadowGate [false, false] = [false, false, false, false]

private def adder : Circuit := circuit(
  input A
  input B
  input Cin
  AB   ← xor A B
  S    ← xor AB Cin
  AB2  ← and A B
  CAB  ← and Cin AB
  Cout ← xor AB2 CAB )

private def adderCorrect (a b cin : Bool) : Bool :=
  let r := runCircuit adder [cin, b, a]
  let cout := r[0]!
  let s    := r[3]!
  cout.toNat * 2 + s.toNat == a.toNat + b.toNat + cin.toNat

#guard adderCorrect false false false
#guard adderCorrect false false true
#guard adderCorrect false true  false
#guard adderCorrect false true  true
#guard adderCorrect true  false false
#guard adderCorrect true  false true
#guard adderCorrect true  true  false
#guard adderCorrect true  true  true

end Tests


