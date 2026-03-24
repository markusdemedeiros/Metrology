abbrev Key := Nat

namespace Key

def colour (k : Key) : Bool := k &&& 1 == 1

def set_colour (k : Key) (b : Bool) : Key :=
  (0xFFFFFFFE &&& k) ||| b.toNat

/-- Generate a random 128-bit key. -/
def gen : IO Key := IO.rand 0 ((2 ^ 128) - 1)

/-- Generate a key pair for a wire: two 128-bit keys with opposite LSBs. -/
def gen_colour_pair : IO (Key × Key) := do
  let ka ← gen
  let kb ← gen
  return (ka, kb.set_colour !ka.colour)

def encrypt (k : Key) (p : Nat) : Nat := k ^^^ p

def decrypt (k : Key) (c : Nat) : Nat := k ^^^ c

def nil : Key := 0

end Key

def Table (α : Type _) : Type _ := α × α × α × α

namespace Table

def set (t : Table α) (ci cj : Bool) (v : α) : Table α :=
  let ⟨t00, t01, t10, t11⟩ := t
  match ci, cj with
  | false, false => ⟨v, t01, t10, t11⟩
  | false, true  => ⟨t00, v, t10, t11⟩
  | true, false  => ⟨t00, t01, v, t11⟩
  | true, true   => ⟨t00, t01, t10, v⟩

def get (t : Table α) (ci cj : Bool) : α :=
  let ⟨t00, t01, t10, t11⟩ := t
  match ci, cj with
  | false, false => t00
  | false, true  => t01
  | true, false  => t10
  | true, true   => t11

end Table

