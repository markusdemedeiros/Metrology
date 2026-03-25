import Std.Data.HashMap

/- ## Word-level SHA-256
Reference: https://www.movable-type.co.uk/scripts/sha256.html
NOTE: THIS IS NOT A VERIFIED IMPLEMENTATION AND IT HAS NOT BEEN EXTENSIVELY TESTED.
NOTE: DO NOT ASSUME IT IS SECURE! -/

namespace SHA256

private def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

private def sigma0 (x : UInt32) : UInt32 := rotr x 7  ^^^ rotr x 18 ^^^ (x >>> 3)
private def sigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)
private def bigSigma0 (x : UInt32) : UInt32 := rotr x 2  ^^^ rotr x 13 ^^^ rotr x 22
private def bigSigma1 (x : UInt32) : UInt32 := rotr x 6  ^^^ rotr x 11 ^^^ rotr x 25
private def ch  (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (~~~ x &&& z)
private def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

private def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

private def H0 : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Compress a single 512-bit block (16 big-endian UInt32 words) into 8 hash words. -/
def block (msg : Array UInt32) : Array UInt32 := Id.run do
  -- Message schedule
  let mut W := msg
  for t in [16:64] do
    W := W.push (sigma1 W[t-2]! + W[t-7]! + sigma0 W[t-15]! + W[t-16]!)
  let mut a := H0[0]!; let mut b := H0[1]!; let mut c := H0[2]!; let mut d := H0[3]!
  let mut e := H0[4]!; let mut f := H0[5]!; let mut g := H0[6]!; let mut h := H0[7]!
  for t in [:64] do
    let t1 := h + bigSigma1 e + ch e f g + K[t]! + W[t]!
    let t2 := bigSigma0 a + maj a b c
    h := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
  return #[H0[0]! + a, H0[1]! + b, H0[2]! + c, H0[3]! + d,
           H0[4]! + e, H0[5]! + f, H0[6]! + g, H0[7]! + h]

/-- Pad and hash a single message ≤ 55 bytes (fits in one block). Input: big-endian UInt32 words. -/
def hashShort (msg : Array UInt32) : Array UInt32 := Id.run do
  let bitLen : UInt64 := (msg.size * 32).toUInt64
  let mut padded := msg
  padded := padded.push 0x80000000
  while padded.size < 15 do
    padded := padded.push 0
  padded := padded.push bitLen.toUInt32
  return block padded

end SHA256


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

/-- Hash a 128-bit key. Input as Nat, output as Nat (big-endian, truncated to 256 bits). -/
def SHA256.hashKey (k : Key) : Nat := Id.run do
  -- Split 128-bit Nat into 4 big-endian UInt32 words
  let w3 := (k &&& 0xFFFFFFFF).toUInt64.toUInt32
  let w2 := ((k >>> 32) &&& 0xFFFFFFFF).toUInt64.toUInt32
  let w1 := ((k >>> 64) &&& 0xFFFFFFFF).toUInt64.toUInt32
  let w0 := ((k >>> 96) &&& 0xFFFFFFFF).toUInt64.toUInt32
  let hash := hashShort #[w0, w1, w2, w3]
  -- Reassemble into a Nat
  let mut result : Nat := 0
  for i in [:8] do
    result := (result <<< 32) ||| hash[i]!.toNat
  return result

/-- Correlation-robust hash: H(x) = SHA256(x) ^^^ x, truncated to 128 bits. -/
def Key.sha256 (k : Key) : Key :=
  (SHA256.hashKey k ^^^ k) &&& ((2 ^ 128) - 1)

/- ## Lazy random functions of type Key → Key -/
structure RandomFunction where
  map : Std.HashMap Key Key := {}

namespace RandomFunction

def new : RandomFunction := {}

def hash (r : RandomFunction) (k : Key) : IO (RandomFunction × Key) :=
  match r.map[k]? with
  | some v => return (r, v)
  | none => do
    let v ← Key.gen
    return (⟨r.map.insert k v⟩, v)

def lookup (r : RandomFunction) (k : Key) : Option Key :=
  r.map[k]?

end RandomFunction




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

