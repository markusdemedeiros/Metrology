import MicroCircuit.Circuits

-- SHA-256 implementation based off of
-- https://www.movable-type.co.uk/scripts/sha256.html

def fullAdder (a b cin : Wire) : CircuitBuilderM (Wire × Wire) := do
  let ab   ← xor1 a b
  let s    ← xor1 ab cin
  let ab2  ← and1 a b
  let cab  ← and1 cin ab
  let cout ← xor1 ab2 cab
  return (s, cout)

def rippleCarry (a b : Bundle n) (cin : Wire) : CircuitBuilderM (Bundle n × Wire) := do
  let mut carry := cin
  let mut sums : Array Wire := #[]
  for i in [:n] do
    let (s, c) ← fullAdder a.wires[i]! b.wires[i]! carry
    sums := sums.push s
    carry := c
  return (⟨sums⟩, carry)

def add32 (a b : Bundle 32) : CircuitBuilderM (Bundle 32) := do
  let z ← const0
  let (sum, _) ← rippleCarry a b z
  return sum

/- ## SHA-256 logical functions -/

-- Σ0(x) = ROTR(2,x) ^ ROTR(13,x) ^ ROTR(22,x)
def sha256_bigSigma0 (x : Bundle 32) : CircuitBuilderM (Bundle 32) := do
  let a ← xorN (rotrN x 2) (rotrN x 13)
  xorN a (rotrN x 22)

-- Σ1(x) = ROTR(6,x) ^ ROTR(11,x) ^ ROTR(25,x)
def sha256_bigSigma1 (x : Bundle 32) : CircuitBuilderM (Bundle 32) := do
  let a ← xorN (rotrN x 6) (rotrN x 11)
  xorN a (rotrN x 25)

-- σ0(x) = ROTR(7,x) ^ ROTR(18,x) ^ (x >>> 3)
def sha256_sigma0 (x : Bundle 32) : CircuitBuilderM (Bundle 32) := do
  let z ← const0
  let a ← xorN (rotrN x 7) (rotrN x 18)
  xorN a (shrN x 3 z)

-- σ1(x) = ROTR(17,x) ^ ROTR(19,x) ^ (x >>> 10)
def sha256_sigma1 (x : Bundle 32) : CircuitBuilderM (Bundle 32) := do
  let z ← const0
  let a ← xorN (rotrN x 17) (rotrN x 19)
  xorN a (shrN x 10 z)

-- Ch(x,y,z) = (x & y) ^ (~x & z)
def sha256_Ch (x y z : Bundle 32) : CircuitBuilderM (Bundle 32) := do
  let xy ← andN x y
  let nx ← notN x
  let nxz ← andN nx z
  xorN xy nxz

-- Maj(x,y,z) = (x & y) ^ (x & z) ^ (y & z)
def sha256_Maj (x y z : Bundle 32) : CircuitBuilderM (Bundle 32) := do
  let xy ← andN x y
  let xz ← andN x z
  let yz ← andN y z
  let a ← xorN xy xz
  xorN a yz

def SHA256_CONST_K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 ]

def SHA256_CONST_H : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]

/-- SHA-256 compression of a single pre-padded 512-bit block.
    Input: 16 × 32-bit words. Output: 8 × 32-bit words. -/
def sha256_block (msg : Array (Bundle 32))
    : CircuitBuilderM (Array (Bundle 32)) := do
  let mut W : Array (Bundle 32) := msg
  for t in [16:64] do
    -- W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]
    let s1 ← sha256_sigma1 W[t-2]!
    let s0 ← sha256_sigma0 W[t-15]!
    let w ← add32 s1 W[t-7]!
    let w ← add32 w s0
    let w ← add32 w W[t-16]!
    W := W.push w

  -- Initial hash values
  let mut H : Array (Bundle 32) := #[]
  for i in [:8] do
    H := H.push (← const32 SHA256_CONST_H[i]!)

  -- Initialize working variables
  let mut a := H[0]!
  let mut b := H[1]!
  let mut c := H[2]!
  let mut d := H[3]!
  let mut e := H[4]!
  let mut f := H[5]!
  let mut g := H[6]!
  let mut h := H[7]!

  -- 64-round compression loop
  for t in [:64] do
    let k ← const32 SHA256_CONST_K[t]!
    -- T1 = h + Σ1(e) + Ch(e,f,g) + K[t] + W[t]
    let sig1 ← sha256_bigSigma1 e
    let ch ← sha256_Ch e f g
    let t1 ← add32 h sig1
    let t1 ← add32 t1 ch
    let t1 ← add32 t1 k
    let t1 ← add32 t1 W[t]!
    -- T2 = Σ0(a) + Maj(a,b,c)
    let sig0 ← sha256_bigSigma0 a
    let maj ← sha256_Maj a b c
    let t2 ← add32 sig0 maj
    -- Rotate working variables
    h := g
    g := f
    f := e
    e ← add32 d t1
    d := c
    c := b
    b := a
    a ← add32 t1 t2

  -- Final addition: H[i] += working var
  let results := #[
    ← add32 H[0]! a, ← add32 H[1]! b, ← add32 H[2]! c, ← add32 H[3]! d,
    ← add32 H[4]! e, ← add32 H[5]! f, ← add32 H[6]! g, ← add32 H[7]! h
  ]
  return results
