import Std

/-- Convert the number `val` into a numBytes-sized little-endian ByteArray.
Return `none` if val does not fit. -/
def Nat.toByteArrayLE (val : Nat) (numBytes : Nat) : Option ByteArray := Id.run do
  let mut v := val
  let mut ba : ByteArray := .emptyWithCapacity numBytes
  for _ in [:numBytes] do
    ba := ba.push (v % 256).toUInt8
    v := v / 256
  if v = 0 then return ba else none

/-- Convert a little-endian ByteArray into a natural number. -/
def Nat.ofByteArrayLE (ba : ByteArray) : Nat := Id.run do
  let mut acc : Nat := 0
  for i in [:ba.size] do
    acc := acc + ba[i]!.toNat <<< (i * 8)
  return acc

namespace LibCrypto

@[extern "enc_aes128_c"]
opaque encAes128 : ByteArray → ByteArray → ByteArray → ByteArray

@[extern "dec_aes128_c"]
opaque decAes128 : ByteArray → ByteArray → ByteArray → ByteArray

@[extern "sha256_c"]
opaque sha256 : ByteArray → ByteArray

end LibCrypto
