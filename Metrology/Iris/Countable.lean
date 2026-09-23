module

public import Metrology.Approxis.AppWeakestpre
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Approxis.PrimitiveLaws
public import Metrology.ProbLang.Syntax.LocallyClosed
public import Iris.Instances.Lib.NaInvariants
public import Iris.Instances.Lib.Invariants

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS

namespace ProbLang


variable {rT : Type _} [ProbLangℝ rT]

/-! ## `Pos.Countable` instances for namespace indexing -/

theorem Pos.toNat_succ (p : Pos) : p.succ.toNat = p.toNat + 1 := by
  induction p with
  | xH => rfl
  | xI p ih => show 2 * p.succ.toNat = _; rw [ih]; simp [Pos.toNat]; ring
  | xO p => show 2 * p.toNat + 1 = _; simp [Pos.toNat]

theorem Pos.toNat_ofNat (n : Nat) : (Pos.ofNat n).toNat = n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [Pos.ofNat, Pos.toNat_succ, ih]

instance : Pos.Countable Nat where
  encode n := Pos.ofNat n
  decode p := some (p.toNat - 1)
  decode_encode n := by
    congr 1
    rw [Pos.toNat_ofNat]; omega

/-- Encode `Int` into `Nat` via the standard zigzag: `n ≥ 0 ↦ 2n`, `n < 0 ↦ -2n - 1`. -/
instance : Pos.Countable Int where
  encode z :=
    Pos.Countable.encode (A := Nat)
      (if 0 ≤ z then 2 * z.toNat else 2 * (-z - 1).toNat + 1)
  decode p := (Pos.Countable.decode (A := Nat) p).bind fun k =>
    some (if k % 2 = 0 then (k / 2 : Int) else -((k - 1) / 2 : Int) - 1)
  decode_encode z := by
    show Option.bind
      (Pos.Countable.decode (A := Nat)
        (Pos.Countable.encode (A := Nat)
          (if 0 ≤ z then 2 * z.toNat else 2 * (-z - 1).toNat + 1))) _ = _
    rw [Pos.Countable.decode_encode]
    show (Option.bind (some _) _ : Option Int) = _
    rw [Option.bind_some]
    by_cases hz : 0 ≤ z
    · rw [if_pos hz]
      have hmod : (2 * z.toNat) % 2 = 0 := Nat.mul_mod_right 2 _
      rw [if_pos hmod]
      have htn : (z.toNat : Int) = z := Int.toNat_of_nonneg hz
      have : (((2 * z.toNat : Nat) : Int) / 2) = z := by
        push_cast; rw [Int.mul_ediv_cancel_left _ (by decide : (2 : Int) ≠ 0)]; exact htn
      rw [this]
    · rw [if_neg hz]
      have hmod : (2 * (-z - 1).toNat + 1) % 2 ≠ 0 := by
        intro h; omega
      rw [if_neg hmod]
      have hnn : (0 : Int) ≤ -z - 1 := by omega
      have htn : ((-z - 1).toNat : Int) = -z - 1 := Int.toNat_of_nonneg hnn
      have hd : ((((2 * (-z - 1).toNat + 1 : Nat) : Int) - 1) / 2) = -z - 1 := by
        push_cast
        rw [show (2 * ((-z - 1).toNat : Int) + 1 - 1) = 2 * (-z - 1) by rw [htn]; ring]
        rw [Int.mul_ediv_cancel_left _ (by decide : (2 : Int) ≠ 0)]
      rw [hd]
      congr 1; omega

instance {A B : Type} [Pos.Countable A] [Pos.Countable B] : Pos.Countable (A × B) where
  encode p := Pos.flatten [Pos.Countable.encode p.1, Pos.Countable.encode p.2]
  decode p := match Pos.unflatten p with
    | some [a, b] =>
      (Pos.Countable.decode a).bind fun x =>
      (Pos.Countable.decode b).bind fun y =>
      some (x, y)
    | _ => none
  decode_encode p := by
    show (match Pos.unflatten
        (Pos.flatten [Pos.Countable.encode p.1, Pos.Countable.encode p.2]) with
      | _ => _) = _
    rw [Pos.unflatten_flatten]
    show Option.bind (Pos.Countable.decode (Pos.Countable.encode p.1)) _ = _
    rw [Pos.Countable.decode_encode]
    show Option.bind (Pos.Countable.decode (Pos.Countable.encode p.2)) _ = _
    rw [Pos.Countable.decode_encode]
    rfl
