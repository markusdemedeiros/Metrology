module

public import Std
public import Std.Data.ExtTreeMap.Lemmas
public import Mathlib.Data.Countable.Basic
public import Mathlib.Logic.Equiv.List

@[expose] public section

/-# Dumping ground for lemmas that belong in Std, or Mathlib/Data. -/

namespace Std

def ExtTreeMap.fresh (t : ExtTreeMap Int V) : Int :=
  match t.maxKey? with | none => 1 | some v => v + 1

theorem ExtTreeMap.fresh_get? (t : ExtTreeMap Int V) :
    t[t.fresh]? = none := by
  unfold ExtTreeMap.fresh
  rcases HM : t.maxKey? with _ | v
  · simp [maxKey?_eq_none_iff.mp HM]
  · apply getElem?_eq_none
    intro hmem
    have hle := ExtTreeMap.le_maxKey?_of_mem hmem (Option.get_of_eq_some (isSome_maxKey?_of_mem hmem) HM)
    simp [compare, compareOfLessAndEq] at hle
    split at hle; grind
    split at hle; grind
    simp_all

end Std


instance instCountableChar : Countable Char where
  exists_injective_nat' := by
    exists (·.1.toNat)
    rintro ⟨v1, _⟩ ⟨v2, _⟩
    simp only [Char.mk.injEq]
    exact UInt32.toNat_inj.mp

instance instCountableString : Countable String where
  exists_injective_nat' := by
    have ⟨f, Hf⟩ : Countable (List Char) := by infer_instance
    exists (fun s => f s.toList)
    exact fun _ _ H => String.toList_inj.mp (Hf H)
