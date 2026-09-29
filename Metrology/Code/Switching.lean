module

public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.Syntax.LocallyClosed
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Programs for the PRF/PRP switching lemma

Ports the object-language code behind `clutch/theories/approxis/examples/prp_prf_weak.v`:

* association-list maps in one heap cell (`initMap`/`getMap`/`setMap`), storing a pure
  assoc-list *value* rather than clutch's linked heap cells — observationally the same
  interface, far less heap reasoning;
* the idealised random function (`randomFunction`): memoise a fresh `rand N` per query;
* the idealised random permutation (`randomPermutation`): a map of past queries plus a
  ref holding the list of unsampled values, sampling uniformly from the remainder;
* the "weak" games `wPRF`/`wPRP`: query the oracle `Q` times at uniform inputs and
  return the list of (input, output) pairs.

Verified in `Metrology/Approxis/Examples/`. -/

namespace ProbLang

variable {rT : Type _}

namespace Switching

/-! ## Pure list values

A list value is `inl ()` (nil) or `inr (x, rest)` (cons). -/

/-- The value of a list of integers. -/
def intListVal : List Int → Val rT
  | [] => .inl .unit
  | n :: l => .inr (.pair (.int n) (intListVal l))

/-- The value of an integer association list (leftmost binding wins). -/
def assocVal : List (Int × Int) → Val rT
  | [] => .inl .unit
  | (k, y) :: m => .inr (.pair (.pair (.int k) (.int y)) (assocVal m))

/-! ## List programs -/

/-- Length of a list value. -/
@[pl_fold] def listLength : Exp rT := pl%
  rec len l :=
    case! l
    | inl(_u) => #0
    | inr(p) => #1 + len (snd(p))

/-- Remove the `i`-th element: `SOME (elem, rest)`, or `NONE` when out of range. -/
@[pl_fold] def listRemoveNth : Exp rT := pl%
  rec rem l i :=
    case! l
    | inl(_u) => inl(#.unit)
    | inr(p) =>
      if i = #0 then inr((fst(p), snd(p)))
      else
        case! (rem (snd(p)) (i - #1))
        | inl(_u) => inl(#.unit)
        | inr(q) => inr((fst(q), inr((fst(p), snd(q)))))

/-! ## Association-list maps in a single cell -/

/-- Look up key `k` in an assoc-list value (leftmost match wins). -/
@[pl_fold] def findList : Exp rT := pl%
  rec find l k :=
    case! l
    | inl(_u) => inl(#.unit)
    | inr(p) => if fst(fst(p)) = k then inr(snd(fst(p))) else find (snd(p)) k

/-- Allocate an empty map. -/
def initMap : Exp rT := pl% fun _u, alloc(inl(#.unit))

/-- `getMap m k`: `SOME v` if `k ↦ v` is in the map, else `NONE`. -/
@[pl_fold] def getMap : Exp rT := pl% fun m k, &findList (!m) k

/-- `setMap m k v`: bind `k ↦ v` (shadowing any previous binding). -/
@[pl_fold] def setMap : Exp rT := pl% fun m k v, m ← inr(((k, v), !m))

/-! ## The idealised random function -/

/-- The query closure of the random function over map location `ℓ`: on a fresh
input draw `rand N`, memoise it, and return it; on a repeat input return the
memoised answer. -/
def rfQuery (N : Int) (ℓ : Loc) : Exp rT := pl%
  fun x,
    case! (&getMap #(.loc ℓ) x)
    | inl(_u) => (let y := rand(#(.int N), #.unit); &setMap #(.loc ℓ) x y; y)
    | inr(y) => y

/-- An idealised random function with output space `[0, N)`. -/
def randomFunction (N : Int) : Exp rT := pl%
  let m := &initMap #.unit;
  fun x,
    case! (&getMap m x)
    | inl(_u) => (let y := rand(#(.int N), #.unit); &setMap m x y; y)
    | inr(y) => y

/-! ## The idealised random permutation -/

/-- The query closure of the random permutation over map location `ℓm` and
fresh-values location `ℓfv`: on a fresh input, sample an index into the list of
unsampled values, remove it, and memoise it. -/
def prpQuery (ℓm ℓfv : Loc) : Exp rT := pl%
  fun x,
    case! (&getMap #(.loc ℓm) x)
    | inl(_u) =>
      (let ln := &listLength (!#(.loc ℓfv));
       let n := rand(ln, #.unit);
       case! (&listRemoveNth (!#(.loc ℓfv)) n)
       | inl(_u) => #0
       | inr(p) => (&setMap #(.loc ℓm) x (fst(p)); #(.loc ℓfv) ← snd(p); fst(p)))
    | inr(y) => y

/-- An idealised random permutation of `[0, N)`: the fresh-values list starts as
`[0, …, N-1]`. -/
def randomPermutation (N : Int) : Exp rT := pl%
  let fv := alloc({(intListVal ((List.range N.toNat).map Int.ofNat)).1});
  let m := &initMap #.unit;
  fun x,
    case! (&getMap m x)
    | inl(_u) =>
      (let ln := &listLength (!fv);
       let n := rand(ln, #.unit);
       case! (&listRemoveNth (!fv) n)
       | inl(_u) => #0
       | inr(p) => (&setMap m x (fst(p)); fv ← snd(p); fst(p)))
    | inr(y) => y

/-! ## The weak PRF/PRP games

Query the oracle at `Q` uniform inputs, collecting the (input, output) pairs. -/

/-- The query loop of the weak games: `wLoop N f res i` queries the oracle `f` at
`i` uniform inputs from `[0, N)`, consing each (input, output) pair onto the
accumulator location `res`. -/
@[pl_fold] def wLoop (N : Int) : Exp rT := pl%
  rec loop f res i :=
    if i = #0 then #.unit
    else
      (let x := rand(#(.int N), #.unit);
       let y := f x;
       res ← inr(((x, y), !res));
       loop f res (i - #1))

/-- The weak PRF game: `Q` queries to an idealised random function at uniform
inputs, returning the list of (input, output) pairs. -/
def wPRF (N Q : Int) : Exp rT := pl%
  let f := {randomFunction N};
  let res := alloc(inl(#.unit));
  {wLoop N} f res #(.int Q);
  !res

/-- The weak PRP game: `Q` queries to an idealised random permutation at uniform
inputs, returning the list of (input, output) pairs. -/
def wPRP (N Q : Int) : Exp rT := pl%
  let f := {randomPermutation N};
  let res := alloc(inl(#.unit));
  {wLoop N} f res #(.int Q);
  !res

/-! ## `openRec`/`closeRec` erasure (`pl_step_simp`)

The library constants are closed programs, so `openRec`/`closeRec` on them are the
identity. Registering the identities in `pl_step_simp` lets the step tactics erase
the stuck wrappers that β-substitution leaves around a constant referenced under
binders, instead of forcing every later `whnf` to re-evaluate the constant's body. -/

theorem findList_fv : (findList : Exp rT).fv = ∅ := rfl
theorem listLength_fv : (listLength : Exp rT).fv = ∅ := rfl
theorem listRemoveNth_fv : (listRemoveNth : Exp rT).fv = ∅ := rfl
theorem initMap_fv : (initMap : Exp rT).fv = ∅ := rfl
theorem getMap_fv : (getMap : Exp rT).fv = ∅ := rfl
theorem setMap_fv : (setMap : Exp rT).fv = ∅ := rfl
theorem rfQuery_fv (N : Int) (ℓ : Loc) : (rfQuery N ℓ : Exp rT).fv = ∅ := rfl
theorem prpQuery_fv (ℓm ℓfv : Loc) : (prpQuery ℓm ℓfv : Exp rT).fv = ∅ := rfl
theorem randomFunction_fv (N : Int) : (randomFunction N : Exp rT).fv = ∅ := rfl

@[pl_step_simp] theorem openRec_findList (k : Nat) (t : Exp rT) :
    Exp.openRec k t (findList : Exp rT) = findList :=
  (Exp.open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_findList (k : Nat) (x : Var) :
    Exp.closeRec k x (findList : Exp rT) = findList :=
  Exp.closeRec_fresh x _ k (by simp [findList_fv])

@[pl_step_simp] theorem openRec_listLength (k : Nat) (t : Exp rT) :
    Exp.openRec k t (listLength : Exp rT) = listLength :=
  (Exp.open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_listLength (k : Nat) (x : Var) :
    Exp.closeRec k x (listLength : Exp rT) = listLength :=
  Exp.closeRec_fresh x _ k (by simp [listLength_fv])

@[pl_step_simp] theorem openRec_listRemoveNth (k : Nat) (t : Exp rT) :
    Exp.openRec k t (listRemoveNth : Exp rT) = listRemoveNth :=
  (Exp.open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_listRemoveNth (k : Nat) (x : Var) :
    Exp.closeRec k x (listRemoveNth : Exp rT) = listRemoveNth :=
  Exp.closeRec_fresh x _ k (by simp [listRemoveNth_fv])

@[pl_step_simp] theorem openRec_initMap (k : Nat) (t : Exp rT) :
    Exp.openRec k t (initMap : Exp rT) = initMap :=
  (Exp.open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_initMap (k : Nat) (x : Var) :
    Exp.closeRec k x (initMap : Exp rT) = initMap :=
  Exp.closeRec_fresh x _ k (by simp [initMap_fv])

@[pl_step_simp] theorem openRec_getMap (k : Nat) (t : Exp rT) :
    Exp.openRec k t (getMap : Exp rT) = getMap :=
  (Exp.open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_getMap (k : Nat) (x : Var) :
    Exp.closeRec k x (getMap : Exp rT) = getMap :=
  Exp.closeRec_fresh x _ k (by simp [getMap_fv])

@[pl_step_simp] theorem openRec_setMap (k : Nat) (t : Exp rT) :
    Exp.openRec k t (setMap : Exp rT) = setMap :=
  (Exp.open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_setMap (k : Nat) (x : Var) :
    Exp.closeRec k x (setMap : Exp rT) = setMap :=
  Exp.closeRec_fresh x _ k (by simp [setMap_fv])

@[pl_step_simp] theorem openRec_rfQuery (k : Nat) (t : Exp rT) (N : Int) (ℓ : Loc) :
    Exp.openRec k t (rfQuery N ℓ : Exp rT) = rfQuery N ℓ :=
  (Exp.open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_rfQuery (k : Nat) (x : Var) (N : Int) (ℓ : Loc) :
    Exp.closeRec k x (rfQuery N ℓ : Exp rT) = rfQuery N ℓ :=
  Exp.closeRec_fresh x _ k (by simp [rfQuery_fv])

@[pl_step_simp] theorem openRec_prpQuery (k : Nat) (t : Exp rT) (ℓm ℓfv : Loc) :
    Exp.openRec k t (prpQuery ℓm ℓfv : Exp rT) = prpQuery ℓm ℓfv :=
  (Exp.open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_prpQuery (k : Nat) (x : Var) (ℓm ℓfv : Loc) :
    Exp.closeRec k x (prpQuery ℓm ℓfv : Exp rT) = prpQuery ℓm ℓfv :=
  Exp.closeRec_fresh x _ k (by simp [prpQuery_fv])

@[pl_step_simp] theorem openRec_randomFunction (k : Nat) (t : Exp rT) (N : Int) :
    Exp.openRec k t (randomFunction N : Exp rT) = randomFunction N :=
  (Exp.open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_randomFunction (k : Nat) (x : Var) (N : Int) :
    Exp.closeRec k x (randomFunction N : Exp rT) = randomFunction N :=
  Exp.closeRec_fresh x _ k (by simp [randomFunction_fv])

theorem wLoop_fv (N : Int) : (wLoop N : Exp rT).fv = ∅ := rfl

@[pl_step_simp] theorem openRec_wLoop (k : Nat) (t : Exp rT) (N : Int) :
    Exp.openRec k t (wLoop N : Exp rT) = wLoop N :=
  (Exp.open_lc k t _ (by is_lc)).symm
@[pl_step_simp] theorem closeRec_wLoop (k : Nat) (x : Var) (N : Int) :
    Exp.closeRec k x (wLoop N : Exp rT) = wLoop N :=
  Exp.closeRec_fresh x _ k (by simp [wLoop_fv])

end Switching
end ProbLang
