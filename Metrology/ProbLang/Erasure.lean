import Metrology.ProbLang.Erasable
import Metrology.ProbLang.Metatheory

/-!
# Erasure: presampling on tapes is invisible

Port of `theories/prob_lang/erasure.v` from Clutch, reformulated to avoid
introducing a language-level `state_step` primitive.

The headline theorem `exec_tape_presample_invariant` says: appending a
uniformly-sampled value onto an *existing* tape `α` of `σ` does not change
`execN m ⟨e, σ⟩`. Equivalently, the local "uniform presample" distribution
on `State`, obtained by binding a uniform sample onto tape `α`, is
`Erasable` at `σ`.

All `state_step`-specialized corollaries of Clutch's `erasure.v` are dropped
in favor of the general `*_erasable` wrappers, which take an arbitrary
erasable `μ : Measure State` and do the lifting. Clients that want the
"uniform presample" instance must construct `tapePresample` themselves and
invoke `tapePresample_erasable` to get the `Erasable` witness.
-/

namespace ProbLang

open MeasureTheory Measure

/-! ## Local uniform-presample distribution

These are file-local helpers used to *state* erasure, without adding any
new primitives to the language. In particular, `tapePresample σ α` is
**not** a language-level transition: it is just the `Measure State`
obtained by "uniformly appending onto an existing tape `α`". Clients of
erasure construct it when invoking the `ARcoupl` wrappers below.
-/

/-- The uniform distribution on indices `{ z : Int // 0 ≤ z ∧ z < N }`.
If `N ≤ 0`, the subtype is empty and we return the zero measure; the
relevant erasure lemmas only apply to existing tapes, which always have a
positive bound. -/
noncomputable def tapeIndexUniform (N : Int) :
    Measure { z : Int // 0 ≤ z ∧ z < N } :=
  if h : (Finset.Ico 0 N).Nonempty then
    -- Map the uniform distribution on `Finset.Ico 0 N` into the subtype.
    (PMF.uniformOfFinset (Finset.Ico 0 N) h).toMeasure.map
      (fun z =>
        if hz : 0 ≤ z ∧ z < N then ⟨z, hz⟩
        else ⟨0, by
          -- Unreachable for `z` in the support, but we need a
          -- `{ z // 0 ≤ z ∧ z < N }` to make the function total. If
          -- `N ≤ 0` this branch is dead on the left already.
          rcases h with ⟨w, hw⟩
          simp [Finset.mem_Ico] at hw
          exact ⟨le_refl _, by omega⟩⟩)
  else 0

/-- The local "uniform presample on tape `α`" distribution on `State`.
Given an existing tape `α` of bound `N` with current content `bs`, this
returns the `State`-measure obtained by sampling `n ∈ [0, N)` uniformly
and appending `n` to the tape. This is the analogue of Clutch's
`state_step σ α`, localized to this file so as not to pollute the
language-level semantics. If the tape `α` is absent, we return `0`. -/
noncomputable def tapePresample (σ : State) (α : Loc) : Measure State :=
  match σ.tapes[α]? with
  | none => 0
  | some ⟨N, bs⟩ =>
      (tapeIndexUniform N).bind (fun n =>
        Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)))

/-! ## Core: presampling is invisible to `execN` -/

/-- **Main theorem (Clutch `prim_coupl_upd_tapes_dom`, reformulated).**
Appending a uniformly-sampled value onto an existing tape `α` of `σ` with
positive bound is invisible to `execN m ⟨e, σ⟩`: the result is the same as
running `execN m` directly from `σ`.

The positivity hypothesis `0 < N` is essential: the presample distribution
`tapePresample σ α` is the zero measure when the tape bound is nonpositive
(since the index subtype `{ z // 0 ≤ z ∧ z < N }` is empty), so without
positivity the LHS would collapse to `0` while the RHS may be nonzero.

Equivalently: `tapePresample σ α` is erasable at `σ` under these
conditions. -/
theorem exec_tape_presample_invariant
    {σ : State} {α : Loc} {e : Exp} {m : Nat} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    (tapePresample σ α).bind (fun σ' => execN m ⟨e, σ'⟩) = execN m ⟨e, σ⟩ := by
  sorry

/-- Corollary: `tapePresample σ α` is `Erasable` at `σ` when `α` is an
existing tape with positive bound. This is the packaging of
`exec_tape_presample_invariant` as an `Erasable` witness, suitable for
feeding into the `ARcoupl` wrappers below. -/
theorem tapePresample_erasable
    {σ : State} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    Erasable (tapePresample σ α) σ := by
  intro e m
  exact exec_tape_presample_invariant h hN

/-! ## Iterated and limit variants -/

/-- **Clutch `iterM_state_step_erasable`, reformulated.**
Iterating `tapePresample` on the same tape `n` times is still erasable.
(The tape persists through presampling, so we always pass the same `α`.) -/
theorem iterM_tapePresample_erasable
    {σ : State} {α : Loc} {t : Tape} (n : Nat)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    Erasable ((Nat.rec (motive := fun _ => Measure State)
                (Measure.dirac σ)
                (fun _ μ => μ.bind (fun σ' => tapePresample σ' α))) n) σ := by
  sorry

/-- **Clutch `limprim_coupl_step_limprim` / `lim_exec_eq_erasure`, reformulated.**
Binding `tapePresample σ α` into `limExec ⟨e, ·⟩` is equal to `limExec ⟨e, σ⟩`.
This is a direct consequence of `tapePresample_erasable` and
`Erasable.lim_exec`. -/
theorem limExec_tape_presample_invariant
    {σ : State} {α : Loc} {t : Tape} {e : Exp}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    (tapePresample σ α).bind (fun σ' => limExec ⟨e, σ'⟩) = limExec ⟨e, σ⟩ :=
  (tapePresample_erasable h hN).lim_exec e

/-! ## ARcoupl wrappers

These are the Approxis-facing lemmas. They take arbitrary erasable
distributions `μ₁ : Measure State` / `μ₂ : Measure State` and lift an
`AddCoupl` on those distributions to an `AddCoupl` on `execN`/`limExec`.

Clients of Approxis that would have instantiated Clutch's `ARcoupl_erasure`
with `state_step σ α` should instead construct `tapePresample` themselves
and feed it here via `tapePresample_erasable`.
-/

/-- **Clutch `ARcoupl_erasure_erasable`, core version.**
Given an additive coupling between arbitrary erasable distributions `μ₁`
and `μ₂`, and a coupling continuation on `exec n / lim_exec`, we can lift
to a coupling on `exec n ⟨e₁, σ₁⟩ / lim_exec ⟨e₁', σ₁'⟩`. The error
slacks add. -/
theorem AddCoupl_erasure_erasable
    {e₁ e₁' : Exp} {σ₁ σ₁' : State}
    {μ₁ μ₂ : Measure State} {R : Set (State × State)} {Φ : Set (Cfg × Cfg)}
    {ε ε₁ ε₂ : ENNReal} {n : Nat}
    (hSum : ε₁ + ε₂ ≤ ε)
    (hCoupl : AddCoupl ε₁ R μ₁ μ₂)
    (hErase₁ : Erasable μ₁ σ₁)
    (hErase₂ : Erasable μ₂ σ₁')
    (hCont : ∀ σ₂ σ₂', R (σ₂, σ₂') →
        AddCoupl ε₂ Φ (execN n ⟨e₁, σ₂⟩) (limExec ⟨e₁', σ₂'⟩)) :
    AddCoupl ε Φ (execN n ⟨e₁, σ₁⟩) (limExec ⟨e₁', σ₁'⟩) := by
  sorry

/-- **Clutch `ARcoupl_erasure_erasable_exp_rhs`, reformulated.**
RHS expected-value variant (advanced composition). Instead of a flat
additive slack on the continuation, we allow the continuation's slack to
depend on the RHS sample, and pay the expected value as additional slack
on the LHS. -/
theorem AddCoupl_erasure_erasable_exp_rhs
    {e₁ e₁' : Exp} {σ₁ σ₁' : State}
    {μ₁ μ₁' : Measure State} {R : Set (State × Cfg)} {Φ : Set (Cfg × Cfg)}
    {ε ε₁ : ENNReal} {E₂ : Cfg → ENNReal} {n m : Nat}
    (hCoupl : AddCoupl ε₁ R μ₁
        (μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)))
    (hBound : ε₁ + ∫⁻ ρ, E₂ ρ ∂(μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)) ≤ ε)
    (hErase₁ : Erasable μ₁ σ₁)
    (hErase₁' : Erasable μ₁' σ₁')
    (hCont : ∀ σ₂ ρ', R (σ₂, ρ') →
        AddCoupl (E₂ ρ') Φ (execN n ⟨e₁, σ₂⟩) (limExec ρ')) :
    AddCoupl ε Φ (execN n ⟨e₁, σ₁⟩) (limExec ⟨e₁', σ₁'⟩) := by
  sorry

/-- **Clutch `ARcoupl_erasure_erasable_exp_lhs`, reformulated.**
LHS expected-value variant. Symmetric to `AddCoupl_erasure_erasable_exp_rhs`:
the continuation's slack depends on the LHS sample, and its expected
value is paid as additional slack on the final coupling. -/
theorem AddCoupl_erasure_erasable_exp_lhs
    {e₁ e₁' : Exp} {σ₁ σ₁' : State}
    {μ₁' : Measure State} {R : Set (Cfg × State)} {Φ : Set (Cfg × Cfg)}
    {ε ε₁ : ENNReal} {E₂ : Cfg → ENNReal} {n : Nat}
    (hCoupl : AddCoupl ε₁ R (primStep ⟨e₁, σ₁⟩) μ₁')
    (hBound : ε₁ + ∫⁻ ρ, E₂ ρ ∂(primStep ⟨e₁, σ₁⟩) ≤ ε)
    (hErase₁' : Erasable μ₁' σ₁')
    (hCont : ∀ ρ σ₂', R (ρ, σ₂') →
        AddCoupl (E₂ ρ) Φ (execN n ρ) (limExec ⟨e₁', σ₂'⟩)) :
    AddCoupl ε Φ ((primStep ⟨e₁, σ₁⟩).bind (execN n)) (limExec ⟨e₁', σ₁'⟩) := by
  sorry

/-- **Clutch `ARcoupl_erasure_erasable_exp_lhs_kanto`, reformulated.**
Kantorovich-style LHS variant: the slack function `E₂` is a function of
pairs, not just the LHS sample. -/
theorem AddCoupl_erasure_erasable_exp_lhs_kanto
    {e₁ e₁' : Exp} {σ₁ σ₁' : State}
    {μ₁' : Measure State} {Φ : Set (Cfg × Cfg)}
    {ε : ENNReal} {E₂ : Cfg → Cfg → ENNReal} {n m : Nat}
    (hErase₁' : Erasable μ₁' σ₁')
    (hCont : ∀ ρ ρ',
        AddCoupl (E₂ ρ ρ') Φ (execN n ρ) (limExec ρ')) :
    AddCoupl ε Φ (execN n ⟨e₁, σ₁⟩) (limExec ⟨e₁', σ₁'⟩) := by
  sorry

end ProbLang
