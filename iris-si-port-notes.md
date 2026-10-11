# Porting Metrology `ora-test` to the step-index sugar PR

Branch `si-sugar` (off `ora-test` at 6ac8b37). Iris target: local `/home/agent/iris-lean/Iris`
at `b94a105` (si-module-sugar2).

## Starting point

- `ora-test` pins Iris `740e2c4` (master, #700). That is the *base* of the ORA PR (#688), not #688
  itself: #688 is 52 commits past it, and our branch is 62 past it (688 ⊂ ours).
- `ora-test` uses no ORA-specific API (`grep ORA|OrdExtend|SIdx|StepIndex` finds nothing).
- Toolchains: Metrology v4.34.0 (Mathlib/cslib v4.34.0 caches); Iris ≥ #702 is on v4.34.1.
  Plan: keep Metrology on v4.34.0, so Mathlib stays cached, and build Iris with it.
- 155 Lean files, 149 in module style; 22 import Iris directly.

## Plan

1. Baseline: build `ora-test` as-is.
2. Stage A: point at #688 (worktree `~/iris-ora`, detached at `pr-688`), fix the build. This is the cost of
   the ORA PR alone.
3. Stage B: point at the local PR (`b94a105`), fix the build. This is the cost of generalised step
   indices plus the sugar.

## Log

### Baseline (`ora-test`, Iris 740e2c4)

Builds cleanly. `lake build` from a `main` build state took 12m21s wall (incremental, so not a clean
number). The slowest modules: `Approxis.Examples.Switching` 412 s, `SwitchingPRP` 134 s,
`ProbLang.HeadStep` 46 s, `ProbLang.Measure` 42 s.

### Stage A: ORA PR #688 (`pr-688` = 162950a)

`lakefile.toml`: `iris` → `path = "../iris-ora/Iris"`, then `lake update iris`. This updates only the
iris manifest entry; Mathlib's cache is untouched.

Iris itself builds under Metrology's v4.34.0 with no trouble. The v4.34.1 bump (#702) isn't needed.

Errors: **2 files, 9 errors**, all fixed by hand in a few minutes.

1. `Metrology/Iris/Algebra.lean`: the `Measure α` CMRA and UCMRA instances. #688 splits `CMRA` into
   `ORA` + `IsInc`, so a classical CMRA written with `where` now lacks all the order fields
   (`OrderN`, `ordN_ne`, …, `ordN_incN`). The fix is mechanical:
   - `CMRA … where {fields}` → `CMRA … := ORA.ofCMRAData { fields }`, same fields unchanged;
   - `UCMRA … where …` → `UORA.ofUCMRAData { … }`;
   - `simp [CMRA.Valid]` → `simp [Valid.Valid]`, and `simp [CMRA.pcore]` → `simp [ORA.pcore]`. The
     projections moved to the `Valid` and `PCore`/`ORA` classes.
2. `Metrology/Iris/StepFupd.lean:63`: `simp only [Nat.repeat]` made no progress. `step_fupdN` is now
   its own recursive def (from the Iris-Rocq bump #706, which came in with #688's master merge), not
   `Nat.repeat`. → `simp only [step_fupdN]`.
   Not an ORA change: master drift.
3. `Metrology/Iris/ErrorCredits.lean`, `Metrology/LiveEris/Credits.lean`: the same CMRA → `ORA.ofCMRAData`
   wrap for `ErrorCredit` and `CreditBelow b`, plus renames. The projections moved out of `CMRA`
   (sed-able):
   - `CMRA.op` → `Op.op`, `CMRA.op?` → `Op.op?`;
   - `CMRA.Valid(N)` → `Valid.Valid(N)`;
   - `CMRA.pcore` / `CMRA.core` → `PCore.pcore` / `PCore.core`;
   - `CMRA.Cancelable` → `ORA.Cancelable`.

   `CMRA.Discrete` → `ORA.Discrete`, which gains a field: `discrete_ord := CMRA.ord_of_ord0`.

   **Unit gotcha:** #688 has two unit projections, `UCMRA.unit` (UCMRA's own field) and `UORA.unit`.
   Iris lemmas (`IsUnit` instance, `auth_update_dealloc`, …) state things with `UORA.unit`, while
   Metrology's simp lemmas and `simp only [UCMRA.unit]` use `UCMRA.unit`. They agree by `rfl`, but
   simp and instance search treat them as different terms. Fixes:
   - the `IsUnit` `inferInstanceAs` uses `UORA.unit`;
   - add a twin simp lemma `uora_unit_val`;
   - `simp only [UORA.unit, UCMRA.unit]`.

   This is a wart in #688 itself, worth flagging upstream.
4. `BundledGFunctors` tables: #688 makes `GFunctor`'s instance field instance-implicit, so
   `⟨F, by infer_instance⟩` → `⟨F⟩`. 26 entries in 3 files (sed).
5. `simp only [Nat.repeat]` → `simp only [step_fupdN]` (8 sites in 4 files, sed).
   This is the same master drift as item 2.

Stage A builds green (9m58s wall, incremental). Remaining warnings: one pre-existing `sorry` in
`TotalEris/Examples/RandomWalk.lean`.
**Stage A total: 11 files, +69/−65.** About 85% is sed-able; the hand work is 4 instance blocks (wrap in
`ofCMRAData` / `ofUCMRAData`) and the unit twin lemma. Patch:
`scratchpad/metro/stageA.patch`.

### Stage B: this PR (local `iris-lean` at b94a105, si-module-sugar2)

`lakefile.toml`: `iris` → `path = "../iris-lean/Iris"`, then `lake update iris`.
Side effect: the Iris oleans in `iris-lean/Iris/.lake/build` are now built by Metrology's v4.34.0, so
the next standalone Iris build (v4.34.1) rebuilds them.

Iris at b94a105 builds under Metrology's v4.34.0 too.

**B0. `local stepindex Nat`.** First build: every Iris-using file fails with `SIdx PROP`,
`SIdx (Measure α)`, … (no step index in scope). As designed: added `local stepindex Nat` right
after `@[expose] public section` in all 82 files that import Iris directly or not. In the 3 tactic
files without a public section it goes after the `namespace` line. Mechanical (script). Pruning to
the files that need it comes after the build is green.

**B1. `Metrology/Iris/Fixpoint.lean`.** `[BI PROP]` → `[BI PROP] [BIStepIndexed PROP]`. BI is SI-free
now; `≡{n}≡` on `PROP` comes from the `BIStepIndexed` mixin. Error: `HasDist Nat PROP` /
`BIStepIndexed PROP` not found. One binder.

**B2. `Metrology/Iris/StepFupd.lean`.** `[Sbi PROP] [BIFUpdate PROP] [BIFUpdateSbi PROP]` →
`[BI PROP] [BIPlainly PROP] [BIFUpdate PROP] [BIFUpdatePlainly PROP]`. `Sbi` no longer extends `BI`,
and `Plain`/`fupd_plain_forall` now want the SI-free `BIPlainly` + `BIFUpdatePlainly` (Iris ≤ 4.2
style). These lemmas end up SI-free. Took some reading of `BI/Plainly.lean`'s doc to find the right
binders: error text `Plainly PROP` alone doesn't say "use BIPlainly".

**B3. `Metrology/Iris/Algebra.lean`, the `Measure α` instances: the biggest per-instance cost.**
- `OFE`: field `Dist` → `dist` (now the `HasDist` field; `OFE.Dist` is an abbrev).
- `CMRA` splits in two:
  - `instance : RA X where pcore op assoc comm pcore_op_left pcore_idem` (SI-free);
  - `CMRA X := ORA.ofCMRAData { Valid ValidN op_ne pcore_ne validN_ne valid_iff_validN validN_le
    validN_op_left pcore_op_mono extend }`.
- `validN_succ` → `validN_le` (`ValidN n x → n' ≤ n → ValidN n' x`): constant validity is
  `validN_le H _ := H`.
- `UCMRA` splits in two:
  - `instance : URA X where unit unit_left_id pcore_unit total` (`URA` extends `IsTotal`, so a
    `total` proof is new);
  - `UCMRA X := UORA.ofUCMRAData { unit_valid }`.
- Proof breakage: `pcore_ne := by simp` stopped working, since `pcore` is now another instance's
  projection and simp doesn't unfold it. Written out: `rintro ⟨rfl⟩; exact ⟨0, rfl, rfl⟩`.
- **Oddity:** `unit_valid := by simp [Valid.Valid, UnitOp.unit]` elaborates but the *kernel*
  rejects it: `declaration type mismatch … _proof_1 has type 0 ≤ 1 but is expected to have type
  ✓ unit`. `show (0 : Measure α) .univ ≤ 1 by simp` works. Likely the auxiliary-proof abstraction
  meeting the `{SI}` binder on `UCMRAData.unit_valid`; worth a minimal repro in Iris.

**B4. `Iris/ErrorCredits.lean`, `LiveEris/Credits.lean`: the same RA/CMRA and URA/UCMRA split** for
`ErrorCredit` and `CreditBelow b`.
- About 40 errors per file, but only the instance block was wrong; the rest cascaded.
- `simp` proofs of RA laws that used to unfold the structure projection now need explicit terms:
  - `pcore_idem := by rintro ⟨rfl⟩; rfl`;
  - `pcore_op_left … exact zero_add _`;
  - `pcore_op_mono … (zero_add 0).symm ▸ rfl`.
- New `total` field on `URA`.
- `URA (CreditBelow b)` no longer needs `[NeZero b]`; only `UCMRA` does (for `unit_valid`).
- The stage-A `UORA.unit`/`UCMRA.unit` patches stay; they still compile.
  - *Correction:* the RA-law `simp` proofs (`pcore_idem := by simp`, `pcore_op_left … simp`) keep
    working inside `RA … where`, since `pcore` there is the structure's own field. What broke were
    the proofs inside `ORA.ofCMRAData { … }` that mention `pcore`/`•`, which are now *another*
    instance's projections. `pcore_op_mono` → `⟨0, congrArg some (zero_add 0).symm⟩`.
- `URA.unit_left_id` is stated `∀ {x}`: needs `intro _`.
- **Unit: the stage-A wart is gone.** There is one unit, `UnitOp.unit` (exported as `unit`).
  `UCMRA.unit`/`UORA.unit` → `UnitOp.unit` (sed), and the `uora_unit_val` twin lemma is dropped
  again.
- **`IsUnit` splits.** `IsRAUnit ε` (SI-free: `unit_left_id`, `pcore_unit`) is now a separate
  instance that `IsUnit ε` (`unit_valid`) takes as a parameter. Each hand-written `IsUnit`
  instance becomes two.
- **Distance unfolding.** `simp only [OFE.Dist, …]` now stops at `HasDist.dist n x y`. Add
  `HasDist.dist` to the simp set (3 sites).
- **Step-index binders (a sugar gap).** `theorem includedN_iff {n} … : x ≼{n} y ↔ …` and
  auto-bound `n` no longer work. `✓{n} x` is `Valid.ValidN n x`, and with `n : ?` the instance
  `Valid ?SI X` is stuck: SI is not an outParam, by design. Fix: `{n : Nat}`.
  - Library-side fix to consider: mark `Valid.ValidN`, `OFE.Dist`, `IncludedN`, … `@[indexed]`
    (or have the `✓{n}`/`≡{n}≡`/`≼{n}` notations ascribe `(n : stepindex%)`). Then
    `local stepindex Nat` alone covers untyped binders.
  - About 42 untyped `{n}` binders exist in Metrology; only those whose SI isn't fixed elsewhere
    break.

**B5. Glm (TotalEris, LiveEris), AppWeakestpre.**
- **SI pins on unmarked lemmas: the main remaining client cost.**
  `iapply (least_fixpoint_iter (F := glmPre' Z₁))` fails with the opaque
  `istart: NonExpansive ?m Ψ is not an emp valid`, plus a stray goal `⊢ Type ?u` (the SI itself).
  - Cause: `least_fixpoint_iter`'s `{SI}` appears only in instance arguments
    (`[BIStepIndexed SI PROP]`, `[NonExpansive SI Φ]`). `PROP := IProp GF` does not mention SI, and
    SI is not an outParam, so nothing determines it. The lemma isn't `@[indexed]`, so
    `local stepindex Nat` doesn't reach it.
  - Fix: `least_fixpoint_iter (SI := Nat) (F := …)`. 4 sites in Glm.
  - Library-side alternative: `@[indexed]` on `least_fixpoint_iter`. The rule of thumb "mark lemmas
    only when needed" applies: a lemma whose SI is fixed by no explicit argument *is* needed.
  - The error message is the worst part of the port. It names neither SI nor the lemma.
- `BIFUpdate.ne.ne` → `FUpdNE.fupd_ne.ne`: the NE law moved to the `FUpdNE` mixin (sed, 3 sites).
- `OFE.Discrete.discrete_0 hd` with `hd : x ≡{n}≡ y` → `OFE.Discrete.discrete hd`. The old
  `discrete_0` was stated for any `n`; it now really is `≡{0}≡`.

**B6. More `least_fixpoint_iter` pins** (`TotalEris/TotalWeakestpre`, `LiveEris/Weakestpre`): 2 more
sites. 6 of the 7 `least_fixpoint_iter` calls need the pin. The exception is
`AppWeakestpre:167`, `ihave … := least_fixpoint_iter (Φ := Φ) $$ …`; there unification against the
context fixes SI.

**B7. `Approxis/Model.lean`: hand-written `OFE`/`IsCOFE` for `lrel`.**
- `Dist` → `dist`.
- `IsCOFE` gains the limit-chain fields of generalised step indices: `lbcompl`, `conv_lbcompl`,
  `lbcompl_ne`. For `Nat` there are no limit indices, so `lbcompl := (·.elim)` etc. (3 boilerplate
  lines, the same idiom as Iris's own `Vector`/`List` instances).
- Library-side alternative: a Nat-only builder (`IsCOFE.ofNat compl conv_compl`) would hide the
  transfinite fields from Nat clients entirely. Not present today.

### Pruning `local stepindex Nat`

For each of the 82 files, compiled a copy without the line: **60 compile unchanged, 22 need it.**
Removed it from the 60. A full rebuild is green (`Build completed successfully`, 10m15s; the only
warning is the pre-existing `sorry`).

### Stage B totals

- 22 files with `local stepindex Nat` (1 line each).
- 11 files with real edits: about 150 +/− lines. 111 of them are the 3 hand-written CMRAs (`Measure`,
  `ErrorCredit`, `CreditBelow`).
- Patch: `scratchpad/metro/stageB-only.patch`; the cumulative patch is `git diff` on `si-sugar`.

### Build time (rough: single runs, uneven machine load)

Sum of per-module times over the 52 modules rebuilt in all of baseline, A and B:
- master 528 s;
- #688 587 s (+11%; suspect, since some A/B runs overlapped Iris compiling);
- this PR 574 s (−2% vs #688, i.e. noise).

The biggest module `Approxis.Examples.Switching`: 412 s (master) vs 417 s (this PR).
`SwitchingPRP`: 134 / 133 / 137 s. Program runtime: unaffected (Iris is proof-only).
