# TotalEris Wishlist

Long-running port target: total Eris from `clutch/theories/eris/` (Rocq) to
Lean 4 under `Metrology/TotalEris/`. Goal: the chosen total-WP **examples**
look similar to the Rocq versions but use Lean/Iris-Lean proofmode tactics and
locally-nameless syntax.

Authoritative agreements from the kickoff:

| Question | Answer |
|---|---|
| Partial scope | Port anything *below* the Eris WP (glm, `pgl_wp`, `erisWpGS`); skip partial primitive_laws / proofmode unless total stack reuses them. |
| Adequacy | Full total adequacy (port `total_adequacy.v`). |
| Target examples | `geometric_total` (tutorial) + `random_walk` (examples). |
| Layout | Everything under `Metrology/TotalEris/`. |

## Success criteria

1. `lake build Metrology.TotalEris` is green; no `sorry` along the dependency
   chain from each example back through the total adequacy theorem.
2. `Metrology/TotalEris/Examples/GeometricTotal.lean` proves the canonical
   geometric-termination spec using `wp_*` / `twp_*` tactics. The text/structure
   is recognizably the same as `geometric_total.v` modulo Lean syntax and the
   locally-nameless representation.
3. `Metrology/TotalEris/Examples/RandomWalk.lean` likewise, using the RSM
   presampling rule.
4. Tactics (`wp_pures`, `wp_apply`, `wp_bind`, `wp_lam`, `wp_pure`,
   `wp_alloctape`, and `iLöb`) work on `tgl_wp` goals — the examples should not
   need to bypass them.

## Current porting status (2026-05-25 — significant infrastructure complete)

Files in `Metrology/TotalEris/` — **all build green, zero sorries**:

| File | Status | Notes |
|---|---|---|
| `Glm.lean` | ✅ | 2 of 3 disjuncts (state_step deferred); `Pgl`, `ErisWpGS` class, `execStutter`, `glm`, `glmPre_mono`, `glm_unfold`, `glm_mono_pred`, `glm_prim_step`, `glm_credit_bump`. |
| `Weakestpre.lean` | ✅ | `pglWpPre`, `pglWp`, `Contractive` instance, unfold + value rules. (Strong_mono, bind, fupd deferred.) |
| `TotalWeakestpre.lean` | ✅ | `tglWp` via `bi_least_fixpoint` over `(CoPset × Exp)` (Φ outer). Unfold + value rules + simple induction principle (`tglWp_ind_simple`, fixed `E`/`Φ`). Marked `@[reducible]` so `iexact`/`iapply` see through `tglWp = bi_least_fixpoint ...` defeq. Per-branch unfolds: `tglWp_unfold_value`, `tglWp_unfold_step`, `tglWpPre_eq_value`, `tglWpPre_eq_step`. Derived: `tglWp_mono`, `tglWp_strong_mono` (fixed-mask, **spatial** fupd wand via `glm_strong_mono` + Q-as-pre trick), `tglWp_wand`/`_l`, `tglWp_fupd`, `fupd_tglWp`, `tglWp_frame_l`/`_r` (spatial), `tglWp_bind`, `tglWp_bind_value`, `tglWp_value_inv_with_state` (extract value-WP post under state). (Mass-changing `tglWp_strong_mono` still deferred.) |
| `Glm.lean` | ✅ | `Pgl`, `ErisWpGS` class, `execStutter`, `glm` (OT + prim_step disjuncts), `glm_unfold`, `glm_strong_mono` (spatial wand via `least_fixpoint_iter` + Q-as-pre), `glm_mono_pred` (intuitionistic), `glm_mono_grading` (ε ≤ ε' weakening, single-step), `glm_prim_step`, `glm_credit_bump`, `glm_bind` (Ectx-bind, derived via `partialInv K.fill` + `primStep_fill` pushforward, no `Hv` precondition required). |
| `TotalLifting.lean` | ✅ | All 8 lifting lemmas proved: `twp_lift_step_fupd_glm`, `twp_lift_step_fupd`, `twp_lift_atomic_step_fupd`, `twp_lift_pure_step`, `twp_lift_pure_det_step`, `twp_lift_atomic_head_step`, `twp_lift_pure_det_head_step`, `twp_lift_pure_det_step_of_pureStep`. **Plus `twp_pure_step_fupd`** (PureExec integration). |
| `ErisGS.lean` | ✅ | `ErisGS` class bundling `AppGS` + `ECGS` + `InvGS_gen`; auto `ErisWpGS` instance. |
| `TotalPrimitiveLaws.lean` | ✅ | `twp_alloc`, `twp_load`, `twp_store`, `twp_alloctape`, `twp_rand`, `twp_rand_tape`, `twp_rand_tape_empty`. |
| `ErrorRules.lean` | ✅ | `ec_split`, `ec_combine`, `ec_eq`, `ec_contradict`, `ec_weaken`, `ec_zero`, `ec_valid`. |
| `Proofmode.lean` | ✅ | Macros `twp_value`, `twp_pure`, `twp_pures`, `twp_lam`, `twp_apply` + `wp_*` aliases. `twp_pure` uses `twp_pure_step_fupd`. |

Still to write (in priority order):

1. ~~`twp_rand_tape`, `twp_rand_tape_empty` in `TotalPrimitiveLaws.lean`.~~ ✅ done.
2. ~~`twp_bind` lemma + `twp_apply` improved macro that does bind+iapply.~~ ✅
   `glm_bind` and `tglWp_bind` both ported. `twp_bind <K>` macro added in
   `Proofmode.lean`. `twp_apply` macro still does plain `iapply` — combining
   bind+apply automatically requires syntactic Ectx inference from the goal
   shape, deferred.
2b. ~~`fupd_tglWp`.~~ ✅ done. The Lean-level term `tglWp_unfold_value` /
   `tglWp_unfold_step` (per-branch unfoldings of `tglWp_unfold` that pre-reduce
   the inner `match e.toVal?` at the Lean term level via `unfold` + `rw`
   *before* introducing the result as an Iris hypothesis) sidesteps the
   "no `rw at <iris-hyp>`" limitation entirely.

2c. ~~Spatial-wand `tglWp_strong_mono` and spatial `tglWp_frame_l`.~~ ✅
   done — `glm_strong_mono` ported using `least_fixpoint_iter` with a
   wand-carrying `Ψ`; spatial `tglWp_strong_mono` derived via the analogous
   Q-as-pre trick; `tglWp_wand` and `tglWp_frame_l` now spatial too.
3. Selective `twp_rand_exp_nat` / `twp_rand_exp_fin` from `error_rules.v` — needed by geometric_total.
3a. ~~**`ec_induction` / `ec_ind_simpl_external`**~~ ✅ already ported in
   `Metrology/Iris/ErrorCredits.lean` as `ErrorCredit.Induction.{external_simple, increasing, amplifying, amp_external}`. Re-exported under Rocq names `ec_ind_simpl_external` and `ec_induction` in `ErrorRules.lean`. Smoke test in `Examples/Basic.lean`.
4. Add state-step disjunct to `glm` (extend `Glm.lean`) — needed by `twp_presample_rsm`.
5. Selective `twp_presample_rsm` from `presample_rules.v` — needed by random_walk.
6. `TotalAdequacy.lean` — `twp_tgl`, `twp_mass_lim_exec`, `twp_pgl_lim_limit`.
7. Smoke-test example (`Examples/Basic.lean`).
8. `Examples/GeometricTotal.lean`, `Examples/RandomWalk.lean`.
9. Partial WP `Lifting.lean` (deferred — only needed if examples use partial WP).

## Module layout (under `Metrology/TotalEris/`)

Following the Approxis template (`Metrology/Approxis/*` already exists and is
the closest analog — copy its style for `WpGS` class, ghost state setup,
`bi_least_fixpoint`-based modalities, and the proofmode tactic macros).

Bottom-up dependency order (also the porting order):

```
                            ┌── Glm.lean              ← glm modality (least fp)
Metrology/TotalEris/        ├── Weakestpre.lean       ← erisWpGS class + pgl_wp def + core lemmas
                            ├── Lifting.lean          ← wp_lift_* glue
                            ├── EctxLifting.lean
                            ├── PrimitiveLaws.lean    ← state_interp setup + wp_alloc/load/store/rand
                            ├── DerivedLaws.lean      ← array laws (only if examples need)
                            ├── TotalWeakestpre.lean  ← tgl_wp def + ind + unfold + monotonicity
                            ├── TotalLifting.lean
                            ├── TotalEctxLifting.lean
                            ├── TotalPrimitiveLaws.lean
                            ├── TotalDerivedLaws.lean (only if needed)
                            ├── ErrorRules.lean       ← selective port (see below)
                            ├── PresampleRules.lean   ← selective port (see below)
                            ├── Proofmode.lean        ← wp_pures / wp_apply / wp_bind / wp_lam / wp_alloctape macros
                            ├── Adequacy.lean        (optional — only if total_adequacy reuses)
                            ├── TotalAdequacy.lean    ← twp_tgl, twp_mass_lim_exec, twp_pgl_lim_limit
                            └── Examples/
                                ├── GeometricTotal.lean
                                └── RandomWalk.lean
```

Top-level index `Metrology/TotalEris.lean` re-exports the public surface.

## Selective porting in the heavy files

`error_rules.v` (1727 lines) and `presample_rules.v` (2322 lines) are too big
to port wholesale. Port only what the chosen examples actually use, plus any
prerequisites that come up.

| File | Must-port lemmas | Reason |
|---|---|---|
| `error_rules.v` | `twp_err_pos`, `twp_rand_exp_nat`, `twp_rand_exp_fin`, `ec_aux`, `ec_split`/`ec_combine`/`ec_eq`/`ec_induction`/`ec_contradict` | geometric_total + ec utility |
| `presample_rules.v` | `twp_presample_rsm` and its supporting RSM machinery | random_walk |
| `seq_amplification.v` | only if `twp_rand_exp_*` proofs need it | check during porting |

If a tempting auxiliary lemma turns out to be a dead end or pulls in another
1000-line chase, leave the dependency as `sorry` and move on. **Do not port
partial-WP `wp_apply` chains in `proofmode.v`** unless the total proofmode
literally needs them.

## Tactics (`Proofmode.lean`)

Build proofmode-style macros directly on top of the lifting lemmas
(`twp_lift_pure_step`, `tgl_wp_bind`, `tgl_wp_value`, etc.). Use Approxis's
`RelTactics.lean` as the structural template:

- `wp_pure` / `wp_pures` — single/repeat pure reductions
- `wp_lam` / `wp_rec` — beta-step on lambdas/recursive functions
- `wp_bind` — focus a redex
- `wp_apply <term>` — `wp_bind` + `iapply`
- `wp_alloc` / `wp_load` / `wp_store` / `wp_rand` / `wp_alloctape` — heap/tape
- These should be generic over `wp` vs `twp` if practical. If not, prefix
  total versions with `twp_*`; either is acceptable as long as the example text
  stays readable.

## Locally-nameless caveat

`Metrology/ProbLang/Syntax/Syntax.lean` uses `fvar`/`bvar` and `Exp`. When
porting code that pattern-matches or unfolds programs, write Lean expressions
in the existing notation (see `Metrology/ProbLang/Test/Notation.lean`). Where
the Rocq proof uses `wp_lam`/`wp_rec`, the Lean tactic should produce the
corresponding substitution under locally-nameless conventions — likely via the
already-existing `open_*`/`subst_*` lemmas in `Syntax/LocallyClosed.lean`.

## Stretch goals (only after the above is green)

- Port `basic_eris.v` tutorial (mostly partial-WP; would force more partial
  primitive laws — skip unless time permits).
- Port `rec_toss.v` / `spline.v` examples.
- Tighten any `sorry`s left in `presample_rules` / `error_rules` ports.

## Things to actively avoid

- Wholesale porting of `error_rules.v` and `presample_rules.v`.
- Porting partial-WP `derived_laws` / `proofmode` if the total stack does not
  reuse them.
- Adding new abstractions or "improvements" over the Rocq structure — the goal
  is a faithful port that survives future maintenance, not a redesign.
- Per `CLAUDE.md`: never delete commented-out Rocq blocks; keep the file
  compiling after each edit; ask for help if stuck instead of spinning.
