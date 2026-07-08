module

public import Metrology.TotalEris.Examples.Samplers.BernoulliGeometric
public import Metrology.TotalEris.Examples.Samplers.RealDecrTrial
public import Metrology.TotalEris.Examples.Samplers.HalfBernNegExp
public import Metrology.TotalEris.Examples.Samplers.BernIter
public import Metrology.TotalEris.Examples.Samplers.NegExp
public import Metrology.TotalEris.Examples.Samplers.Selector
public import Metrology.TotalEris.Examples.Samplers.Gauss
public import Metrology.TotalEris.Examples.Samplers.Laplace

@[expose] public section

/-!
# Gaussian / Laplace samplers — scaffolding (continuous-uniform port)

Aggregator for the `urand`-based port of the Gauss/Laplace sampler stack from
`clutch/theories/eris/examples/{gauss,laplace}.v` (branch `elementary-infinite`).

Dependency layering (bottom-up):

```
RealDecrTrial ── decreasing trial (init→urand, cmp→real <, presample→twp_urand_exp)
  ├── HalfBernNegExp (LeHalf, BNEHalf)        ── concrete base-½ Bernoulli
  └── NegExp                                   ── Laplace magnitude sampler
BernoulliGeometric (GeometricTrial) / BernIter (IterTrial)  ── generic combinators over AbstractBernoulli
Selector (C, Bii, S, S0, B)                    ── integer-part selection
Gauss   (G1, G2)   ← BNEHalf, GeometricTrial, IterTrial, B
Laplace (Laplace0, Laplace) ← NegExp
```

**Status: stub.** Every file contains programs + specifications only; all
proofs are `sorry`. Fixed at `rT = ℝ`.

Two language extensions are deferred to the proof phase (flagged in-file):
* real comparison `<`/`≤` in `BinOp.eval` (needed by every sampler), and
* a real power-of-two op for `Laplace`'s `R_mulPow`.

Deliberately **not** imported by `Examples.lean`, so these stubs stay out of
the default build target until the proofs land.
-/
