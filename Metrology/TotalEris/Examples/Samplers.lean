module

public import Metrology.TotalEris.Examples.Samplers.BernoulliGeometric
public import Metrology.TotalEris.Examples.Samplers.RealDecrTrial
public import Metrology.TotalEris.Examples.Samplers.HalfBernNegExp
public import Metrology.TotalEris.Examples.Samplers.BernIter
public import Metrology.TotalEris.Examples.Samplers.NegExp
public import Metrology.TotalEris.Examples.Samplers.Selector
public import Metrology.TotalEris.Examples.Samplers.Gauss

@[expose] public section

/-!
# Gaussian / Laplace samplers — scaffolding (continuous-uniform port)

Aggregator for the `urand`-based port of the Gauss sampler stack from
`clutch/theories/eris/examples/gauss.v` (branch `elementary-infinite`).

Dependency layering (bottom-up):

```
RealDecrTrial ── decreasing trial (init→urand, cmp→real <, presample→twp_urand_exp)
  ├── HalfBernNegExp (LeHalf, BNEHalf)        ── concrete base-½ Bernoulli
  └── NegExp                                   ── negative-exponential sampler
BernoulliGeometric (GeometricTrial) / BernIter (IterTrial)  ── generic combinators over AbstractBernoulli
Selector (C, Bii, S, S0, B)                    ── integer-part selection
Gauss   (G1, G2)   ← BNEHalf, GeometricTrial, IterTrial, B
```

**Status:** every WP spec is Iris-complete; remaining `sorry`s are the deferred
MATH side-conditions (PMF/lintegral/measurability/ENNReal-arithmetic). Fixed at
`rT = ℝ`.

(Laplace was dropped: its value-reconstruction/scaling need real-arithmetic and
real-power-of-two `BinOp.eval` extensions not yet in the language.)
-/
