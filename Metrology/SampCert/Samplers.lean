import Metrology.SampCert.SLang

/-
noncomputable section

open EmbedSLang ProbLang

/-! ## probUntil combinator -/

-- def probUntil (body : SLang T) (cond : T → Bool) : SLang T := do
--   let v ← body
--   probWhile (λ v : T => ¬ cond v) (λ _ : T => body) v
def plProbUntil (f x dummy : String) (bodyE condE : Exp) : Exp :=
  probLangBind (.named x) bodyE
    (probLangWhile f x dummy
      (probLangNot (probLangApp condE (Exp.var x)))  -- ¬ cond v
      (probLangLam dummy bodyE)                       -- fun _ => body
      (Exp.var x))                                    -- init = v

/-! ## UniformSample -/

-- def UniformSample (n : PNat) : SLang Nat := do
--   let r ← probUntil (UniformPowerOfTwoSample (2 * n)) (λ x : Nat => x < n)
--   return r
-- Uniform over {0, ..., n-1} via rejection sampling from rand (n-1).
-- rand (n-1) gives uniform over {0, ..., n-1} directly when n is a power of two.
-- For general n, we use probUntil with rand on a sufficiently large range.
def plUniformSample (n : ℕ) : Exp :=
  plProbUntil "f" "r" "r'"
    (.rand (probLangInt (n - 1)) probLangUnit)  -- rand(n-1, ()) samples {0,...,n-1}
    (probLangLam "x" (probLangLt (Exp.var "x") (probLangInt n)))

/-! ## BernoulliSample -/

-- def BernoulliSample (num : Nat) (den : PNat) (_ : num ≤ den) : SLang Bool := do
--   let d ← UniformSample den
--   return d < num
def plBernoulliSample (num den : ℕ) : Exp :=
  probLangBind (.named "d") (plUniformSample den)
    (probLangLt (Exp.var "d") (probLangInt num))

/-! ## Geometric sampler -/

-- variable (trial : SLang Bool)
-- def geoLoopCond (st : Bool × ℕ) : Bool := st.1
-- def geoLoopBody (st : Bool × ℕ) : SLang (Bool × ℕ):= do
--   let x ← trial
--   return (x,st.2 + 1)
-- def probGeometric : SLang ℕ := do
--   let st ← probWhile geoLoopCond (geoLoopBody trial) (true,0)
--   return st.2
def plGeoLoopBody (trialE : Exp) : Exp :=
  probLangLam "st"
    (probLangBind (.named "x") trialE
      (probLangPair (Exp.var "x")
        (probLangAdd (probLangSnd (Exp.var "st")) (probLangInt 1))))

def plProbGeometric (trialE : Exp) : Exp :=
  probLangBind (.named "st")
    (probLangWhile "f" "st" "x"
      (probLangFst (Exp.var "st"))
      (plGeoLoopBody trialE)
      (probLangPair (probLangBool true) (probLangInt 0)))
    (probLangSnd (Exp.var "st"))

/-! ## BernoulliExpNeg -/

-- def BernoulliExpNegSampleUnitLoop (num : Nat) (den : PNat) (wf : num ≤ den)
--     (state : (Bool × PNat)) : SLang (Bool × PNat) := do
--   let A ← BernoulliSample num (state.2 * den) (halve_wf num den state.2 wf)
--   return (A, state.2 + 1)
-- Note: BernoulliSample depends on state.2 * den as denominator.
-- Since the denominator is dynamic (depends on state), we inline the
-- uniform sampler using rand.
def plBernoulliExpNegUnitLoop (num den : ℕ) : Exp :=
  probLangLam "state"
    (let dynDen := probLangMul (probLangSnd (Exp.var "state")) (probLangInt den)
     probLangBind (.named "d")
      (.rand (probLangSub dynDen (probLangInt 1)) probLangUnit)  -- rand(dynDen-1, ())
      (probLangBind (.named "a")
        (probLangCond (probLangLt (Exp.var "d") (probLangInt num))
          (probLangBool true) (probLangBool false))
        (probLangPair (Exp.var "a")
          (probLangAdd (probLangSnd (Exp.var "state")) (probLangInt 1)))))

-- def BernoulliExpNegSampleUnitAux (num : Nat) (den : PNat) (wf : num ≤ den) : SLang Nat := do
--   let r ← probWhile (λ state : Bool × PNat => state.1)
--     (BernoulliExpNegSampleUnitLoop num den wf) (true,1)
--   return r.2
def plBernoulliExpNegUnitAux (num den : ℕ) : Exp :=
  probLangBind (.named "r")
    (probLangWhile "f" "state" "s'"
      (probLangFst (Exp.var "state"))
      (plBernoulliExpNegUnitLoop num den)
      (probLangPair (probLangBool true) (probLangInt 1)))
    (probLangSnd (Exp.var "r"))

-- def BernoulliExpNegSampleUnit (num : Nat) (den : PNat) (wf : num ≤ den) : SLang Bool := do
--   let K ← BernoulliExpNegSampleUnitAux num den wf
--   if K % 2 = 0 then return true else return false
def plBernoulliExpNegUnit (num den : ℕ) : Exp :=
  probLangBind (.named "k")
    (plBernoulliExpNegUnitAux num den)
    (probLangCond
      (probLangEq (probLangMod (Exp.var "k") (probLangInt 2)) (probLangInt 0))
      (probLangBool true)
      (probLangBool false))

-- def BernoulliExpNegSampleGenLoop (iter : Nat) : SLang Bool := do
--   if iter = 0 then return true
--   else
--     let B ← BernoulliExpNegSampleUnit 1 1 (le_refl 1)
--     if ¬ B then return B else
--       let R ← BernoulliExpNegSampleGenLoop (iter - 1)
--       return R
-- Encoding: while loop with state = (result : Bool, remaining : Int)
-- while remaining > 0 && result:  result ← unit(1,1);  remaining -= 1
def plBernoulliExpNegGenLoop (iter : ℕ) : Exp :=
  probLangBind (.named "st")
    (probLangWhile "f" "st" "st'"
      (probLangAnd
        (probLangFst (Exp.var "st"))
        (probLangNot (probLangEq (probLangSnd (Exp.var "st")) (probLangInt 0))))
      (probLangLam "st"
        (probLangBind (.named "b") (plBernoulliExpNegUnit 1 1)
          (probLangPair (Exp.var "b")
            (probLangSub (probLangSnd (Exp.var "st")) (probLangInt 1)))))
      (probLangPair (probLangBool true) (probLangInt iter)))
    (probLangFst (Exp.var "st"))

-- def BernoulliExpNegSample (num : Nat) (den : PNat) : SLang Bool := ...
-- Complex: branches on num ≤ den statically. For now, only handle the num ≤ den case.
-- def BernoulliExpNegSample (num : Nat) (den : PNat) : SLang Bool := do
--   if h : num ≤ den
--   then let X ← BernoulliExpNegSampleUnit num den h
--        return X
--   else
--     let gamf := num / den
--     let B ← BernoulliExpNegSampleGenLoop (gamf)
--     if B
--     then
--       let X ← BernoulliExpNegSampleUnit (num % den) den (rat_less_floor_le1 num den)
--       return X
--     else return false
-- Full version: uses dynamic branching on num ≤ den
def plBernoulliExpNegSample (num den : ℕ) : Exp :=
  probLangCond (probLangNot (probLangLt (probLangInt den) (probLangInt num)))  -- num ≤ den
    (plBernoulliExpNegUnit num den)
    (probLangBind (.named "b") (plBernoulliExpNegGenLoop (num / den))
      (probLangCond (Exp.var "b")
        (plBernoulliExpNegUnit (num % den) den)
        (probLangBool false)))

-- def DiscreteLaplaceGenSample (num : PNat) (den : PNat) (μ : ℤ) : SLang ℤ := do
--   let s ← DiscreteLaplaceSample num den
--   return s + μ
def plDiscreteLaplaceGenSample (laplaceSamplerE : Exp) (μ : Int) : Exp :=
  probLangBind (.named "s") laplaceSamplerE
    (probLangAdd (Exp.var "s") (probLangInt μ))

/-! ## Laplace sampler -/

-- def DiscreteLaplaceSampleLoopIn1Aux (t : PNat) : SLang (Nat × Bool) := do
--   let U ← UniformSample t
--   let D ← BernoulliExpNegSample U t
--   return (U,D)
-- Note: BernoulliExpNegSample takes dynamic (U, t). Since U is runtime,
-- we pass it via a lambda. bernExpNegE is a function: numerator → Bool sampler.
def plLaplaceSampleLoopIn1Aux (t : ℕ) (bernExpNegE : Exp) : Exp :=
  probLangBind (.named "u") (plUniformSample t)
    (probLangBind (.named "d") (probLangApp bernExpNegE (Exp.var "u"))
      (probLangPair (Exp.var "u") (Exp.var "d")))

-- def DiscreteLaplaceSampleLoopIn1 (t : PNat) : SLang Nat := do
--   let r1 ← probUntil (DiscreteLaplaceSampleLoopIn1Aux t) (λ x : Nat × Bool => x.2)
--   return r1.1
def plLaplaceSampleLoopIn1 (t : ℕ) (bernExpNegE : Exp) : Exp :=
  probLangBind (.named "r1")
    (plProbUntil "f" "x" "x'"
      (plLaplaceSampleLoopIn1Aux t bernExpNegE)
      (probLangLam "x" (probLangSnd (Exp.var "x"))))
    (probLangFst (Exp.var "r1"))

-- def DiscreteLaplaceSampleLoopIn2Aux (num : Nat) (den : PNat)
--     (K : Bool × Nat) : SLang (Bool × Nat) := do
--   let A ← BernoulliExpNegSample num den
--   return (A, K.2 + 1)
def plLaplaceSampleLoopIn2Aux (num den : ℕ) : Exp :=
  probLangLam "k"
    (probLangBind (.named "a") (plBernoulliExpNegSample num den)
      (probLangPair (Exp.var "a")
        (probLangAdd (probLangSnd (Exp.var "k")) (probLangInt 1))))

-- def DiscreteLaplaceSampleLoopIn2 (num : Nat) (den : PNat) : SLang Nat := do
--   let r2 ← probWhile (λ K : Bool × Nat => K.1)
--     (DiscreteLaplaceSampleLoopIn2Aux num den) (true,0)
--   return r2.2
def plLaplaceSampleLoopIn2 (num den : ℕ) : Exp :=
  probLangBind (.named "r2")
    (probLangWhile "f" "k" "k'"
      (probLangFst (Exp.var "k"))
      (plLaplaceSampleLoopIn2Aux num den)
      (probLangPair (probLangBool true) (probLangInt 0)))
    (probLangSnd (Exp.var "r2"))

-- def DiscreteLaplaceSampleLoop (num : PNat) (den : PNat) : SLang (Bool × Nat) := do
--   let v ← DiscreteLaplaceSampleLoopIn2 den num
--   let V := v - 1
--   let B ← BernoulliSample 1 2 (Nat.le.step Nat.le.refl)
--   return (B,V)
def plLaplaceSampleLoop (num den : ℕ) : Exp :=
  probLangBind (.named "v") (plLaplaceSampleLoopIn2 den num)
    (probLangBind (.named "b") (plBernoulliSample 1 2)
      (probLangPair (Exp.var "b")
        (probLangSub (Exp.var "v") (probLangInt 1))))

-- def DiscreteLaplaceSample (num den : PNat) : SLang ℤ := do
--   let r ← probUntil (DiscreteLaplaceSampleLoop num den)
--     (λ x : Bool × Nat => ¬ (x.1 ∧ x.2 = 0))
--   let Z : Int := if r.1 then - r.2 else r.2
--   return Z
def plDiscreteLaplaceSample (num den : ℕ) : Exp :=
  probLangBind (.named "r")
    (plProbUntil "f" "x" "x'"
      (plLaplaceSampleLoop num den)
      (probLangLam "x"
        (probLangNot
          (probLangAnd
            (probLangFst (Exp.var "x"))
            (probLangEq (probLangSnd (Exp.var "x")) (probLangInt 0))))))
    (probLangCond (probLangFst (Exp.var "r"))
      (probLangNegInt (probLangSnd (Exp.var "r")))
      (probLangSnd (Exp.var "r")))

/-! ## Gaussian sampler -/

-- def DiscreteGaussianSampleLoop (num den t : PNat) (mix : ℕ) : SLang (Int × Bool) := do
--   let Y : Int ← DiscreteLaplaceSampleMixed t 1 mix
--   let y : Nat := Int.natAbs Y
--   let n : Nat := (Int.natAbs (Int.sub (y * t * den) num))^2
--   let d : PNat := 2 * num * t^2 * den
--   let C ← BernoulliExpNegSample n d
--   return (Y,C)
-- abs(e) = if e < 0 then -e else e;  e^2 = e * e
-- BernoulliExpNegSample takes dynamic (n, d) — we use a lambda.
def plAbsInt (e : Exp) : Exp :=
  probLangCond (probLangLt e (probLangInt 0)) (probLangNegInt e) e

def plSquare (e : Exp) : Exp := probLangMul e e

def plDiscreteGaussianSampleLoop (num den t : ℕ) (laplaceMixedE bernExpNegDynE : Exp) : Exp :=
  probLangBind (.named "Y") laplaceMixedE
    (let y := plAbsInt (Exp.var "Y")
     let raw := probLangSub
       (probLangMul (probLangMul y (probLangInt t)) (probLangInt den))
       (probLangInt num)
     let n := plSquare (plAbsInt raw)
     let d := probLangMul
       (probLangMul (probLangInt 2)
         (probLangMul (probLangInt num)
           (probLangMul (plSquare (probLangInt t)) (probLangInt den))))
       (probLangInt 1)
     probLangBind (.named "C") (probLangApp (probLangApp bernExpNegDynE n) d)
       (probLangPair (Exp.var "Y") (Exp.var "C")))

-- def DiscreteGaussianSample (num : PNat) (den : PNat) (mix : ℕ) : SLang ℤ := do
--   let r ← probUntil (DiscreteGaussianSampleLoop num den t mix) (λ x : Int × Bool => x.2)
--   return r.1
def plDiscreteGaussianSample (gaussianLoopE : Exp) : Exp :=
  probLangBind (.named "r")
    (plProbUntil "f" "x" "x'"
      gaussianLoopE
      (probLangLam "x" (probLangSnd (Exp.var "x"))))
    (probLangFst (Exp.var "r"))

-- def DiscreteGaussianGenSample (num : PNat) (den : PNat) (μ : ℤ) : SLang ℤ := do
--   let s ← DiscreteGaussianSample num den 7
--   return s + μ
def plDiscreteGaussianGenSample (gaussianSamplerE : Exp) (μ : Int) : Exp :=
  probLangBind (.named "s") gaussianSamplerE
    (probLangAdd (Exp.var "s") (probLangInt μ))
-/
