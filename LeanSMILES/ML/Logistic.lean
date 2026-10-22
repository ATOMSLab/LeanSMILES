import LeanSMILES.Scalar
import LeanSMILES.Fingerprint.Morgan

/-!
# Logistic regression on Morgan fingerprints

Binary classification with L2-regularized logistic regression, the model of
ENCH 470 Lecture 21 (`sklearn.linear_model.LogisticRegression()`): it learns a
weight per fingerprint bit and a bias, and predicts

    P(class 1 | x) = σ(w · x + b),   σ(z) = 1 / (1 + e^(−z)).

Training minimizes scikit-learn's objective (L2 penalty, `C`, intercept not
penalized)

    ½ ‖w‖² + C · Σᵢ log(1 + e^(−ỹᵢ (w · xᵢ + b))),   ỹᵢ = ±1,

with Nesterov-accelerated gradient descent until the gradient is (nearly) zero.
The objective is strongly convex in `w`, so this reaches the same optimum as
scikit-learn's solver.

Fingerprints are sparse (about 40 of 2048 bits set), so a sample is stored as
the list of its on-bits and `w · x` is a sum over those bits.

Everything is written once over Tyler's `ScalarLike` (`LeanSMILES/Scalar.lean`):
run it at `Float`; state theorems at `ℝ`.
-/

namespace LeanSMILES.ML

/-- A scalar with `exp` and `log`, which the logistic function needs and
`ScalarLike` does not provide. -/
class ExpLog (K : Type) where
  exp : K → K
  log : K → K

instance : ExpLog Float := ⟨Float.exp, Float.log⟩
noncomputable instance : ExpLog ℝ := ⟨Real.exp, Real.log⟩

/-- A sample with 0/1 features, stored as the indices of its 1s (e.g. Morgan on-bits). -/
abbrev SparseBits := Array Nat

variable {K : Type} [ScalarLike K] [ExpLog K]

/-- The logistic function σ(z) = 1 / (1 + e^(−z)), written so `exp` never overflows. -/
def sigmoid (z : K) : K :=
  if 0 ≤ z then 1 / (1 + ExpLog.exp (-z))
  else let e := ExpLog.exp z; e / (1 + e)

/-- log(1 + e^t), written so `exp` never overflows. -/
def softplus (t : K) : K :=
  if 0 < t then t + ExpLog.log (1 + ExpLog.exp (-t))
  else ExpLog.log (1 + ExpLog.exp t)

structure LogisticModel (K : Type) where
  weights : Array K
  bias : K

namespace LogisticModel

/-- The score w · x + b (the "decision function"). -/
def score (m : LogisticModel K) (x : SparseBits) : K :=
  x.foldl (fun s j => s + m.weights.getD j 0) m.bias

/-- Probability of class 1 (scikit-learn's `predict_proba(x)[1]`). -/
def proba (m : LogisticModel K) (x : SparseBits) : K := sigmoid (m.score x)

/-- Predicted class: `true` (1) when the score is positive, as scikit-learn's `predict`. -/
def predict (m : LogisticModel K) (x : SparseBits) : Bool := 0 < m.score x

end LogisticModel

structure LogisticConfig (K : Type) [ScalarLike K] where
  /-- Inverse regularization strength, as scikit-learn's `C`. -/
  C : K := 1
  maxIter : Nat := 20000
  /-- Stop when every gradient component is below this. -/
  tol : K := 0.000000001

/-- The training objective ½ ‖w‖² + C Σᵢ log(1 + e^(−ỹᵢ scoreᵢ)). -/
def objective (C : K) (data : Array (SparseBits × Bool)) (m : LogisticModel K) : K :=
  let reg := m.weights.foldl (fun s w => s + w * w) 0 / 2
  reg + C * data.foldl (fun s (x, y) =>
    let z := m.score x
    s + softplus (if y then -z else z)) 0

/-- Gradient of `objective`: w + C Σᵢ (σ(scoreᵢ) − yᵢ) xᵢ for the weights,
C Σᵢ (σ(scoreᵢ) − yᵢ) for the bias. -/
def gradient (C : K) (data : Array (SparseBits × Bool)) (m : LogisticModel K) :
    LogisticModel K := Id.run do
  let mut gw := m.weights
  let mut gb : K := 0
  for (x, y) in data do
    let r := C * (sigmoid (m.score x) - (if y then 1 else 0))
    gb := gb + r
    for j in x do
      gw := gw.modify j (· + r)
  return { weights := gw, bias := gb }

/-- The curvature of `objective` is at most 1 + (C/4)·λ, where λ is the largest
eigenvalue of AᵀA for the 0/1 matrix A = [X | 1]. λ is estimated by 50 steps of
power iteration and padded by 10 %; the restart in `fitLogistic` keeps the
method safe even if the estimate is slightly low. -/
def lipschitzBound (C : K) (nFeatures : Nat) (data : Array (SparseBits × Bool)) : K := Id.run do
  -- v has one entry per feature plus one for the bias column
  let mut v : Array K := Array.replicate (nFeatures + 1) 1
  let mut lam : K := 1
  for _ in [0:50] do
    -- u = A v, then w = Aᵀ u
    let mut w : Array K := Array.replicate (nFeatures + 1) 0
    for (x, _) in data do
      let u := x.foldl (fun s j => s + v.getD j 0) (v.getD nFeatures 0)
      for j in x do
        w := w.modify j (· + u)
      w := w.modify nFeatures (· + u)
    let norm := ScalarLike.sqrt (w.foldl (fun s a => s + a * a) 0)
    let vnorm := ScalarLike.sqrt (v.foldl (fun s a => s + a * a) 0)
    if norm == 0 then break
    lam := norm / vnorm
    v := w.map (· / norm)
  return 1 + C / 4 * (lam * 1.1)

/-- Train a logistic regression model on samples with `nFeatures` 0/1 features
and labels `true` (class 1) / `false` (class 0). Returns the model and the
number of iterations used.

Nesterov's accelerated gradient with gradient-based restart (O'Donoghue &
Candès, 2015): the momentum is reset whenever the step points uphill, which
keeps the method fast without comparing objective values. -/
def fitLogistic (cfg : LogisticConfig K) (nFeatures : Nat) (data : Array (SparseBits × Bool)) :
    LogisticModel K × Nat := Id.run do
  let step := 1 / lipschitzBound cfg.C nFeatures data
  let zero : LogisticModel K := { weights := Array.replicate nFeatures 0, bias := 0 }
  let mut model := zero          -- current iterate
  let mut prev := zero           -- previous iterate
  let mut t : K := 1             -- momentum parameter
  let mut iters := cfg.maxIter
  for k in [0:cfg.maxIter] do
    -- look-ahead point y = model + β (model − prev)
    let tNext := (1 + ScalarLike.sqrt (1 + 4 * t * t)) / 2
    let β := (t - 1) / tNext
    let y : LogisticModel K :=
      { weights := (model.weights.zip prev.weights).map fun (a, p) => a + β * (a - p),
        bias := model.bias + β * (model.bias - prev.bias) }
    let g := gradient cfg.C data y
    -- converged when the gradient is (nearly) zero
    let gmax := g.weights.foldl (fun s d => max s (ScalarLike.abs d)) (ScalarLike.abs g.bias)
    if gmax < cfg.tol then
      model := y
      iters := k + 1
      break
    let next : LogisticModel K :=
      { weights := (y.weights.zip g.weights).map fun (a, d) => a - step * d,
        bias := y.bias - step * g.bias }
    -- restart if the gradient at y makes an acute angle with the step taken
    let uphill := (g.weights.zip ((next.weights.zip model.weights).map fun (a, b) => a - b)).foldl
      (fun s (d, e) => s + d * e) (g.bias * (next.bias - model.bias))
    prev := model
    model := next
    t := if 0 < uphill then 1 else tNext
  return (model, iters)

/-! ## Evaluation -/

/-- Fraction of samples whose predicted class equals the label. -/
def accuracy (m : LogisticModel K) (data : Array (SparseBits × Bool)) : Float :=
  let ok := (data.filter fun (x, y) => m.predict x == y).size
  ok.toFloat / data.size.toFloat

/-- Confusion matrix in scikit-learn's layout: rows = true class (0, 1),
columns = predicted class (0, 1), i.e. [[TN, FP], [FN, TP]]. -/
def confusionMatrix (m : LogisticModel K) (data : Array (SparseBits × Bool)) : List (List Nat) :=
  let count (y p : Bool) := (data.filter fun (x, y') => y' == y && m.predict x == p).size
  [[count false false, count false true], [count true false, count true true]]

/-- Morgan on-bits of a SMILES string as a sparse feature vector (radius 2,
2048 bits by default), ready for `fitLogistic`. -/
def morganFeatures (s : String) (radius : ℕ := 2) (fpSize : ℕ := 2048) :
    Except SMILES.ParseError SparseBits :=
  (SMILES.morganBits s radius fpSize).map List.toArray

end LeanSMILES.ML
