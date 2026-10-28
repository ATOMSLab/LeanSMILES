module

-- LeanLearn: learning algorithms on tabular data `(X, y)` and their proofs. Imports Mathlib only.
-- Every executable algorithm is written once over the scalar interface: `Float` is what runs,
-- `ℝ` is what the theorems are about. The executable code is at the top level and exposes its
-- definition bodies; everything under `Proofs/` is over `ℝ`.

-- The scalar interface: `ScalarLike`, its polynomial fragment, and the `Float`-usable sums
public import LeanLearn.Scalar
-- Linear regression over any scalar: the problem, its iterative solvers (gradient descent,
-- Jacobi, Gauss–Seidel) and the exact `ℚ` certificate checks that run before them
public import LeanLearn.Regression.Problem
public import LeanLearn.Regression.Solvers
public import LeanLearn.Regression.Certificates
-- The residual certificate on sparse 0/1 features (Morgan bits), from the bit lists
public import LeanLearn.Regression.SparseProblem
-- The prediction, squared error and ridge objective on a Mathlib matrix, over any scalar
public import LeanLearn.Regression.LinearModel
-- Householder-QR solvers on `Float` arrays
public import LeanLearn.Regression.OLSFloat
public import LeanLearn.Regression.RidgeFloat
-- Ridge on sparse 0/1 features (conjugate gradients) and regression metrics: R², RMSE, MAE
public import LeanLearn.Regression.SparseRidge
public import LeanLearn.Regression.Metrics
-- Classification
public import LeanLearn.Classification.Logistic
public import LeanLearn.Classification.ROC
-- Plots written as SVG
public import LeanLearn.Plot.Parity
-- Proofs over ℝ, part one: least squares in closed form on Mathlib matrices — OLS, ridge, and
-- the two against each other (the trade-off, shrinkage, the ridge path)
public import LeanLearn.Proofs.LeastSquares.OLS
public import LeanLearn.Proofs.LeastSquares.Ridge
public import LeanLearn.Proofs.LeastSquares.RidgeOLS
-- Proofs over ℝ, part two: the executable code read in ℝ — the quadratic loss, gradient
-- descent, Jacobi and Gauss–Seidel, certificate soundness, and the bridges to the closed form
public import LeanLearn.Proofs.Regression.Basic
public import LeanLearn.Proofs.Regression.GradientDescent
public import LeanLearn.Proofs.Regression.Iterative
public import LeanLearn.Proofs.Regression.Certificates
public import LeanLearn.Proofs.Regression.SparseProblem
public import LeanLearn.Proofs.Regression.MatrixBridge
public import LeanLearn.Proofs.Regression.LinearModel
-- Examples: worked proofs (`ols`, `ridge`) and runs of the `Float` solvers
public import LeanLearn.Examples.ols
public import LeanLearn.Examples.ridge
public import LeanLearn.Examples.olsFloat
public import LeanLearn.Examples.ridgeFloat
