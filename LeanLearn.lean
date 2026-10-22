module

-- The scalar interface every executable algorithm is written over: `Float` runs, `ℝ` proves
public import LeanLearn.Scalar
-- Linear regression: the problem, its iterative solvers and their certificate checks
public import LeanLearn.Regression.Problem
public import LeanLearn.Regression.Solvers
public import LeanLearn.Regression.Certificates
-- Linear regression: exact specifications over ℝ (closed form) and the bridge to execution
public import LeanLearn.Regression.OLS
public import LeanLearn.Regression.Ridge
public import LeanLearn.Regression.RidgeOLS
public import LeanLearn.Regression.LinearModel
-- Linear regression: Householder-QR solvers on `Float`
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
-- Proofs (over ℝ)
public import LeanLearn.Proofs.Regression.Basic
public import LeanLearn.Proofs.Regression.MatrixBridge
public import LeanLearn.Proofs.Regression.GradientDescent
public import LeanLearn.Proofs.Regression.Iterative
public import LeanLearn.Proofs.Regression.Certificates
-- Optimization and learning theory (from TorchLean)
public import LeanLearn.Optimization.GDLinearConvergence
public import LeanLearn.Optimization.StronglyConvexGD
public import LeanLearn.Optimization.SmoothStrongConvexBridge
public import LeanLearn.LearningTheory.Stability.Core
public import LeanLearn.LearningTheory.Stability.RidgeRegression1D
-- Examples
public import LeanLearn.Examples.ols
public import LeanLearn.Examples.ridge
public import LeanLearn.Examples.olsFloat
public import LeanLearn.Examples.ridgeFloat
