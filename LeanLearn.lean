-- The scalar interface every executable algorithm is written over: `Float` runs, `ℝ` proves
import LeanLearn.Scalar
-- Linear regression: the problem, its iterative solvers and their certificate checks
import LeanLearn.Regression.Problem
import LeanLearn.Regression.Solvers
import LeanLearn.Regression.Certificates
-- Linear regression: exact specifications over ℝ (closed form) and the bridge to execution
import LeanLearn.Regression.OLS
import LeanLearn.Regression.Ridge
import LeanLearn.Regression.LinearModel
-- Linear regression: Householder-QR solvers on `Float`
import LeanLearn.Regression.OLSFloat
import LeanLearn.Regression.RidgeFloat
-- Classification
import LeanLearn.Classification.Logistic
-- Proofs (over ℝ)
import LeanLearn.Proofs.Regression.Basic
import LeanLearn.Proofs.Regression.GradientDescent
import LeanLearn.Proofs.Regression.Iterative
import LeanLearn.Proofs.Regression.Certificates
-- Optimization and learning theory (from TorchLean)
import LeanLearn.Optimization.GDLinearConvergence
import LeanLearn.Optimization.StronglyConvexGD
import LeanLearn.Optimization.SmoothStrongConvexBridge
import LeanLearn.LearningTheory.Stability.Core
import LeanLearn.LearningTheory.Stability.RidgeRegression1D
-- Examples
import LeanLearn.Examples.ols
import LeanLearn.Examples.ridge
import LeanLearn.Examples.olsFloat
import LeanLearn.Examples.ridgeFloat
