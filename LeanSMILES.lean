-- The root module is a plain (non-`module`) file: it imports both the `module` files of the
-- pipeline and the plain files of the SMILES toolkit.

-- The typed SMILES toolkit (`LeanSMILES` namespace)
import LeanSMILES.main
import LeanSMILES.Scalar
import LeanSMILES.Data.CSVparser
import LeanSMILES.Examples.parsercsv
import LeanSMILES.Chem.Element
import LeanSMILES.Chem.Atom
import LeanSMILES.Chem.Bond
import LeanSMILES.Chem.Molecule
import LeanSMILES.Chem.Graph
import LeanSMILES.Chem.BondMatrix
import LeanSMILES.SMILES.Token
import LeanSMILES.SMILES.Parse
import LeanSMILES.SMILES.Write
import LeanSMILES.SMILES.Canon
import LeanSMILES.SMILES.Canonicity
import LeanSMILES.Fingerprint.Morgan
import LeanSMILES.Examples.smiles
import LeanSMILES.Examples.caffeine

-- Polymorphic definitions (any `Scalar`)
import LeanSMILES.Polymorphic.Scalar
import LeanSMILES.Polymorphic.Decimal
import LeanSMILES.Polymorphic.LinAlg
import LeanSMILES.Polymorphic.Chem.Types
import LeanSMILES.Polymorphic.Chem.Graph
import LeanSMILES.Polymorphic.Chem.SMILES
import LeanSMILES.Polymorphic.Chem.Fingerprint
import LeanSMILES.Polymorphic.Chem.Descriptors
import LeanSMILES.Polymorphic.Chem.Matrices
import LeanSMILES.Polymorphic.Chem.Distance
import LeanSMILES.Polymorphic.Chem.Representation
import LeanSMILES.Polymorphic.ML.Types
import LeanSMILES.Polymorphic.ML.LinearModel
import LeanSMILES.Polymorphic.ML.GradientDescent
import LeanSMILES.Polymorphic.ML.LeastSquares
import LeanSMILES.Polymorphic.ML.Perceptron
import LeanSMILES.Polymorphic.ML.Metrics
import LeanSMILES.Polymorphic.ML.Algorithm
import LeanSMILES.Polymorphic.Pipeline
import LeanSMILES.Polymorphic.Certificates
-- `Float`: execution
import LeanSMILES.Float.Scalar
import LeanSMILES.Float.ML
import LeanSMILES.Float.Chem
import LeanSMILES.Float.Pipeline
-- `ℝ`: the proof-side instance
import LeanSMILES.Real.Scalar
-- Proofs
import LeanSMILES.Proofs.Basic
import LeanSMILES.Proofs.LinAlg
import LeanSMILES.Proofs.LinSolve
import LeanSMILES.Proofs.Decimal
import LeanSMILES.Proofs.Chem.SMILES
import LeanSMILES.Proofs.Chem.Fingerprint
import LeanSMILES.Proofs.Chem.Descriptors
import LeanSMILES.Proofs.Chem.Matrices
import LeanSMILES.Proofs.Chem.Distance
import LeanSMILES.Proofs.Chem.Representation
import LeanSMILES.Proofs.ML.Basic
import LeanSMILES.Proofs.ML.LeastSquares
import LeanSMILES.Proofs.ML.Convergence
import LeanSMILES.Proofs.ML.Perceptron
import LeanSMILES.Proofs.ML.Metrics
import LeanSMILES.Proofs.Pipeline
import LeanSMILES.Proofs.Certificates
