module

public import LeanSMILES.Float.Scalar
public import LeanSMILES.Polymorphic.Chem.Representation

/-!
# Molecules on `Float`

The `Float` side of `Polymorphic/Chem/`, plus string-level entry points (an RDKit-style
`Chem` API). The numeric definitions (molecular weight, Tanimoto similarity, matrix
representations, features) are generic in `[Scalar α]`. They run here at `α := Float`,
specialized once in this precompiled module, and their theorems are stated over `ℝ` in
`Proofs/Chem/`. Each `*_eq` lemma below holds by `rfl`.

Open `Chem.Exec` to use the `Float` versions.
-/

@[expose] public section

namespace Chem.Exec

/-- Parse a SMILES string and check the result is well-formed with at least one atom
(RDKit's `MolFromSmiles`). Surrounding whitespace is ignored. -/
def molFromSmiles (s : String) : Except String Molecule := do
  let m ← (SMILES.mk s.trimAscii.toString).parse
  unless decide m.WellFormed do throw "bond refers to a missing atom"
  unless 0 < m.atoms.size do throw "empty molecule"
  return m

/-- Canonical SMILES of a molecule (RDKit's `MolToSmiles`). -/
def molToSmiles (m : Molecule) : String := m.canonicalSMILES.smiles.str

/-- Canonical SMILES of a SMILES string. -/
def canonicalize (s : String) : Except String String := molToSmiles <$> molFromSmiles s

def molecularWeight (m : Molecule) : Float := m.molecularWeight

/-- Morgan fingerprint (RDKit's `GetMorganGenerator(radius, fpSize).GetFingerprint`). -/
def morganFingerprint (m : Molecule) (radius nBits : Nat) : MorganFingerprint nBits :=
  m.morganFingerprint radius nBits

def fingerprintFeatures {nBits : Nat} (fp : MorganFingerprint nBits) :
    Primitives.Vec Float nBits :=
  fp.toFeatures

def tanimoto {nBits : Nat} (a b : MorganFingerprint nBits) : Float := a.tanimoto b

/-! ## Matrix representations -/

abbrev Mat (m n : Nat) := Primitives.Mat Float m n

def adjacencyMatrix (m : Molecule) : Mat m.size m.size := m.adjacencyMatrix
def bondOrderMatrix (m : Molecule) : Mat m.size m.size := m.bondOrderMatrix
def laplacianMatrix (m : Molecule) : Mat m.size m.size := m.laplacianMatrix
def distanceMatrix (m : Molecule) : Mat m.size m.size := m.distanceMatrix
def coulombMatrix (m : Molecule) : Mat m.size m.size := m.coulombMatrix
def wienerIndex (m : Molecule) : Float := m.wienerIndex

/-- Features of a molecule under a representation. -/
def featurize {n : Nat} (r : Representation Float n) (m : Molecule) : Primitives.Vec Float n :=
  r.featurize m

theorem molecularWeight_eq (m : Molecule) :
    molecularWeight m = m.molecularWeight (α := Float) := rfl
theorem tanimoto_eq {nBits : Nat} (a b : MorganFingerprint nBits) :
    tanimoto a b = a.tanimoto (α := Float) b := rfl
theorem laplacianMatrix_eq (m : Molecule) :
    laplacianMatrix m = m.laplacianMatrix (α := Float) := rfl
theorem distanceMatrix_eq (m : Molecule) :
    distanceMatrix m = m.distanceMatrix (α := Float) := rfl

end Chem.Exec

end
