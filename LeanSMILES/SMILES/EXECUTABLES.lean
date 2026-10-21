module

public import LeanSMILES.SMILES.DEFINITIONS

/-!
# SMILES — Executables

The `Float` side of the SMILES definitions, plus string-level entry points for notebooks
(an RDKit-style `Chem` API). The numeric definitions (molecular weight, Tanimoto
similarity, fingerprint features, 2D layout) are generic in `[Scalar α]`. They run here
at `α := Float`, specialized once in this precompiled module, and their theorems are
stated over `ℝ` in `PROOFS.lean`. Each `*_eq` lemma below holds by `rfl`.

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

/-- 2D drawing coordinates (bond length ≈ 1). -/
def layout2D (m : Molecule) (iters : Nat := 300) : Array (Float × Float) := m.layout2D iters

theorem molecularWeight_eq (m : Molecule) :
    molecularWeight m = m.molecularWeight (α := Float) := rfl
theorem tanimoto_eq {nBits : Nat} (a b : MorganFingerprint nBits) :
    tanimoto a b = a.tanimoto (α := Float) b := rfl
theorem layout2D_eq (m : Molecule) (iters : Nat) :
    layout2D m iters = m.layout2D (α := Float) iters := rfl

end Chem.Exec

end
