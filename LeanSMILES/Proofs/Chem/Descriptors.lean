module

public import LeanSMILES.Proofs.Decimal
public import LeanSMILES.Polymorphic.Chem.Descriptors

/-!
# Descriptors — Proofs
-/

public section

namespace Chem

/-- Over `ℝ`, the molecular weight is exactly the sum of the decimal atomic masses. -/
theorem molecularWeight_real (m : Molecule) :
    m.molecularWeight (α := ℝ) = m.molecularWeightExact.toReal :=
  Primitives.Decimal.toScalar_eq_toReal _

end Chem

end
