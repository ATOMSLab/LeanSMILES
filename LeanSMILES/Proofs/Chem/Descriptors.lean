/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher
-/

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
