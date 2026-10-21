import LeanSMILES.Canonical.Molecule
import LeanSMILES.Canonical.Parse
import LeanSMILES.Canonical.Sanitize
import LeanSMILES.Canonical.Write

/-!
# LeanSMILES.Canonical

SMILES → canonical SMILES, matching RDKit's
`Chem.MolToSmiles(Chem.MolFromSmiles(s), isomericSmiles=False)`.

    Chem.canonicalSmiles "OCC"            -- Except.ok "CCO"

| Module | Step |
|---|---|
| `LeanSMILES.Canonical.Molecule` | elements, atoms, bonds, molecule graph |
| `LeanSMILES.Canonical.Parse` | `Smiles.parse`: SMILES text → graph |
| `LeanSMILES.Canonical.Sanitize` | `Chem.molFromSmiles`: hydrogens, rings, cleanup, kekulization, aromaticity (as RDKit) |
| `LeanSMILES.Canonical.Write` | `Chem.canonicalSmiles`: rank atoms, write the string |
-/
