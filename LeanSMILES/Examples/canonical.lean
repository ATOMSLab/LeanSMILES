import LeanSMILES.Data.CSVparser
import LeanSMILES.Canonical
open CSVparser Chem

/-!
# Example: SMILES → canonical SMILES

A SMILES string can be written many ways for the same molecule. The canonical
SMILES is one fixed spelling per molecule, so two molecules are the same exactly
when their canonical SMILES are equal. `canonicalSmiles` gives the same string as
RDKit's `Chem.MolToSmiles(Chem.MolFromSmiles(s), isomericSmiles=False)`.

Click on an `#eval` line to see its result in the Infoview.
-/

-- One molecule
#eval canonicalSmiles "OCC"                       -- "CCO" (ethanol)

-- Different ways of writing the same molecule give the same answer
#eval ["OCC", "CCO", "C(O)C"].map canonicalSmiles
#eval ["c1ccccc1", "C1=CC=CC=C1", "C=1C=CC=CC=1"].map canonicalSmiles       -- benzene
#eval ["CC(=O)Oc1ccccc1C(=O)O", "OC(=O)c1ccccc1OC(C)=O"].map canonicalSmiles -- aspirin

-- So canonical SMILES can tell whether two SMILES are the same molecule
def sameMolecule (a b : String) : Bool :=
  match canonicalSmiles a, canonicalSmiles b with
  | .ok x, .ok y => x == y
  | _, _ => false

#eval sameMolecule "Oc1ccccc1N(=O)=O" "O=[N+]([O-])c1ccccc1O"   -- true: same nitrophenol
#eval sameMolecule "Oc1ccccc1N(=O)=O" "Oc1ccc(cc1)N(=O)=O"      -- false: different isomer

-- RDKit's chemistry is applied on the way: aromaticity is detected, nitro groups
-- are charge-separated, fragments are sorted
#eval canonicalSmiles "C1=CC=C2C=CC=CC2=C1"        -- naphthalene, Kekulé input
#eval canonicalSmiles "CN(=O)=O"                   -- nitromethane
#eval canonicalSmiles "[Cl-].[NH4+]"

-- Hydrogens written as atoms are folded in, as RDKit does (isotopic ones stay)
#eval ["[H]C([H])([H])[H]", "[H]O[H]", "[2H]C"].map canonicalSmiles

-- The molecule graph in between (atoms, bonds, H counts) is also available
#eval (molFromSmiles "c1cc[nH]c1").map fun m =>
  ((List.range m.numAtoms).map m.totalHs, m.bonds.map (·.order))

-- Invalid SMILES give a reason instead of a string (the same ones RDKit rejects)
#eval canonicalSmiles "C1CC"                       -- ring never closed
#eval canonicalSmiles "FCl(F)(F)(F)F"              -- chlorine with five bonds
#eval canonicalSmiles "c1cccc1"                    -- cannot be kekulized

-- With the dataset: canonical SMILES of the first molecules in Delaney
def records := load "datasets/delaney-processed.csv"

#eval (List.range 5).map fun i => (records[i].smiles, canonicalSmiles records[i].smiles)
