import LeanSMILES.SMILES.EXECUTABLES
import LeanSMILES.MetaPrograms.Test

/-! Tests for `Molecule.layout2D` (2D coordinates for drawings). -/

open Chem Chem.Exec

def mol! (s : String) : Molecule := (molFromSmiles s).toOption.getD default

def bondLengths (m : Molecule) : List Float :=
  let p := layout2D m
  m.bonds.toList.map fun b =>
    let (x1, y1) := p.getD b.src (0, 0)
    let (x2, y2) := p.getD b.dst (0, 0)
    Float.sqrt ((x1 - x2) ^ 2 + (y1 - y2) ^ 2)

#eval bondLengths (mol! "c1ccccc1")

-- benzene is a regular hexagon with unit-ish sides
#test (bondLengths (mol! "c1ccccc1")).all fun l => (l - (bondLengths (mol! "c1ccccc1")).head!).abs < 0.01
#test (bondLengths (mol! "c1ccccc1")).all fun l => 0.7 < l && l < 1.3
-- bonds stay near unit length in larger molecules
#test (bondLengths (mol! "CC(=O)Oc1ccccc1C(=O)O")).all fun l => 0.6 < l && l < 1.5
#test (bondLengths (mol! "CN1C=NC2=C1C(=O)N(C(=O)N2C)C")).all fun l => 0.6 < l && l < 1.5
-- one position per atom, all finite
#test (layout2D (mol! "CCO")).size == 3
#test (layout2D (mol! "CC(C)Cc1ccc(cc1)C(C)C(=O)O")).all fun (x, y) => !x.isNaN && !y.isNaN
-- fragments are placed side by side, not on top of each other
#test let p := layout2D (mol! "[Na+].[Cl-]")
  ((p.getD 0 (0, 0)).1 - (p.getD 1 (0, 0)).1).abs ≥ 1.5
