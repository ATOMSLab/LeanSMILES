import LeanSMILES.SMILES.Executables
import LeanSMILES.MetaPrograms.Test

/-! Tests for the RDKit-style descriptors (`Molecule.descriptors` and friends). -/

open Chem Chem.Exec

def mol! (s : String) : Molecule := (molFromSmiles s).toOption.getD default

#eval repr (mol! "CC(=O)Oc1ccccc1C(=O)O").descriptors

-- molecular weight (RDKit `MolWt`)
#test (mol! "CCO").molecularWeightExact.toString == "46.069"
#test (mol! "c1ccccc1").molecularWeightExact.toString == "78.114"
#test (mol! "CC(=O)Oc1ccccc1C(=O)O").molecularWeightExact.toString == "180.159"
#test (mol! "[13CH4]").molecularWeightExact.toString == "17.032"
#test (molecularWeight (mol! "O") - 18.015).abs < 1e-9
-- formula (Hill order)
#test (mol! "CC(=O)Oc1ccccc1C(=O)O").formula == "C9H8O4"
#test (mol! "O").formula == "H2O"
#test (mol! "[Na+].[Cl-]").formula == "ClNa"
#test (mol! "ClC(Cl)(Cl)Cl").formula == "CCl4"
-- H-bond donors (RDKit `NumHDonors`)
#test (mol! "CCO").hDonorCount == 1
#test (mol! "CC(=O)N").hDonorCount == 1
#test (mol! "c1cc[nH]c1").hDonorCount == 1
#test (mol! "c1ccncc1").hDonorCount == 0
#test (mol! "O").hDonorCount == 0
-- rings (cyclomatic number)
#test (mol! "c1ccc2ccccc2c1").ringCount == 2
#test (mol! "C1CC2CCC1C2").ringCount == 2
#test (mol! "CCCC").ringCount == 0
#test (mol! "[Na+].[Cl-]").componentCount == 2
-- rotatable bonds (RDKit strict `NumRotatableBonds`)
#test (mol! "CCCC").rotatableBondCount == 1
#test (mol! "CCO").rotatableBondCount == 0
#test (mol! "CC(=O)NCC").rotatableBondCount == 1
#test (mol! "CCCC(F)(F)F").rotatableBondCount == 1
#test (mol! "c1ccccc1-c1ccccc1").rotatableBondCount == 1
#test (mol! "CC#CC").rotatableBondCount == 0
-- minimum degree
#test (mol! "C").minDegree == 0
#test (mol! "c1ccccc1").minDegree == 2
#test (mol! "CCO").minDegree == 1
