/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Data.CSVparser
public import LeanSMILES.Examples.parsercsv
public import LeanSMILES.Chem.Element
public import LeanSMILES.Chem.Atom
public import LeanSMILES.Chem.Bond
public import LeanSMILES.Chem.Molecule
public import LeanSMILES.Chem.Charge
public import LeanSMILES.Chem.Graph
public import LeanSMILES.Chem.BondMatrix
public import LeanSMILES.Chem.Stereo
public import LeanSMILES.SMILES.Token
public import LeanSMILES.SMILES.Parse
public import LeanSMILES.SMILES.Write
public import LeanSMILES.SMILES.Canon
public import LeanSMILES.SMILES.Canonicity
public import LeanSMILES.Fingerprint.Morgan
public import LeanSMILES.Fingerprint.MorganInvariance
public import LeanSMILES.Fingerprint.MorganRadius3
public import LeanSMILES.Fingerprint.Tanimoto
public import LeanSMILES.Aromaticity.Perceive
public import LeanSMILES.Depict.Graph
public import LeanSMILES.Depict.Layout
public import LeanSMILES.Depict.Svg
public import LeanSMILES.Depict.Widget
public import LeanSMILES.Examples.smiles
public import LeanSMILES.Examples.caffeine
public import LeanSMILES.Examples.depict

/-!
# LeanSMILES

The typed SMILES toolkit: elements, atoms, bonds and the molecular graph `Molecule n`
(`Chem/`), the SMILES tokenizer, parser, writer and canonical SMILES with its canonicity proof
(`SMILES/`), RDKit-compatible Morgan fingerprints and Tanimoto similarity (`Fingerprint/`),
aromaticity perception (`Aromaticity/`), 2D depiction (`Depict/`), the CSV reader for the
Delaney table (`Data/`) and the worked examples (`Examples/`). Importing this module imports
all of them.
-/
