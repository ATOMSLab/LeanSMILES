/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
import LeanSMILES.SMILES.Canon
import LeanSMILES.Chem.Graph
import LeanSMILES.Chem.BondMatrix
import LeanSMILES.Fingerprint.Morgan
import LeanSMILES.Data.CSVparser

/-!
# Examples: SMILES → molecule → graph → canonical SMILES

Open this file in the editor; the Infoview shows each `#eval`.
-/

open LeanSMILES LeanSMILES.SMILES

-- A parse is an `Except`: the molecule, or a positioned error.
#eval parse "CCO"
#eval parse "c1cc[nH]c1"
#eval parse "[13CH3][NH3+].[Cl-]"
#eval parse "C1CC"
#eval parse "C()C"

-- Three strings, one molecule, one canonical SMILES.
#eval (Mol.ofSmiles! "OCC").canonicalSmiles
#eval (Mol.ofSmiles! "C(O)C").canonicalSmiles
#eval (Mol.ofSmiles! "CCO").canonicalSmiles

-- Camphene written two ways (ThermoPropertiesSMILES.csv, isomeric and canonical columns).
#eval (Mol.ofSmiles! "CC1(C)C2CCC(C2)C1=C").canonicalSmiles
#eval (Mol.ofSmiles! "CC1(C2CCC(C2)C1=C)C").canonicalSmiles

-- Where exhaustive tie-breaking matters: a 12-carbon cubic cage whose atoms no
-- refinement tells apart. RDKit 2026.09.1 returns eight different "canonical"
-- SMILES for it depending on the input atom order (two of them below); the
-- search over every tied atom returns one.
#eval ["C12C3C1C(C1C4C5C1C1C4C51)C23", "C12C3C1C1C2C3C1C1C2C3C2C31"].map fun s ↦
  (Mol.ofSmiles! s).canonicalSmiles

-- Canonicalization relabels the atoms; the graph is the same up to isomorphism
-- (`Molecule.canonicalizeIso`).
#eval (Mol.ofSmiles! "OCC").canonicalize
#eval (Mol.ofSmiles! "c1ccccc1C").canonicalize

-- The Mathlib views: bond-order-weighted and 0/1 adjacency matrices.
#eval (Mol.ofSmiles! "C=CO").mol.adjMatrix
#eval (Mol.ofSmiles! "C=CO").mol.graph.adjMatrix ℚ

-- The same two matrices as subtypes that say they come from a molecule
-- (`BondMatrix`: entries are bond orders; `FlatMatrix`: Mathlib's `IsAdjMatrix`),
-- with O(1) lookups, and the normal form that is nothing but atoms + bond matrix.
#eval (Mol.ofSmiles! "C=CO").mol.toBondMatrix
#eval (Mol.ofSmiles! "C=CO").mol.toBondMatrix.flatten
#eval let M := Mol.ofSmiles! "C=CO"
      let B := M.mol.toBondMatrix
      (List.finRange M.n).map fun i ↦ (List.finRange M.n).map fun j ↦ B.kindAt i j
#eval (Mol.ofSmiles! "C1CC1").isNormal       -- false: the ring-closure bond is stored 2→0
#eval (Mol.ofSmiles! "C1CC1").normalize      -- bonds now 0-1, 0-2, 1-2
#eval (Mol.ofSmiles! "C1CC1").normalize.isNormal
#eval (BondMatrix.ofMatrix? !![0, 7; 7, 0]).isSome       -- 7 is not a bond order
#eval (BondMatrix.ofMatrix? !![0, 2; 2, 0]).isSome

-- Hydrogens by the default-valence rule.
#eval let M := Mol.ofSmiles! "CC(C)(C)O"; (List.finRange M.n).map fun i ↦ (M.mol.atom i).totalH

-- What is *not* done: no aromaticity perception, so a Kekulé benzene stays Kekulé.
#eval (Mol.ofSmiles! "C1=CC=CC=C1").canonicalSmiles
#eval (Mol.ofSmiles! "c1ccccc1").canonicalSmiles

-- Morgan fingerprints (radius 2, 2048 bits), RDKit's hashing on the graph as written.
#eval (Mol.ofSmiles! "CCO").morganBits
#eval (Mol.ofSmiles! "CCO").morganIds
#eval (Mol.ofSmiles! "OCC").morganIds == (Mol.ofSmiles! "CCO").morganIds
#eval tanimoto (Mol.ofSmiles! "CCO").morganBits (Mol.ofSmiles! "CCCO").morganBits
-- `.toList`: `#eval` of a `Vector` whose length is not a literal makes the elaborator
-- check the size proof by reducing the whole parse in the kernel (design notes §8).
#eval (Mol.ofSmiles! "c1ccccc1CC").mol.inRingVector.toList

-- From the solubility dataset.
def delaney := CSVparser.load "datasets/delaney-processed.csv"
#eval (delaney.toList.take 5).map fun r ↦ (r.smiles, (Mol.ofSmiles! r.smiles).canonicalSmiles)
