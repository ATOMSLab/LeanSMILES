/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

-- Molecules (LeanSMILES) meet learning algorithms (LeanLearn): the only library that imports both
public import Pipelines.Representation
public import Pipelines.Pipeline
public import Pipelines.Data
public import Pipelines.Certificates
-- Proofs (over ℝ)
public import Pipelines.Proofs.Representation
public import Pipelines.Proofs.Certificates
-- Walkthroughs: solubility regression on the Delaney table, EGFR classification
public import Pipelines.Examples.delaney
public import Pipelines.Examples.egfr

/-!
# Pipelines

Molecules as tabular data: the only library that imports both `LeanSMILES` and `LeanLearn`.
Representations of a molecule as a feature vector, labelled molecules read from the CSV tables
in `datasets/`, certified regression pipelines and their soundness proofs, and the Delaney and
EGFR walkthroughs. Importing this module imports all of them.
-/
