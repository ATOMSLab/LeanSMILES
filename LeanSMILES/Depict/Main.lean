/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ejike Ugwuanyi
-/
module

public import LeanSMILES.Depict.Cli

/-!
# LeanSMILES.Depict.Main

Entry point of `lake exe depict`; everything is in `LeanSMILES.Depict.Cli`.
-/

public section

/-- Entry point of `lake exe depict` (SVG drawings, mol blocks, gallery pages from SMILES): hands
the arguments to `LeanSMILES.Depict.main`, whose module `Depict/Cli` documents the flags. -/
def main (args : List String) : IO UInt32 := LeanSMILES.Depict.main args
