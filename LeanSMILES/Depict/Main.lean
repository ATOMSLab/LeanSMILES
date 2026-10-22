/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ejike Ugwuanyi, Claude (Anthropic)
-/
module

public import LeanSMILES.Depict.Cli

/-!
# LeanSMILES.Depict.Main

Entry point of `lake exe depict`; everything is in `LeanSMILES.Depict.Cli`.
-/

public section

/-- `lake exe depict`. -/
def main (args : List String) : IO UInt32 := LeanSMILES.Depict.main args
