/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ejike Ugwuanyi
-/
module

public import LeanSMILES.Depict.Widget
-- The same modules again as `meta` imports: the `#eval`s and `#draw`s run their code at
-- elaboration time.
meta import LeanSMILES.Depict.Widget
meta import LeanSMILES.SMILES.Parse
meta import LeanSMILES.Depict.Svg

/-!
# Drawing molecules

Put the cursor on a `#draw` line and the Infoview shows the picture. The same
drawing is available as text: `Mol.svgString` for the SVG, `Mol.molBlock` for
an MDL mol block with wedge/hash flags, `Mol.coordinates` for the bare
coordinates.
-/

public section

open LeanSMILES LeanSMILES.SMILES

-- `#draw` shows a widget rather than logging text, which this linter mistakes for silence
set_option linter.hashCommand false

/-! ### Flat molecules: rings become regular polygons, chains zigzag -/

#draw "Cn1cnc2c1c(=O)n(C)c(=O)n2C"          -- caffeine
#draw "CC(=O)Oc1ccccc1C(=O)O"                -- aspirin
#draw "CCCCCCCCCC(=O)O"                      -- decanoic acid
#draw "c1ccc2c(c1)ccc1ccccc12"               -- phenanthrene

/-! ### Stereocentres: one wedge or hash per `@`/`@@`, chosen by signed volume -/

#draw "C[C@H](N)C(=O)O"                      -- L-alanine
#draw "OC[C@H]1O[C@@H](O)[C@H](O)[C@@H](O)[C@@H]1O"  -- β-D-glucose
#draw "C[C@]12CC[C@H]3[C@@H](CCc4cc(O)ccc34)[C@@H]1CC[C@@H]2O"  -- estradiol

/-! ### Double bonds: `/` `\` fix the cis/trans arrangement -/

#draw "F/C=C/F"                              -- trans
#draw "F/C=C\\F"                             -- cis
#draw "C/C=C/C=C/C"                          -- (2E,4E)-hexadiene

/-! ### Cages: three or more rings that cannot lie flat are drawn in perspective -/

#draw "C12C3C4C1C5C2C3C45"                   -- cubane
#draw "C1C2CC3CC1CC(C2)C3"                   -- adamantane
#draw "C1CC2CCC1C2"                          -- norbornane

/-! ### Labels: heteroatoms, charges, isotopes, hydrogens -/

#draw "[NH4+].[O-]C(=O)C"                    -- ammonium acetate
#draw "[13CH3]C(=O)O[2H]"                    -- isotope labels, D for ²H
#draw "O=[N+]([O-])c1ccccc1"                 -- nitrobenzene

/-! ### The text forms -/

#eval (Mol.ofSmiles! "C[C@H](N)C(=O)O").coordinates
#eval IO.println (Mol.ofSmiles! "F/C=C/F").molBlock
#eval (Mol.ofSmiles! "CCO").svgString.length
