/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ejike Ugwuanyi
-/
module

public import ProofWidgets.Component.HtmlDisplay
public import LeanSMILES.SMILES.Parse
public import LeanSMILES.Depict.Svg
public import LeanSMILES.Depict.Fingerprint
-- `#draw` runs the parser and the drawing at elaboration time
public meta import LeanSMILES.SMILES.Parse
public meta import LeanSMILES.Depict.Svg
public meta import LeanSMILES.Depict.Fingerprint

/-!
# LeanSMILES.Depict.Widget

`#draw` shows a molecule in the editor's Infoview, as the SVG of
`LeanSMILES.Depict.Svg` handed to ProofWidgets:

```lean
#draw "Cn1cnc2c1c(=O)n(C)c(=O)n2C"      -- a SMILES string
#draw (Mol.ofSmiles! "C[C@H](N)C(=O)O")  -- a parsed molecule
#draw caffeine.mol                       -- a `Molecule n`
```

`#fingerprint` shows a Morgan fingerprint (`LeanSMILES.Depict.Fingerprint`) as a
grid and a barcode; with a second SMILES, the bits both share are highlighted:

```lean
#fingerprint "CC(=O)Oc1ccccc1C(=O)O"
#fingerprint "CC(=O)Oc1ccccc1C(=O)O", "Cn1cnc2c1c(=O)n(C)c(=O)n2C"
```

ProofWidgets comes with Mathlib, so nothing new is required; the picture
appears when the cursor is on the command.
-/

@[expose] public section

open Lean ProofWidgets

namespace LeanSMILES.Depict

/-- `stroke-width` ↦ `strokeWidth`: React spells SVG attributes in camel case. -/
meta def camel (s : String) : String :=
  match s.splitOn "-" with
  | [] => s
  | w :: ws => w ++ String.join (ws.map String.capitalize)

/-- Convert to ProofWidgets HTML. ProofWidgets is not on the module system, so its
`Html` is `meta` here; `#draw` only runs this at elaboration time. -/
meta partial def Xml.toHtml : Xml → Html
  | .text s => .text s
  | .elem tag attrs children =>
    .element tag (attrs.toArray.map fun (k, v) ↦ (camel k, Json.str v))
      (children.toArray.map Xml.toHtml)

/-- Anything `#draw` can show. -/
class Drawable (α : Type) where
  /-- The molecule to draw. -/
  toMol : α → Mol

instance : Drawable Mol := ⟨id⟩
instance {n : ℕ} : Drawable (Molecule n) := ⟨fun m ↦ ⟨n, m⟩⟩
instance : Drawable String := ⟨Mol.ofSmiles!⟩

/-- The Infoview picture of a drawable value. -/
meta def html {α : Type} [Drawable α] (x : α) : Html :=
  ((Drawable.toMol x).svg).toHtml

/-- The Infoview picture of a SMILES string's Morgan fingerprint, compared with
`other` if given. -/
meta def fingerprintHtml (s : String) (other : Option String := none) : Html :=
  match smilesFingerprintSvg s other with
  | .ok x => x.toHtml
  | .error e => .text e

end LeanSMILES.Depict

namespace LeanSMILES

/-- `#draw t`: show the molecule `t` (a SMILES string, a `Mol` or a
`Molecule n`) in the Infoview. -/
macro "#draw " t:term : command => `(#html LeanSMILES.Depict.html $t)

/-- `#fingerprint s`: show the Morgan fingerprint (radius 2, 2048 bits) of the
SMILES string `s` in the Infoview, as a grid and a barcode.
`#fingerprint s, t` also highlights the bits `t` shares and gives the Tanimoto
similarity. -/
syntax "#fingerprint " term (", " term)? : command

macro_rules
  | `(#fingerprint $s) => `(#html LeanSMILES.Depict.fingerprintHtml $s)
  | `(#fingerprint $s, $t) => `(#html LeanSMILES.Depict.fingerprintHtml $s (some $t))

end LeanSMILES
