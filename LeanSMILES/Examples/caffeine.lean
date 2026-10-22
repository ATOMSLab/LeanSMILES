/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
import LeanSMILES.SMILES.Canon
import LeanSMILES.Chem.Graph
import LeanSMILES.Fingerprint.Morgan
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# One molecule, every representation

Caffeine, C₈H₁₀N₄O₂, walked through the pipeline one representation at a
time.  Open this file in the editor; the Infoview shows each `#eval`.

```
        O
        ‖
  CH₃–N–C   C––N–CH₃
       |   ‖    ‖
   O═C   C–––N  CH
       \ /       ‖
   CH₃–N         N
```

Fourteen heavy atoms: eight carbons, four nitrogens, two oxygens.  Two fused
rings, nine ring atoms, all written aromatic.  Three N-methyls.
-/

open LeanSMILES LeanSMILES.SMILES LeanSMILES.Molecule

/-- Caffeine as PubChem writes it. -/
def caffeine : String := "Cn1cnc2c1c(=O)n(C)c(=O)n2C"

/-! ### 1. The string becomes tokens

`tokenize` is the only place SMILES *syntax* lives: atoms (bare or bracketed),
bond symbols, ring-closure digits, branch parentheses, `.` for fragments.
Lowercase symbols are read as aromatic atoms.  A `Token` is a `TokenKind`
with its position in the string; shown here one token per entry. -/

/-- A token, in one word. -/
def Token.show (t : Token) : String :=
  match t.kind with
  | .atom a => a.toSmiles
  | .bond k => k.symbol
  | .dirBond d => s!"dir {repr d}"
  | .dot => "."
  | .branchOpen => "("
  | .branchClose => ")"
  | .ring k => s!"ring {k}"

#eval (tokenize caffeine).map fun ts ↦ ts.toList.map Token.show

/-! ### 2. Tokens become a `Molecule`

`parse` runs the tokens through a small state machine (open branches, pending
ring closures) and returns `Mol`, a molecule bundled with its atom count `n`.
Inside is `Molecule n`: a `Vector Atom n` and a `List (Bond n)`, where every
bond's endpoints are `Fin n`, so a bond cannot point at an atom that is not
there.  The `Repr` shows each atom as SMILES would write it alone, and each
bond as `src kind dst`. -/

#eval parse caffeine

/-- The parsed molecule, for the rest of the file.

`opaque`, not `def`: several `#eval`s below have a result type that mentions
`M.n` (`List (Bond M.n)`, `Matrix (Fin M.n) (Fin M.n) ℚ`), and to print such a
value the elaborator may unify its type and unfold `M` — running the whole
parse by kernel reduction, which does not terminate in practice for an
aromatic ring (design notes §8).  `opaque` keeps the value for the compiler
and hides it from the elaborator. -/
opaque M : Mol := Mol.ofSmiles! caffeine

#eval M.n            -- 14 atoms
#eval M.mol.numBonds -- 15 bonds: 14 atoms, 2 rings, 14 - 1 + 2

/-! ### 3. Atoms

An `Atom` records what the string said: element, aromatic flag, and the
bracket decorations (none here).  `parse` then fills `implicitH` by the
OpenSMILES default-valence rule; the written hydrogen count is `explicitH`,
and `totalH` is their sum. -/

#eval M.mol.atoms.toList

-- Hydrogens per atom, and the ten of C₈H₁₀N₄O₂.
#eval (List.finRange M.n).map fun i ↦ (M.mol.atom i).totalH
#eval ((List.finRange M.n).map fun i ↦ (M.mol.atom i).totalH).sum

/-! ### 4. Bonds and the molecular graph

Bonds are typed (`single`, `double`, `aromatic`, …) and carry a proof that
their endpoints differ, which is what lets `Molecule.graph` be a Mathlib
`SimpleGraph`.  Degrees here count heavy-atom neighbors; hydrogens are
counts on atoms, not vertices. -/

#eval M.mol.bonds

-- Each atom's heavy-atom neighbors, by index.
#eval (List.finRange M.n).map fun i ↦ (i.val, (M.mol.neighbors i).map (·.val))

-- The same degrees, from Mathlib's `SimpleGraph.degree` on `M.mol.graph`,
-- and the handshake lemma `Molecule.sum_degrees` checked numerically.
#eval (List.finRange M.n).map fun i ↦ M.mol.graph.degree i
#eval (∑ i, M.mol.graph.degree i, 2 * M.mol.numBonds)

-- Which atoms lie on a ring (nine of the fourteen).
#eval M.mol.inRingVector.toList

/-! ### 5. The adjacency matrix

`adjMatrix` is the bond-order-weighted adjacency matrix over `ℚ`: `1`, `2`,
`3`, or `3/2` for an aromatic bond, zero elsewhere, symmetric with zero
diagonal.  `toBondMatrix` is the same matrix as the subtype `BondMatrix n`,
whose type says it came from a molecule; `flatten` forgets the orders and
gives Mathlib's 0/1 `IsAdjMatrix`. -/

#eval M.mol.adjMatrix
#eval M.mol.toBondMatrix.flatten

-- The bond kind between atoms 5 and 6 (aromatic), 6 and 7 (the `=O`), 0 and 1.
#eval (List.finRange M.n).map fun i ↦ (List.finRange M.n).map fun j ↦
  (M.mol.toBondMatrix.kindAt i j).map BondKind.symbol

/-! ### 6. Normal form

A symmetric matrix cannot remember which end of a bond the string wrote
first, or the order of the bond list.  `normalize` forgets exactly that and
nothing else (`normalEquiv`), so a molecule in normal form *is* its atoms
plus its bond matrix.  The parsed molecule is not normal — ring closures are
stored from the closing atom back to the opening one. -/

#eval M.isNormal
#eval M.normalize.isNormal
#eval M.normalize.mol.bonds

/-! ### 7. Canonical ranks and the canonical SMILES

Canonicalization is a relabeling.  The search reads the molecule as atoms
plus bond matrix (`toMolData`).  Each atom gets an invariant (degree,
element, hydrogens, aromatic, charge, …); ranks are refined by neighbors'
ranks until nothing splits; ties are broken by trying every tied atom —
skipping those a verified symmetry shows redundant — and keeping the
lexicographically smallest string.  `canonicalPerm` is the
resulting permutation, `canonicalize` applies it, and the canonical SMILES is
the canonical molecule written in its new atom order. -/

-- The initial invariants, and how many classes refinement reaches.
#eval (List.finRange M.n).map M.mol.toMolData.atomInvariant
#eval numClasses M.mol.toMolData.initialRanks

-- Where each atom goes.
#eval let σ := M.mol.canonicalPerm; (List.finRange M.n).map fun i ↦ (i.val, (σ i).val)

#eval M.canonicalSmiles
#eval M.canonicalize.toSmiles == M.canonicalSmiles

-- Any other way of writing caffeine lands on the same string.
#eval (Mol.ofSmiles! "O=c1c2c(ncn2C)n(C)c(=O)n1C").canonicalSmiles == M.canonicalSmiles
#eval (M.relabel (finRotate M.n)).canonicalSmiles == M.canonicalSmiles

/-! ### 8. Morgan fingerprint

Circular environments of radius 0, 1, 2 around each atom, hashed as RDKit
does; `morganIds` lists the environment hashes with their counts, and
`morganBits` folds them into 2048 bit positions. -/

#eval M.morganIds
#eval M.morganBits

-- Caffeine against theobromine (one N-methyl fewer), as Tanimoto similarity.
#eval tanimoto M.morganBits (Mol.ofSmiles! "Cn1cnc2c1c(=O)[nH]c(=O)n2C").morganBits
