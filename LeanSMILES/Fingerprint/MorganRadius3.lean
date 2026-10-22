/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Fingerprint.Morgan
-- The proofs make the kernel run the fingerprint, including `Array.ofFn`, `Array.map` and
-- `Fin.foldl`, whose bodies core does not expose; `import all` lets this file see them.
import all Init.Data.Array.Basic
import all Init.Data.Vector.Basic
import all Init.Data.Fin.Fold

/-!
# LeanSMILES.Fingerprint.MorganRadius3

At radius 3 the Morgan fingerprint can depend on the order of the atoms, so the
hypothesis `radius ≤ 2` of `Molecule.morganBits_relabel` cannot be dropped
(`Molecule.not_forall_morganBits_relabel_three`).

The witness is `C1=C(CO)C=C1CC`, a cyclobutadiene with an ethyl and a
hydroxymethyl group (`radius3Example`). Its two ring CH carbons, atoms 0 and 4,
cover the same bonds with the same identifier at radius 2, so duplicate removal
keeps the one with the smaller index and stops the other. They are not
symmetric: atom 0 is double-bonded to the carbon carrying CH₂OH, atom 4 to the
carbon carrying the ethyl group, so their radius-3 identifiers differ. Swapping
them (`Equiv.swap 0 4`) changes which one survives, and with it the
fingerprint (`morganBits_relabel_swap_ne`). RDKit 2026.09.1 does the same: over
all 8! atom orders it gives two different radius-3 fingerprints of this
molecule (README, "Findings about external tools").

The proofs are kernel computations (`decide +kernel`): no compiled code is
trusted.
-/

@[expose] public section

namespace LeanSMILES.Molecule

/-- `C1=C(CO)C=C1CC` as the parser reads it: atoms in SMILES order, with their
implicit hydrogens. Atoms 0 and 4 are the two ring CH carbons. -/
def radius3Example : Molecule 8 where
  atoms := ⟨#[{ element := some .C, implicitH := 1 },    -- 0  ring CH, = C(CH₂OH)
             { element := some .C },                     -- 1  ring C bearing CH₂OH
             { element := some .C, implicitH := 2 },     -- 2  CH₂
             { element := some .O, implicitH := 1 },     -- 3  OH
             { element := some .C, implicitH := 1 },     -- 4  ring CH, = C(ethyl)
             { element := some .C },                     -- 5  ring C bearing the ethyl group
             { element := some .C, implicitH := 2 },     -- 6  CH₂
             { element := some .C, implicitH := 3 }], rfl⟩  -- 7  CH₃
  bonds :=
    [{ src := 0, dst := 1, kind := .double, ne := by decide },
     { src := 1, dst := 2, ne := by decide },
     { src := 2, dst := 3, ne := by decide },
     { src := 1, dst := 4, ne := by decide },
     { src := 4, dst := 5, kind := .double, ne := by decide },
     { src := 0, dst := 5, ne := by decide },
     { src := 5, dst := 6, ne := by decide },
     { src := 6, dst := 7, ne := by decide }]
  nodup := by decide

/-- `radius3Example` is what the parser reads from `C1=C(CO)C=C1CC`: the same
atoms, and the same bonds in the same order. -/
theorem parse_radius3Example :
    (SMILES.parse "C1=C(CO)C=C1CC").toOption.map
        (fun M ↦ (M.n, M.mol.atoms.toList, M.mol.bonds.map fun b ↦ (b.src.val, b.dst.val, b.kind)))
      = some (8, radius3Example.atoms.toList,
          radius3Example.bonds.map fun b ↦ (b.src.val, b.dst.val, b.kind)) := by
  decide +kernel

/-- Swapping the two ring CH carbons changes the radius-3 fingerprint. -/
theorem morganBits_relabel_swap_ne :
    (radius3Example.relabel (Equiv.swap 0 4)).morganBits 3 ≠ radius3Example.morganBits 3 := by
  decide +kernel

/-- The same swap leaves the radius-2 fingerprint alone, as `morganBits_relabel` says. -/
theorem morganBits_relabel_swap_two :
    (radius3Example.relabel (Equiv.swap 0 4)).morganBits 2 = radius3Example.morganBits 2 := by
  decide +kernel

/-- **The radius bound of `morganBits_relabel` is sharp**: at radius 3 the Morgan
fingerprint is not invariant under relabeling of the atoms. -/
theorem not_forall_morganBits_relabel_three :
    ¬ ∀ (n : ℕ) (m : Molecule n) (σ : Equiv.Perm (Fin n)),
      (m.relabel σ).morganBits 3 = m.morganBits 3 :=
  fun h ↦ morganBits_relabel_swap_ne (h _ _ _)

end LeanSMILES.Molecule
