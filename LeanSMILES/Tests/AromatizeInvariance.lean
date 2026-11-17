/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Aromaticity.Invariance
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Invariance test: the statements of `LeanSMILES.Aromaticity.Invariance`, as written

Each theorem of `LeanSMILES/Aromaticity/Invariance.lean` is checked on every
SMILES of the given files: its hypotheses decided by the instances there, its
conclusion as an equality of molecules.  A theorem whose hypotheses fail on an
input is not counted for it.  The theorems are unproved (`sorry`) for now, so
this test is the evidence that they are true; it stays useful afterwards as a
check that a refactoring of `aromatize` did not change what they are about.

Per string: five renumberings (a rotation, the reversal, three pseudo-random
permutations), five relistings of the bonds (reversed, every bond turned
round, three pseudo-random orders), and up to 64 Kekulé variants over the
bonds that come out aromatic, enumerated exhaustively.  The witness for
`exists_kekule_aromatize` is the Kekulé structure the pipeline itself computes
(`kekuleWitness`).

The lines tagged `[info]` count what happens *without* the hypotheses, which
is how the counterexamples in the module docstring of `Invariance.lean` show
up: they must not be zero failures for the hypotheses to be earning their keep.

```
lake exe invariance-test [files]            # default: datasets/aromatize-invariance.smi
lake exe invariance-test --dump [files]     # one line per string: input, aromatize's output
```

`--dump` writes `aromatize`'s output in stored atom order (`toSmiles`), for
comparing before and after a change to the pipeline.
-/

open LeanSMILES LeanSMILES.SMILES LeanSMILES.Aromaticity

namespace LeanSMILES.Tests.AromatizeInvariance

variable {n : ℕ}

/-- `aromatize`, with the error message dropped. -/
def arom (m : Molecule n) : Option (Molecule n) := m.aromatize.toOption

/-- `m` with the bond list `bs`, when no two of them join the same atoms. -/
def withBonds (m : Molecule n) (bs : List (Bond n)) : Option (Molecule n) :=
  if h : (bs.map Bond.edge).Nodup then some { m with bonds := bs, nodup := h } else none

/-- One step of a linear congruential generator. -/
def lcg (x : ℕ) : ℕ := (x * 1103515245 + 12345) % 2147483648

/-- A pseudo-random permutation of `Fin nn`: a product of `2 * nn` transpositions. -/
def randPerm (nn seed : ℕ) : Equiv.Perm (Fin nn) :=
  if h : 0 < nn then
    let rec go : ℕ → ℕ → Equiv.Perm (Fin nn) → Equiv.Perm (Fin nn)
      | 0, _, σ => σ
      | k + 1, x, σ =>
        let x₁ := lcg x
        let x₂ := lcg x₁
        go k x₂ (σ.trans (Equiv.swap ⟨(x₁ / 7) % nn, Nat.mod_lt _ h⟩ ⟨(x₂ / 7) % nn,
          Nat.mod_lt _ h⟩))
    go (2 * nn) (seed + nn) (Equiv.refl _)
  else Equiv.refl _

/-- A pseudo-random reordering of a list. -/
def randShuffle {α : Type} (l : List α) (seed : ℕ) : List α :=
  let rec go : ℕ → ℕ → List α → List α → List α
    | _, _, [], acc => acc
    | 0, _, r, acc => acc ++ r
    | fuel + 1, x, r, acc =>
      let x' := lcg x
      let i := (x' / 7) % r.length
      match r[i]? with
      | some y => go fuel x' (r.eraseIdx i) (y :: acc)
      | none => acc ++ r
  go l.length (seed + l.length) l []

/-- Every way to give each atom its `need` double bonds among the bonds `sb` (bond index and
the two atoms), as lists of the bond indices made double; at most `cap` of them.  `last[u]` is
the position in `sb` of the last bond at atom `u`: a bond may stay single only if neither of its
atoms is at its last chance. -/
partial def enumKekule (sb : Array (ℕ × ℕ × ℕ)) (last : Array ℕ) (cap p : ℕ) (need : Array ℕ)
    (chosen : List ℕ) (acc : Array (List ℕ)) : Array (List ℕ) :=
  if cap ≤ acc.size then acc else
  if h : p < sb.size then
    let (k, u, v) := sb[p]
    let acc :=
      if (last[u]! == p && 0 < need[u]!) || (last[v]! == p && 0 < need[v]!) then acc
      else enumKekule sb last cap (p + 1) need chosen acc
    if 0 < need[u]! && 0 < need[v]! then
      enumKekule sb last cap (p + 1) ((need.modify u (· - 1)).modify v (· - 1)) (k :: chosen) acc
    else acc
  else if need.all (· == 0) then acc.push chosen else acc

/-- The Kekulé variants of `m` over the bonds with indices `sIdx`: every placement of single and
double bonds there that gives each atom the number of double bonds it has in `m`; at most
`cap`, `m` itself among them. -/
def kekuleVariants (m : Molecule n) (sIdx : List ℕ) (cap : ℕ) : List (Molecule n) :=
  let bs : Array (ℕ × ℕ × Bool) :=
    m.bonds.toArray.map fun b ↦ (b.src.val, b.dst.val, b.kind == BondKind.double)
  let sb : Array (ℕ × ℕ × ℕ) := (sIdx.map fun k ↦ (k, bs[k]!.1, bs[k]!.2.1)).toArray
  let need := sb.foldl (init := Array.replicate n 0) fun a (k, u, v) ↦
    if bs[k]!.2.2 then (a.modify u (· + 1)).modify v (· + 1) else a
  let last := (List.range sb.size).foldl (init := Array.replicate n 0) fun a p ↦
    let (_, u, v) := sb[p]!
    (a.set! u p).set! v p
  (enumKekule sb last cap 0 need [] #[]).toList.filterMap fun chosen ↦
    withBonds m <| m.bonds.zipIdx.map fun (b, k) ↦
      if sIdx.contains k then { b with kind := if chosen.contains k then .double else .single }
      else b

/-- The Kekulé structure of the output `a` that the pipeline itself used for `m`: `a`'s atoms
with the aromatic flags cleared, and each aromatic bond of `a` with the kind `Work.kekulize`
gave it. -/
def kekuleWitness (m a : Molecule n) : Option (Molecule n) :=
  let w := (Work.ofMolecule m).freezeHs.cleanUp.cacheValences
  match w.kekulize w.relevantCycles with
  | .ok w' =>
    withBonds { a with atoms := a.atoms.map fun x ↦ { x with aromatic := false } } <|
      a.bonds.zipIdx.map fun (b, k) ↦
        if b.kind == BondKind.aromatic then
          { b with kind := (w'.bonds[k]?.map (·.kind)).getD b.kind }
        else b
  | .error _ => none

/-- Passed and checked, for one line of the report. -/
abbrev Count := ℕ × ℕ

/-- Count one check. -/
def Count.add (c : Count) (ok : Bool) : Count := (c.1 + (if ok then 1 else 0), c.2 + 1)

/-- The tallies of a run: one `Count` per theorem, then the checks made without hypotheses. -/
structure Tally where
  /-- Strings that parsed. -/
  parsed : ℕ := 0
  /-- Strings `aromatize` rejects. -/
  failed : ℕ := 0
  /-- `sameSkeleton_aromatize` and `stereo_aromatize`. -/
  skeleton : Count := (0, 0)
  /-- `IsKekule.exists_aromatize`. -/
  exists_ : Count := (0, 0)
  /-- `IsKekule.aromaticKept`. -/
  kekuleKept : Count := (0, 0)
  /-- `kind_aromatize`. -/
  kind : Count := (0, 0)
  /-- `aromatize_relabel`. -/
  relabel : Count := (0, 0)
  /-- `IsKekule.aromatize_relabel`. -/
  relabelKekule : Count := (0, 0)
  /-- `aromatize_of_sameBonds`. -/
  listing : Count := (0, 0)
  /-- Generated variants that satisfy `KekuleVariant` as written. -/
  variantHyp : Count := (0, 0)
  /-- `aromatize_of_kekuleVariant`. -/
  variant : Count := (0, 0)
  /-- `aromatize_aromatize`. -/
  idempotent : Count := (0, 0)
  /-- `exists_kekule_aromatize`, with `kekuleWitness`. -/
  witness : Count := (0, 0)
  /-- `canonicalSmiles_aromatize_eq`. -/
  canonical : Count := (0, 0)
  /-- Relabeling commutes, no hypothesis. -/
  relabelAny : Count := (0, 0)
  /-- The relabeled molecule aromatizes exactly when the molecule does. -/
  relabelSuccess : Count := (0, 0)
  /-- Relisting gives the same output up to `SameBonds`, no hypothesis. -/
  listingAny : Count := (0, 0)
  /-- Relisting gives the same canonical SMILES, no hypothesis. -/
  listingCanonical : Count := (0, 0)
  /-- The output aromatizes again. -/
  outputAromatizes : Count := (0, 0)
  /-- The first failures, as printed lines. -/
  misses : Array String := #[]

/-- Record a failed check of a theorem (at most 20 are kept). -/
def Tally.miss (t : Tally) (ok : Bool) (line : Unit → String) : Tally :=
  if ok || 20 ≤ t.misses.size then t else { t with misses := t.misses.push (line ()) }

/-- Run every check on one SMILES string. -/
def testOne (s : String) (t : Tally) : Tally := Id.run do
  let .ok M := parse s | return t
  let m := M.mol
  let nn := M.n
  let mut t := { t with parsed := t.parsed + 1 }
  let kek : Bool := decide m.IsKekule
  let perms : List (Equiv.Perm (Fin nn)) :=
    [finRotate nn, Fin.revPerm, randPerm nn 1, randPerm nn 2, randPerm nn 3]
  let lists := [m.bonds.reverse, m.bonds.map Bond.flip, randShuffle (m.bonds.map Bond.flip) 1,
    randShuffle m.bonds 2, randShuffle m.bonds 3]
  let some a := arom m
    | do
      t := { t with failed := t.failed + 1 }
      if kek then
        t := ({ t with exists_ := t.exists_.add false }).miss false
          fun _ ↦ s!"IsKekule.exists_aromatize: {s}"
      for σ in perms do
        t := { t with relabelSuccess := t.relabelSuccess.add (arom (m.relabel σ)).isNone }
      return t
  let chg : Bool := decide (m.ChargesKept a)
  let kept : Bool := decide (m.AromaticKept a)
  let okS := decide (m.SameSkeleton a) && decide (a.stereo = m.stereo)
  t := ({ t with skeleton := t.skeleton.add okS }).miss okS
    fun _ ↦ s!"sameSkeleton_aromatize: {s}"
  if kek then
    t := ({ t with exists_ := t.exists_.add true, kekuleKept := t.kekuleKept.add kept }).miss kept
      fun _ ↦ s!"IsKekule.aromaticKept: {s}"
  if kek && chg then
    let ok : Bool := decide (List.Forall₂ (fun (b b' : Bond nn) ↦
      b'.kind = BondKind.aromatic ∨ b'.kind = b.kind) m.bonds a.bonds)
    t := ({ t with kind := t.kind.add ok }).miss ok fun _ ↦ s!"kind_aromatize: {s}"
  -- the numbering of the atoms
  for σ in perms do
    let r := arom (m.relabel σ)
    let ok : Bool := decide (r = some (a.relabel σ))
    t := { t with relabelSuccess := t.relabelSuccess.add r.isSome,
                  relabelAny := t.relabelAny.add ok }
    if chg && kept && r.isSome then
      t := ({ t with relabel := t.relabel.add ok }).miss ok fun _ ↦ s!"aromatize_relabel: {s}"
    if chg && kek then
      t := ({ t with relabelKekule := t.relabelKekule.add ok }).miss ok
        fun _ ↦ s!"IsKekule.aromatize_relabel: {s}"
  -- the listing of the bonds
  for bs in lists do
    let some m' := withBonds m bs | continue
    let r := arom m'
    let ok := match r with
      | some a' => decide (a'.atoms = a.atoms) && decide (a'.stereo = a.stereo) &&
          decide (a'.SameBonds a)
      | none => false
    t := { t with listingAny := t.listingAny.add ok,
                  listingCanonical := t.listingCanonical.add
                    (r.map (·.canonicalSmiles) == some a.canonicalSmiles) }
    if chg && decide (m'.SameBonds m) then
      t := ({ t with listing := t.listing.add ok }).miss ok
        fun _ ↦ s!"aromatize_of_sameBonds: {s}"
  -- the output as an input
  match arom a with
  | some a' =>
    let ok : Bool := decide (a' = a)
    t := ({ t with idempotent := t.idempotent.add ok,
                   outputAromatizes := t.outputAromatizes.add true }).miss ok
      fun _ ↦ s!"aromatize_aromatize: {s}: {a.toSmiles} then {a'.toSmiles}"
  | none => t := { t with outputAromatizes := t.outputAromatizes.add false }
  let okW := match kekuleWitness m a with
    | some k => decide k.IsKekule && decide (k.IsKekuleStructureOf a) &&
        decide (arom k = some a)
    | none => false
  t := ({ t with witness := t.witness.add okW }).miss okW
    fun _ ↦ s!"exists_kekule_aromatize: {s}: {a.toSmiles}"
  -- the Kekulé structure
  let sIdx := (a.bonds.zipIdx.filter fun (b, _) ↦ b.kind == BondKind.aromatic).map (·.2)
  if kek && !sIdx.isEmpty then
    let mut j := 0
    for v in kekuleVariants m sIdx 64 do
      j := j + 1
      let hyp : Bool := decide (Molecule.KekuleVariant a m v)
      t := { t with variantHyp := t.variantHyp.add hyp }
      if !hyp then continue
      let ok : Bool := decide (arom v = some a)
      t := ({ t with variant := t.variant.add ok }).miss ok
        fun _ ↦ s!"aromatize_of_kekuleVariant: {s}: {v.toSmiles}"
      -- another Kekulé structure, renumbered and relisted: one canonical SMILES
      if chg && j ≤ 3 then
        let v' := v.relabel (randPerm nn (10 + j))
        let some m₂ := withBonds v' (randShuffle (v'.bonds.map Bond.flip) (20 + j)) | continue
        if decide (m₂.SameBonds v') then
          let ok := (arom m₂).map (·.canonicalSmiles) == some a.canonicalSmiles
          t := ({ t with canonical := t.canonical.add ok }).miss ok
            fun _ ↦ s!"canonicalSmiles_aromatize_eq: {s}: {v.toSmiles}"
  return t

/-- The SMILES of a file: the first field of each line that is neither blank nor a `#` comment. -/
def readSmiles (path : String) : IO (List String) := do
  let lines ← IO.FS.lines path
  return lines.toList.filterMap fun l ↦
    match (l.splitOn "\t").headD "" |>.trimAscii.toString with
    | "" => none
    | s => if s.startsWith "#" then none else some s

/-- One line of the report for a theorem: every check must pass. -/
def must (label : String) (c : Count) : String := s!"{label}: {c.1}/{c.2}  [must be all]"

/-- One line of the report for a check made without the hypotheses. -/
def info (label : String) (c : Count) : String := s!"{label}: {c.1}/{c.2}  [info]"

/-- Print the report; `true` when every check of every theorem passed. -/
def report (t : Tally) : IO Bool := do
  IO.println s!"{t.parsed} strings parsed, aromatize rejects {t.failed}"
  let theorems : List (String × Count) := [
    ("sameSkeleton_aromatize, stereo_aromatize", t.skeleton),
    ("IsKekule.exists_aromatize", t.exists_),
    ("IsKekule.aromaticKept", t.kekuleKept),
    ("kind_aromatize", t.kind),
    ("aromatize_relabel", t.relabel),
    ("IsKekule.aromatize_relabel", t.relabelKekule),
    ("aromatize_of_sameBonds", t.listing),
    ("aromatize_of_kekuleVariant", t.variant),
    ("aromatize_aromatize", t.idempotent),
    ("exists_kekule_aromatize (the pipeline's Kekulé structure as witness)", t.witness),
    ("canonicalSmiles_aromatize_eq", t.canonical)]
  for (label, c) in theorems do IO.println (must label c)
  IO.println (must "generated variants are `KekuleVariant`s as written" t.variantHyp)
  IO.println (info "without hypotheses: relabeling commutes" t.relabelAny)
  IO.println (info "without hypotheses: relabeled molecule aromatizes iff the molecule does"
    t.relabelSuccess)
  IO.println (info "without hypotheses: relisting gives the same output up to SameBonds"
    t.listingAny)
  IO.println (info "without hypotheses: relisting gives the same canonical SMILES"
    t.listingCanonical)
  IO.println (info "without hypotheses: the output aromatizes again" t.outputAromatizes)
  for l in t.misses do IO.println s!"  FAILED {l}"
  return theorems.all (fun p ↦ p.2.1 == p.2.2) && t.variantHyp.1 == t.variantHyp.2

end LeanSMILES.Tests.AromatizeInvariance

open LeanSMILES.Tests.AromatizeInvariance in
/-- Entry point of `lake exe invariance-test`: checks the statements of
`LeanSMILES.Aromaticity.Invariance` on the SMILES of the given files (by default
`datasets/aromatize-invariance.smi`) and exits with 1 if any fails; with `--dump`, prints each
string with `aromatize`'s output instead. -/
public def main (args : List String) : IO UInt32 := do
  let dump := args.contains "--dump"
  let files := args.filter (· != "--dump")
  let files := if files.isEmpty then ["datasets/aromatize-invariance.smi"] else files
  let mut t : Tally := {}
  for path in files do
    for s in ← readSmiles path do
      if dump then
        let out := match parse s with
          | .ok M => match M.mol.aromatize with
            | .ok a => a.toSmiles
            | .error e => s!"ERROR {e}"
          | .error e => s!"PARSE ERROR {e}"
        IO.println s!"{s}\t{out}"
      else t := testOne s t
  if dump then return 0
  return if ← report t then 0 else 1
