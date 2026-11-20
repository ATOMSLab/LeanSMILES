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
input is not counted for it.  The theorems are proved; the test is a check that
a refactoring of `aromatize` did not change what they are about, and the
evidence for the one conjecture left (idempotence with hypotheses on the output
only).  The Kekulé statement without
`ChargesKept` is false (`O=P1[SiH]=CC=CC=1`), so it is counted for information only
and `aromatize_of_kekuleVariant_of_chargesKept` is checked.

Per string: five renumberings (a rotation, the reversal, three pseudo-random
permutations), five relistings of the bonds (reversed, every bond turned
round, three pseudo-random orders), and up to 64 Kekulé variants over the
bonds that come out aromatic, enumerated exhaustively.  The witness for
`exists_kekule_aromatize` is the Kekulé structure the pipeline itself computes
(`kekuleWitness`).

The lines tagged `[info]` count what happens *without* the hypotheses, which
is how the counterexamples in the module docstring of `Invariance.lean` show
up: they must not be zero failures for the hypotheses to be earning their keep.

For `aromatize_eq_self_of_isKekuleSpellingOf` the spelling is that same
structure, and `aromatize_aromatize` is checked on the input and its output.
Idempotence with hypotheses on the output only (`ChargesKept`, `ValenceOk`) is a
conjecture, counted for information, and the `[info]` lines under it count which
of `aromatize_aromatize`'s hypotheses the inputs under those two satisfy.

For `aromatize_of_isKekuleSpellingOf`, three Kekulé spellings are built from
each input on the Kekulé structure the pipeline computes for it — the atoms as
written, in bracket normal form, and with every hydrogen in brackets — with
up to eight Kekulé variants of each (`spellings`).  A file whose lines have two
tab-separated SMILES is read as matched pairs, a molecule and a Kekulé string
of it in the same atom order: the second is parsed on its own and read onto
the bond list of the first (`alignOnto`), which is the theorem's situation for
two strings a user wrote.

```
lake exe invariance-test [files]            # default: datasets/aromatize-invariance.smi
                                            #          and datasets/aromatize-pairs.tsv
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

/-- Kekulé spellings of `m` to try, built on the Kekulé structure the pipeline computes for it
(each bond written aromatic given the kind `Work.kekulize` gave it): the atoms as written with
the aromatic flags cleared, the same in bracket normal form, and the same with every hydrogen
written in brackets; then up to eight Kekulé variants of each over the bonds written aromatic.
Whether each is an `IsKekuleSpellingOf m` is for the caller to decide. -/
def spellings (m : Molecule n) : List (Molecule n) :=
  let w := (Work.ofMolecule m).freezeHs.cleanUp.cacheValences
  match w.kekulize w.relevantCycles with
  | .error _ => []
  | .ok w' =>
    let k? := withBonds { m with atoms := m.atoms.map fun x ↦ { x with aromatic := false } } <|
      m.bonds.zipIdx.map fun (b, i) ↦
        if b.kind == BondKind.aromatic then
          { b with kind := (w'.bonds[i]?.map (·.kind)).getD b.kind }
        else b
    match k? with
    | none => []
    | some k₀ =>
      let sIdx := (m.bonds.zipIdx.filter fun (b, _) ↦ b.kind == BondKind.aromatic).map (·.2)
      let bracketed : Molecule n :=
        { k₀ with atoms := k₀.atoms.map fun x ↦
            if x.totalH == 0 then x else { x with explicitH := some x.totalH, implicitH := 0 } }
      [k₀, k₀.normalizeBrackets, bracketed].flatMap fun k ↦
        if sIdx.isEmpty then [k] else kekuleVariants k sIdx 8

/-- The molecule `kk` read onto the bond list of `ml`: `kk`'s atoms and configurations, `ml`'s
bonds in `ml`'s order and orientation, each with the kind `kk` gives that pair of atoms. -/
def alignOnto (ml kk : Molecule n) : Option (Molecule n) :=
  withBonds { ml with atoms := kk.atoms, stereo := kk.stereo } <| ml.bonds.map fun b ↦
    match kk.bondBetween b.src b.dst with
    | some c => { b with kind := c.kind }
    | none => b

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
  /-- `aromatize_of_kekuleVariant_of_chargesKept`. -/
  variant : Count := (0, 0)
  /-- The Kekulé statement without `ChargesKept`: false
  (`O=P1[SiH]=CC=CC=1`), so counted for information only. -/
  variantAny : Count := (0, 0)
  /-- Idempotence with hypotheses on the output only (`ChargesKept`, `ValenceOk`): a conjecture,
  not proved. -/
  idempotent : Count := (0, 0)
  /-- Idempotence without `ChargesKept` for the second run: false
  (`O=p1ccccc1`), so counted for information only. -/
  idempotentAny : Count := (0, 0)
  /-- `exists_kekule_aromatize`, with `kekuleWitness`. -/
  witness : Count := (0, 0)
  /-- `aromatize_eq_self_of_isKekuleSpellingOf`, with `kekuleWitness` as the spelling. -/
  fixedPoint : Count := (0, 0)
  /-- `aromatize_aromatize`. -/
  idempotentRounds : Count := (0, 0)
  /-- Inputs under the conjecture's hypotheses that are under those of `aromatize_aromatize`. -/
  idempotentCover : Count := (0, 0)
  /-- Among the inputs under the conjecture's hypotheses, those with `AromaticWritten`,
  `RoundsToKekule` and `BareWritable` for the input. -/
  coverInput : Count := (0, 0)
  /-- Among them, those whose output has the input's valences (`SameValences`). -/
  coverValences : Count := (0, 0)
  /-- Among them, those whose output is `AromaticWritten` and `RoundsToKekule`. -/
  coverOutput : Count := (0, 0)
  /-- Among them, those whose output is `BareWritable`. -/
  coverBare : Count := (0, 0)
  /-- Parsed molecules satisfy `BareWritable`, as every parsed molecule should. -/
  bareWritable : Count := (0, 0)
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
  /-- `aromatize_of_isKekuleSpellingOf`, on the spellings built from the input. -/
  spelling : Count := (0, 0)
  /-- `canonicalSmiles_aromatize_of_isKekuleSpellingOf`, on those spellings. -/
  spellingCanonical : Count := (0, 0)
  /-- Built spellings that are `IsKekuleSpellingOf` the input as written. -/
  spellingHyp : Count := (0, 0)
  /-- A spelling aromatizes to the input's output, no hypothesis beyond the relation. -/
  spellingAny : Count := (0, 0)
  /-- A spelling aromatizes to the input's output, with the charge and aromatic hypotheses but
  not `AromaticWritten`, `RoundsToKekule` and `BareWritable`. -/
  spellingOld : Count := (0, 0)
  /-- Inputs that aromatize, keeping their charges and aromatic bonds, and are
  `RoundsToKekule`. -/
  rounds : Count := (0, 0)
  /-- Matched pairs read. -/
  pairs : ℕ := 0
  /-- Matched pairs whose second string, read onto the first, is an `IsKekuleSpellingOf` it. -/
  pairHyp : Count := (0, 0)
  /-- `aromatize_of_isKekuleSpellingOf`, on matched pairs. -/
  pair : Count := (0, 0)
  /-- `canonicalSmiles_aromatize_of_isKekuleSpellingOf`, on matched pairs: the second string as
  parsed, against the first. -/
  pairCanonical : Count := (0, 0)
  /-- The two strings of a pair aromatize to one canonical SMILES, no hypothesis. -/
  pairCanonicalAny : Count := (0, 0)
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
  t := { t with bareWritable := t.bareWritable.add (decide m.BareWritable) }
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
  if chg && kept then t := { t with rounds := t.rounds.add (decide m.RoundsToKekule) }
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
    t := { t with idempotentAny := t.idempotentAny.add ok,
                  outputAromatizes := t.outputAromatizes.add true }
    -- the conjecture assumes the second run's `cleanUp` rewrote nothing (`O=p1ccccc1`)
    if decide (a.ChargesKept a') && decide a.ValenceOk then
      t := { t with idempotent := t.idempotent.add ok }
  | none => t := { t with outputAromatizes := t.outputAromatizes.add false }
  let okW := match kekuleWitness m a with
    | some k => decide k.IsKekule && decide (k.IsKekuleStructureOf a) &&
        match arom k with
        | some a' => !decide (k.ChargesKept a') ||
            !decide m.AromaticWritten || !decide m.BareWritable || !decide (m.SameValences k) ||
            decide (a' = a)
        | none => false
    | none => false
  t := ({ t with witness := t.witness.add okW }).miss okW
    fun _ ↦ s!"exists_kekule_aromatize: {s}: {a.toSmiles}"
  -- the output as a fixed point: of its own Kekulé structure, and under the hypotheses on the
  -- input and the output alone
  match arom a with
  | some a' =>
    let ok : Bool := decide (a' = a)
    let chg' := decide (a.ChargesKept a')
    let onIn := decide m.AromaticWritten && decide m.RoundsToKekule && decide m.BareWritable
    let vals := decide (m.SameValences a)
    let onOut := decide a.AromaticWritten && decide a.RoundsToKekule
    let bare := decide a.BareWritable
    let hyp := chg' && onIn && vals && onOut && bare
    if hyp then
      t := ({ t with idempotentRounds := t.idempotentRounds.add ok }).miss ok
        fun _ ↦ s!"aromatize_aromatize: {s}: {a.toSmiles} then {a'.toSmiles}"
    if chg' && decide a.ValenceOk then
      t := { t with idempotentCover := t.idempotentCover.add hyp,
                    coverInput := t.coverInput.add onIn,
                    coverValences := t.coverValences.add vals,
                    coverOutput := t.coverOutput.add onOut,
                    coverBare := t.coverBare.add bare }
    match kekuleWitness m a with
    | some k =>
      let wit := match arom k with
        | some a'' => decide (a'' = a) && decide (k.ChargesKept a'')
        | none => false
      if decide (k.IsKekuleSpellingOf a) && wit && chg' && onOut && bare &&
          decide k.BareWritable then
        t := ({ t with fixedPoint := t.fixedPoint.add ok }).miss ok
          fun _ ↦ s!"aromatize_eq_self_of_isKekuleSpellingOf: {s}: {a.toSmiles} then {a'.toSmiles}"
    | none => pure ()
  | none => pure ()
  -- a Kekulé spelling of the input
  let mut q := 0
  for k in spellings m do
    q := q + 1
    let hyp : Bool := decide (k.IsKekuleSpellingOf m)
    t := { t with spellingHyp := t.spellingHyp.add hyp }
    if !hyp then continue
    let some a' := arom k | continue
    let ok : Bool := decide (a' = a)
    t := { t with spellingAny := t.spellingAny.add ok }
    if !(chg && kept && decide (k.ChargesKept a')) then continue
    t := { t with spellingOld := t.spellingOld.add ok }
    if !(decide m.AromaticWritten && decide m.RoundsToKekule && decide m.BareWritable &&
        decide k.BareWritable) then continue
    t := ({ t with spelling := t.spelling.add ok }).miss ok
      fun _ ↦ s!"aromatize_of_isKekuleSpellingOf: {s}: {k.toSmiles}"
    if q % 4 == 1 then
      let k' := k.relabel (randPerm nn (30 + q))
      let some k₂ := withBonds k' (randShuffle (k'.bonds.map Bond.flip) (40 + q)) | continue
      if decide (k₂.SameBonds k') then
        let ok := (arom k₂).map (·.canonicalSmiles) == some a.canonicalSmiles
        t := ({ t with spellingCanonical := t.spellingCanonical.add ok }).miss ok
          fun _ ↦ s!"canonicalSmiles_aromatize_of_isKekuleSpellingOf: {s}: {k.toSmiles}"
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
      t := { t with variantAny := t.variantAny.add ok }
      if chg then
        t := ({ t with variant := t.variant.add ok }).miss ok
          fun _ ↦ s!"aromatize_of_kekuleVariant_of_chargesKept: {s}: {v.toSmiles}"
      -- another Kekulé structure, renumbered and relisted: one canonical SMILES
      if chg && j ≤ 3 then
        let v' := v.relabel (randPerm nn (10 + j))
        let some m₂ := withBonds v' (randShuffle (v'.bonds.map Bond.flip) (20 + j)) | continue
        if decide (m₂.SameBonds v') then
          let ok := (arom m₂).map (·.canonicalSmiles) == some a.canonicalSmiles
          t := ({ t with canonical := t.canonical.add ok }).miss ok
            fun _ ↦ s!"canonicalSmiles_aromatize_eq: {s}: {v.toSmiles}"
  return t

/-- Run the Kekulé-spelling checks on a matched pair: `sl` a molecule as written, `sk` a Kekulé
string of it in the same atom order. -/
def testPair (sl sk : String) (t : Tally) : Tally := Id.run do
  let (.ok Ml, .ok Mk) := (parse sl, parse sk) | return t
  let mut t := { t with pairs := t.pairs + 1 }
  if h : Mk.n = Ml.n then
    let m := Ml.mol
    let kk : Molecule Ml.n := h ▸ Mk.mol
    let some a := arom m | return t
    let okAny := (arom kk).map (·.canonicalSmiles) == some a.canonicalSmiles
    t := { t with pairCanonicalAny := t.pairCanonicalAny.add okAny }
    let some k := alignOnto m kk | return { t with pairHyp := t.pairHyp.add false }
    let hyp : Bool := decide (k.IsKekuleSpellingOf m)
    t := { t with pairHyp := t.pairHyp.add hyp }
    if !hyp then return t
    let some a' := arom k | return t
    if !(decide (m.ChargesKept a) && decide (m.AromaticKept a) && decide (k.ChargesKept a') &&
        decide m.AromaticWritten && decide m.RoundsToKekule && decide m.BareWritable &&
        decide k.BareWritable) then
      return t
    let ok : Bool := decide (a' = a)
    t := ({ t with pair := t.pair.add ok }).miss ok
      fun _ ↦ s!"aromatize_of_isKekuleSpellingOf: {sl} against {sk}"
    -- the second string as parsed is `k` with its bonds listed another way
    if decide (kk.atoms = k.atoms) && decide (kk.stereo = k.stereo) && decide (kk.SameBonds k) then
      t := ({ t with pairCanonical := t.pairCanonical.add okAny }).miss okAny
        fun _ ↦ s!"canonicalSmiles_aromatize_of_isKekuleSpellingOf: {sl} against {sk}"
    return t
  else return { t with pairHyp := t.pairHyp.add false }

/-- The SMILES of a file: the first field of each line that is neither blank nor a `#` comment. -/
def readSmiles (path : String) : IO (List String) := do
  let lines ← IO.FS.lines path
  return lines.toList.filterMap fun l ↦
    match (l.splitOn "\t").headD "" |>.trimAscii.toString with
    | "" => none
    | s => if s.startsWith "#" then none else some s

/-- The matched pairs of a file: the first two tab-separated fields of each line that has two
and is not a `#` comment. -/
def readPairs (path : String) : IO (List (String × String)) := do
  let lines ← IO.FS.lines path
  return lines.toList.filterMap fun l ↦
    if l.startsWith "#" then none else
    match l.splitOn "\t" with
    | a :: b :: _ =>
      let (a, b) := (a.trimAscii.toString, b.trimAscii.toString)
      if a.isEmpty || b.isEmpty then none else some (a, b)
    | _ => none

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
    ("aromatize_of_kekuleVariant_of_chargesKept", t.variant),
    ("exists_kekule_aromatize (the pipeline's Kekulé structure as witness)", t.witness),
    ("aromatize_eq_self_of_isKekuleSpellingOf (that structure as the spelling)", t.fixedPoint),
    ("aromatize_aromatize", t.idempotentRounds),
    ("parsed molecules are `BareWritable`", t.bareWritable),
    ("canonicalSmiles_aromatize_eq", t.canonical),
    ("aromatize_of_isKekuleSpellingOf (spellings built from the input)", t.spelling),
    ("canonicalSmiles_aromatize_of_isKekuleSpellingOf (built spellings)", t.spellingCanonical),
    ("aromatize_of_isKekuleSpellingOf (matched pairs)", t.pair),
    ("canonicalSmiles_aromatize_of_isKekuleSpellingOf (matched pairs)", t.pairCanonical)]
  for (label, c) in theorems do IO.println (must label c)
  IO.println (must "generated variants are `KekuleVariant`s as written" t.variantHyp)
  IO.println (info "built spellings that are `IsKekuleSpellingOf` the input as written"
    t.spellingHyp)
  IO.println (info s!"matched pairs ({t.pairs} read) that are `IsKekuleSpellingOf` as written"
    t.pairHyp)
  IO.println (info "without the charge and aromatic hypotheses: a spelling gives the same output"
    t.spellingAny)
  IO.println (info
    "without AromaticWritten, RoundsToKekule, BareWritable: a spelling gives the same output"
    t.spellingOld)
  IO.println (info "inputs keeping charges and aromatic bonds that are `RoundsToKekule`" t.rounds)
  IO.println (info "without hypotheses: the two strings of a pair give one canonical SMILES"
    t.pairCanonicalAny)
  IO.println (info "Kekule statement without ChargesKept (false)" t.variantAny)
  IO.println (info "without hypotheses: relabeling commutes" t.relabelAny)
  IO.println (info "without hypotheses: relabeled molecule aromatizes iff the molecule does"
    t.relabelSuccess)
  IO.println (info "without hypotheses: relisting gives the same output up to SameBonds"
    t.listingAny)
  IO.println (info "without hypotheses: relisting gives the same canonical SMILES"
    t.listingCanonical)
  IO.println (info "without hypotheses: the output aromatizes again" t.outputAromatizes)
  IO.println (info "idempotence without ChargesKept (false: O=p1ccccc1)" t.idempotentAny)
  IO.println (info
    "conjecture (not proved): idempotence with ChargesKept and ValenceOk for the output only"
    t.idempotent)
  IO.println (info "inputs under the conjecture's hypotheses under aromatize_aromatize's"
    t.idempotentCover)
  IO.println (info "  of those inputs: AromaticWritten, RoundsToKekule, BareWritable for the input"
    t.coverInput)
  IO.println (info "  of those inputs: the output has the input's valences" t.coverValences)
  IO.println (info "  of those inputs: the output is AromaticWritten and RoundsToKekule"
    t.coverOutput)
  IO.println (info "  of those inputs: the output is BareWritable" t.coverBare)
  for l in t.misses do IO.println s!"  FAILED {l}"
  return theorems.all (fun p ↦ p.2.1 == p.2.2) && t.variantHyp.1 == t.variantHyp.2

end LeanSMILES.Tests.AromatizeInvariance

open LeanSMILES.Tests.AromatizeInvariance in
/-- Entry point of `lake exe invariance-test`: checks the statements of
`LeanSMILES.Aromaticity.Invariance` on the SMILES of the given files (by default
`datasets/aromatize-invariance.smi` and the matched pairs of `datasets/aromatize-pairs.tsv`) and
exits with 1 if any fails; with `--dump`, prints each string with `aromatize`'s output instead. -/
public def main (args : List String) : IO UInt32 := do
  let dump := args.contains "--dump"
  let files := args.filter (· != "--dump")
  let files := if files.isEmpty then
      ["datasets/aromatize-invariance.smi", "datasets/aromatize-pairs.tsv"]
    else files
  let mut t : Tally := {}
  for path in files do
    let pairs ← readPairs path
    -- a file of matched pairs: the pair checks only
    if !dump && !pairs.isEmpty then
      for (sl, sk) in pairs do t := testPair sl sk t
      continue
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
