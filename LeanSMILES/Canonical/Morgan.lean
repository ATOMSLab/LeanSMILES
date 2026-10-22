import LeanSMILES.Canonical.Sanitize

/-!
# Morgan fingerprints (ECFP-like)

`Chem.morganBits "…"` gives the same on-bits as RDKit's
`rdFingerprintGenerator.GetMorganGenerator(radius=2, fpSize=2048).GetFingerprint(mol)`
(RDKit 2026.09.1), and `Mol.morganIds` the same unfolded identifiers as
`GetSparseCountFingerprint`. Ported from `docs/reference/morgan_ref.py`.

How it works (`Fingerprints/MorganGenerator.cpp`, `FingerprintUtil.cpp`):

1. **Radius 0.** Each atom gets a 32-bit number from its own properties: element,
   number of neighbours including H, H count, charge, isotope mass shift
   (`isotopeMassShift`, e.g. 1 for `[2H]`, 0 for `[13C]`), and whether it is in
   a ring.
2. **Each radius 1, 2, …** Each atom's number is re-hashed together with its
   sorted (bond type, neighbour's number) pairs, so it describes a bigger and
   bigger neighbourhood (an "environment").
3. **Duplicates.** If two atoms' environments cover exactly the same bonds, only
   one is kept; an environment already seen at a smaller radius is dropped, and
   its atom stops growing.
4. **Folding.** Each identifier `id` sets bit `id mod 2048`.

All arithmetic is unsigned 32-bit with wrap-around, exactly as in RDKit
(boost `hash_combine`, `RDGeneral/hash/hash.hpp:211-219`).
-/

namespace Chem

/-- boost's `hash_combine` on 32-bit values: `seed ^ (v + 0x9e3779b9 + (seed << 6) + (seed >> 2))`. -/
def hashCombine (seed v : UInt32) : UInt32 :=
  seed ^^^ (v + 0x9e3779b9 + (seed <<< (6 : UInt32)) + (seed >>> (2 : UInt32)))

/-- Hash of a list of values, starting from seed 0 (`hash_range`). -/
def hashList (vs : List UInt32) : UInt32 := vs.foldl hashCombine 0

/-- Hash of a pair (`hash_value(std::pair)`). -/
def hashPair (a b : UInt32) : UInt32 := hashCombine (hashCombine 0 a) b

/-- A signed integer as RDKit stores it in a `uint32` (negative numbers wrap). -/
def toUInt32 (i : Int) : UInt32 := (if i ≥ 0 then i.toNat else (4294967296 + i).toNat).toUInt32

namespace Mol

/-- Radius-0 identifier of atom `i` (`getConnectivityInvariants`,
`FingerprintUtil.cpp:240-263`). -/
def morganAtomInvariant (m : Mol) (i : Nat) : UInt32 :=
  let a := m.atoms[i]!
  -- H count includes hydrogens written as atoms, e.g. the [2H] neighbours in
  -- [2H]C([2H])([2H])[2H] (getTotalNumHs(includeNeighbors=true))
  let hs := m.totalHs i + ((m.neighbors i).filter fun (_, o) => m.atoms[o]!.atomicNum == 1).length
  let base := [a.atomicNum.toUInt32, (m.degree i + m.totalHs i).toUInt32,
               hs.toUInt32, toUInt32 a.charge,
               toUInt32 (isotopeMassShift a.atomicNum a.isotope)]
  hashList (if m.atomInRing i then base ++ [1] else base)

/-- All Morgan environments as (identifier, atom, radius), in RDKit's order
(`MorganGenerator.cpp:280-503`). Bond sets are bitmasks over bond indices. -/
def morganEnvironments (m : Mol) (radius : Nat := 2) : List (UInt32 × Nat × Nat) := Id.run do
  let n := m.numAtoms
  let mut cur : Array UInt32 := (List.range n).toArray.map m.morganAtomInvariant
  -- radius 0: every atom, always included
  let mut result : List (UInt32 × Nat × Nat) := (List.range n).map fun i => (cur[i]!, i, 0)
  let mut prevEnv : Array Nat := Array.replicate n 0    -- bonds covered, previous round
  let mut roundEnv : Array Nat := Array.replicate n 0   -- bonds covered, this round
  let mut seen : List Nat := []                         -- bond sets already emitted
  let mut dead := Array.replicate n false
  for layer in [0:radius] do
    let mut next : Array UInt32 := Array.replicate n 0  -- dead atoms contribute 0
    let mut thisRound : List (UInt32 × Nat × Nat) := []  -- (identifier, atom, bond set)
    for a in [0:n] do
      if dead[a]! then continue
      let nbrs := m.neighbors a
      if nbrs.isEmpty then
        dead := dead.set! a true
        continue
      -- environment grows by the atom's bonds and its neighbours' previous environments
      let mut env := roundEnv[a]!
      for (k, o) in nbrs do
        env := env ||| (1 <<< k) ||| prevEnv[o]!
      roundEnv := roundEnv.set! a env
      -- sorted (bond type, neighbour identifier) pairs, hashed onto (layer, own identifier)
      let pairs := (nbrs.map fun (k, o) => (m.bonds[k]!.order.rdkitType.toUInt32, cur[o]!)).mergeSort
        fun p q => p.1 < q.1 || (p.1 == q.1 && p.2 ≤ q.2)
      let h := pairs.foldl (fun h (t, v) => hashCombine h (hashPair t v))
        (hashCombine layer.toUInt32 cur[a]!)
      next := next.set! a h
      thisRound := thisRound ++ [(h, a, env)]
    -- keep one atom per new bond set: the smallest (identifier, atom)
    let sorted := thisRound.mergeSort fun p q => p.1 < q.1 || (p.1 == q.1 && p.2.1 ≤ q.2.1)
    for (h, a, env) in sorted do
      if seen.contains env then dead := dead.set! a true
      else
        result := result ++ [(h, a, layer + 1)]
        seen := env :: seen
    cur := next
    prevEnv := roundEnv
  return result

/-- Unfolded Morgan fingerprint: each distinct identifier with its count, sorted
by identifier (RDKit's `GetSparseCountFingerprint`). -/
def morganIds (m : Mol) (radius : Nat := 2) : List (UInt32 × Nat) :=
  let ids := (m.morganEnvironments radius).map (·.1)
  let sorted := ids.mergeSort (· ≤ ·)
  sorted.eraseDups.map fun id => (id, sorted.count id)

/-- Folded Morgan fingerprint: the sorted list of on-bits (RDKit's `GetFingerprint`). -/
def morganBits (m : Mol) (radius : Nat := 2) (fpSize : Nat := 2048) : List Nat :=
  ((m.morganIds radius).map fun (id, _) => id.toNat % fpSize).eraseDups.mergeSort (· ≤ ·)

/-- The fingerprint as a bit vector of length `fpSize` (for ML features). -/
def morganVector (m : Mol) (radius : Nat := 2) (fpSize : Nat := 2048) : Array Bool :=
  (m.morganBits radius fpSize).foldl (fun v b => v.set! b true) (Array.replicate fpSize false)

end Mol

/-- SMILES in, Morgan on-bits out (radius 2, 2048 bits by default). -/
def morganBits (s : String) (radius : Nat := 2) (fpSize : Nat := 2048) : Except String (List Nat) :=
  (molFromSmiles s).map (·.morganBits radius fpSize)

/-- Tanimoto similarity of two bit sets: shared bits / bits in either. -/
def tanimoto (a b : List Nat) : Float :=
  let common := (a.filter b.contains).length
  let union := a.length + b.length - common
  if union == 0 then 0 else common.toFloat / union.toFloat

end Chem
