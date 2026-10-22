module

public import LeanSMILES.Polymorphic.Chem.SMILES
public import LeanSMILES.Polymorphic.LinAlg

/-!
# Molecules — Morgan fingerprints

ECFP-style fingerprints: iterated hashing of atom environments, then folding the
identifiers into `nBits` bits. Hashing is plain `Nat` arithmetic (FNV-1a), so fingerprints
compute in the kernel and unfold in proofs.
-/

@[expose] public section

namespace Chem

/-! ## Morgan fingerprints -/

/-- 32-bit FNV-1a over a list of naturals: plain `Nat` arithmetic, so it computes in the
kernel and unfolds in proofs. -/
def fnv (xs : List Nat) : Nat :=
  xs.foldl (fun h x => ((h ^^^ x) * 16777619) % 4294967296) 2166136261

/-- Radius-0 identifier of atom `i` (the ECFP atom invariants): element, degree, total
hydrogens, charge, isotope and ring membership. -/
def Molecule.morganInvariant (m : Molecule) (i : Nat) : Nat :=
  let a := m.atom i
  fnv [a.element, m.degree i, m.totalH i, (a.charge + 1000).toNat, a.isotope.getD 0,
    if m.atomInRing i then 1 else 0]

/-- One Morgan round: hash the round number, the atom's own identifier and the sorted
`(bond, neighbour identifier)` pairs. -/
def morganRound (adj : Array (List (Nat × BondOrder))) (round : Nat) (ids : Array Nat) :
    Array Nat :=
  ids.mapIdx fun i h =>
    fnv (round :: h :: (insertionSort lexLe
      ((adj.getD i []).map fun (u, b) => [b.code, ids.getD u 0])).flatten)

/-- Identifiers of rounds `round, …, round + k`, starting from `ids`. -/
def morganRounds (adj : Array (List (Nat × BondOrder))) : Nat → Nat → Array Nat → List Nat
  | 0, _, ids => ids.toList
  | k + 1, round, ids =>
    ids.toList ++ morganRounds adj k (round + 1) (morganRound adj (round + 1) ids)

/-- All environment identifiers of radius `0, …, radius`. -/
def Molecule.morganIds (m : Molecule) (radius : Nat) : List Nat :=
  morganRounds m.adjacency radius 0 ((Array.range m.atoms.size).map m.morganInvariant)

/-- Morgan fingerprint: bit `j` is set iff some identifier is `≡ j (mod nBits)`. -/
def Molecule.morganFingerprint (m : Molecule) (radius nBits : Nat) : MorganFingerprint nBits :=
  let ids := m.morganIds radius
  ⟨Vector.ofFn fun j => ids.any (· % nBits == j.val)⟩

/-- `bits` with bit `x % nBits` also set for every `x ∈ xs`. -/
def setBits {nBits : Nat} (bits : Vector Bool nBits) : List Nat → Vector Bool nBits
  | [] => bits
  | x :: xs => setBits (bits.setIfInBounds (x % nBits) true) xs

theorem getElem_setBits {nBits : Nat} (bits : Vector Bool nBits) (xs : List Nat) (j : Nat)
    (hj : j < nBits) : (setBits bits xs)[j] = (bits[j] || xs.any (· % nBits == j)) := by
  induction xs generalizing bits with
  | nil => simp [setBits]
  | cons x xs ih =>
    simp only [setBits, ih, Vector.getElem_setIfInBounds, List.any_cons]
    by_cases h : x % nBits = j
    · simp [h]
    · have hb : (x % nBits == j) = false := by simpa using h
      simp [h, hb]

/-- `morganFingerprint` in one pass over the identifiers, instead of one pass per bit.
The compiler uses it in place of `morganFingerprint` (`morganFingerprint_eq_fast`). -/
def Molecule.morganFingerprintFast (m : Molecule) (radius nBits : Nat) :
    MorganFingerprint nBits :=
  ⟨setBits (Vector.replicate nBits false) (m.morganIds radius)⟩

@[csimp] theorem Molecule.morganFingerprint_eq_fast :
    @Molecule.morganFingerprint = @Molecule.morganFingerprintFast := by
  funext m radius nBits
  simp only [Molecule.morganFingerprint, Molecule.morganFingerprintFast, MorganFingerprint.mk.injEq]
  ext j hj
  simp [getElem_setBits]

def SMILES.morganFingerprint (s : SMILES) (radius nBits : Nat) :
    Except String (MorganFingerprint nBits) :=
  (·.morganFingerprint radius nBits) <$> s.parse

/-- Number of set bits. -/
def MorganFingerprint.popCount {nBits : Nat} (fp : MorganFingerprint nBits) : Nat :=
  fp.bits.toList.count true

/-- Tanimoto similarity `|a ∧ b| / |a ∨ b|` (RDKit's `TanimotoSimilarity`); `1` for two
empty fingerprints. -/
def MorganFingerprint.tanimoto {α : Type} [Primitives.Scalar α] {nBits : Nat}
    (a b : MorganFingerprint nBits) : α :=
  let both := ((a.bits.zip b.bits).toList.filter fun x => x.1 && x.2).length
  let either := ((a.bits.zip b.bits).toList.filter fun x => x.1 || x.2).length
  if either = 0 then 1 else Primitives.Scalar.fromNat both / Primitives.Scalar.fromNat either

/-- Number of bits where the fingerprints differ. Over `ℝ` it is the squared Euclidean
distance between their feature vectors (`distSq_toFeatures` in
`Proofs/Chem/Fingerprint.lean`). -/
def MorganFingerprint.hammingDistance {nBits : Nat} (a b : MorganFingerprint nBits) : Nat :=
  Fin.foldl nBits (fun acc j => acc + if a.bits[j] = b.bits[j] then 0 else 1) 0

/-- The fingerprint as an ML feature vector (`1` for set bits, `0` otherwise). -/
def MorganFingerprint.toFeatures {α : Type} [Primitives.Scalar α] {nBits : Nat}
    (fp : MorganFingerprint nBits) : Primitives.Vec α nBits :=
  fp.bits.map fun b => if b then 1 else 0

end Chem

end
