module

public import LeanSMILES.Polymorphic.Pipeline

/-!
# Integer certificates

Some guarantee conditions are about the training data: the perceptron's needs a
separator with a positive margin on every training molecule. For a bit representation
(`Representation.ofBits`, e.g. Morgan fingerprints) such a condition can be stated with
integers and checked by a `Bool` function. The kernel evaluates it (`decide +kernel`),
fingerprints included, so the check is a proof, without trusting compiled code.

`PerceptronWitness.check` is that function. `PerceptronWitness.certificate` in
`Proofs/Pipeline.lean` turns a passing check into a `PerceptronCertificate`, and so into
the guarantee that the trained perceptron classifies every training molecule correctly.
-/

@[expose] public section

namespace LeanSMILES

open Chem

namespace Check

variable {m n : Nat}

/-- `⟪z, (x, 1)⟫` for the `0/1` vector `x` of `bits`: the entries of `z` at the set bits,
plus the last entry (the bias). -/
def bitScore (z : Vector Int (n + 1)) (bits : Vector Bool n) : Int :=
  Fin.foldl n (fun acc j => acc + if bits[j] then z[j.castSucc] else 0) 0 + z[Fin.last n]

/-- `‖z‖²`. -/
def sqNorm {k : Nat} (z : Vector Int k) : Int := Fin.foldl k (fun acc j => acc + z[j] * z[j]) 0

/-- Number of set bits. -/
def popCount (bits : Vector Bool n) : Nat :=
  Fin.foldl n (fun acc j => acc + if bits[j] then 1 else 0) 0

end Check

/-- Integer data for a perceptron certificate on a bit representation with `n` bits. The
real separator is `separator / scale` and the real margin `margin / scale`. -/
structure PerceptronWitness (n : Nat) where
  /-- A separating parameter vector `(w, b)`, scaled by `scale`. -/
  separator : Vector Int (n + 1)
  scale : Nat
  /-- The margin, scaled by `scale`. -/
  margin : Int
  /-- At most this many bits are set in any training molecule. -/
  maxBits : Nat

namespace PerceptronWitness

variable {m n : Nat}

/-- Check a witness against the training molecules, their `±1` labels, and an epoch
budget:

* `‖separator‖ ≤ scale` (so the real separator has norm `≤ 1`) and `margin > 0`;
* every label is `±1`, every molecule has at most `maxBits` set bits, and
  `margin ≤ label · ⟪separator, (x, 1)⟫` for every molecule;
* `(maxBits + 1) · scale² ≤ epochs · margin²`, Novikoff's bound `(R/γ)² ≤ epochs`. -/
def check (w : PerceptronWitness n) (bits : Molecule → Vector Bool n)
    (molecules : Vector Molecule m) (labels : Vector Int m) (epochs : Nat) : Bool :=
  decide (0 < w.scale) && decide (0 < w.margin) &&
    decide (Check.sqNorm w.separator ≤ (w.scale : Int) ^ 2) &&
    (List.finRange m).all (fun i =>
      (labels[i] == 1 || labels[i] == -1) &&
        decide (Check.popCount (bits molecules[i]) ≤ w.maxBits) &&
        decide (w.margin ≤ labels[i] * Check.bitScore w.separator (bits molecules[i]))) &&
    decide (((w.maxBits + 1) * w.scale ^ 2 : Int) ≤ epochs * w.margin ^ 2)

end PerceptronWitness

end LeanSMILES

end
