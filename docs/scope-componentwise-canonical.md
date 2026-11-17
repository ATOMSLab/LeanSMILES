# Scope: canonicalize each connected component on its own

Status: proposal, 2026-11-16. Nothing here is implemented.

## The problem, measured

Worker built 2026-10-28 (pruning from `4bff8ea` is in it), time per molecule after
subtracting process start. Raw output: `docs/cas-probe/fragment_scaling.out`.

| Identical fragments | 2 | 4 | 8 | 12 | 20 | 60 |
|---|---|---|---|---|---|---|
| cubane | 0.17 s | 1.2 s | 23 s | | | |
| benzene | 0.04 s | 0.35 s | 6.9 s | | | |
| neopentane | 0.03 s | 0.16 s | 3.1 s | 20 s | > 120 s | |
| water | | | | | 0.5 s | 111 s |

For comparison, one cubane takes 0.06 s, so eight of them canonicalized separately would
take about 0.5 s instead of 23 s. InChI takes 0.6 ms on the same inputs.

Everyday records are fine today: copper sulfate pentahydrate 0.03 s, alum with twelve
waters 0.30 s, a 3:2 salt 0.15 s. The cliff is at roughly eight identical multi-atom
fragments or forty identical single atoms: large hydrates and solvates, ionic clusters,
mixtures, reaction SMILES. **This is a real limit but not an urgent one**; the stereo gaps
in `docs/cas-probe/README.md` matter more.

## Why it is slow

`search` (`Canon.lean:276`) prunes among the atoms of one tied class: each tied atom costs
a walk to its first leaf (`firstLeaf`), then an automorphism check against siblings already
explored. With `k` identical fragments the lowest tied class holds an atom from every
fragment, at every one of about `k × depth` levels, and each first-leaf walk is itself
`k × depth` refinements over all `n` atoms. Cost grows about as `k⁴`–`k⁵`, which matches
the table. Nothing learned in one fragment is reused in the next.

## The change

```lean
/-- The connected components, each as its own bundled molecule, atoms in stored order. -/
def Molecule.components (m : Molecule n) : List Mol

/-- Today's whole-molecule search, renamed. Unchanged, theorem and all. -/
def Molecule.canonicalSmilesConnected (m : Molecule n) : String

/-- New: each component's canonical string, sorted, joined by `.`. -/
def Molecule.canonicalSmiles (m : Molecule n) : String :=
  ".".intercalate ((m.components.map (·.mol.canonicalSmilesConnected)).mergeSort (· ≤ ·))
```

- **Connected molecules get exactly today's string.** All 1 128 Delaney rows are
  single-component, so that oracle does not move.
- **Multi-component strings change**: components are ordered by string, not by their
  lowest-ranked atom. Rows affected in `datasets/`: 7 in `egfr-classification.csv`, 44 in
  `ThermoPropertiesSMILES.csv`, 21 in `stereo.smi`, 1 in `hydrogen-cases.csv`. RDKit also
  sorts fragment strings, so this moves toward its convention.
- **A law users expect becomes true**: `canonical(A.B)` is the sorted pair
  `canonical(A)`, `canonical(B)`. Stripping a counterion is then a string split.

## What has to be proved

Goal, same statement as today: `(m.relabel σ).canonicalSmiles = m.canonicalSmiles`.

| Step | What | Reuses | Rough size |
|---|---|---|---|
| 1 | Executable component labels (propagate the minimum index for `n` rounds) and proof that two atoms share a label iff `m.graph.Reachable` | `Molecule.graph` | 150 lines |
| 2 | `Molecule.induce`: the sub-molecule on a sorted list of atoms, with lemmas for its atoms and bonds | | 80 lines |
| 3 | Canonical string is invariant under any isomorphism of bundled molecules, not only a relabeling within one `Fin n` | `canonicalSmiles_relabel`, after `subst` on the sizes | 40 lines |
| 4 | Components of `m.relabel σ` are the images of the components of `m`; so the two lists of component strings are a permutation of each other | `relabelIso` (`Graph.lean:279`), Mathlib's `Reachable` under graph isomorphism, step 3 | 120 lines |
| 5 | Sorting a permuted list gives the same list; main theorem; `Mol` wrappers | `List.Perm` lemmas already used in `Canonicity.lean` | 40 lines |

About 400–450 lines, against 621 in `Canonicity.lean`. Step 4 is the fiddly one: the
component sizes are equal only propositionally, which is why step 3 is stated for bundled
`Mol` and why the components are bundled.

`Pipelines` needs no change: it uses only the string and `Mol.canonicalSmiles_relabel`
(`Pipelines/Proofs/Representation.lean:92`).

## The one theorem that gets weaker

`toSmiles_canonicalize : m.canonicalize.toSmiles = m.canonicalSmiles` ties the string to a
relabeling of the whole molecule. `canonicalize`, `canonicalRanks` and `canonicalPerm` can
still be built (rank = component's place in the sorted order, then the atom's rank inside
it), and every isomorphism fact about them survives because those hold for any
permutation. But equating the writer's output on that block ranking with the sorted join
is a lemma about `dfs` and `emit` (`Write.lean`): the walk never leaves a component, and no
ring digit is open between components. Two ways to handle it:

1. **First pass:** prove it for connected molecules only (follows from step 3) and keep
   the general case as a tested property. `Tests/Oracle.lean:123` already checks it; add
   multi-component rows.
2. **Later:** prove the writer lemma. Perhaps 200–300 lines, and worth doing only together
   with the stereo work, which has to reason about the writer's walk anyway.

## Why not a pure speed-up that keeps today's strings

That would need "the smallest whole-molecule string is the join of the smallest component
strings". I do not see how to prove it and suspect it is false: today's component order
follows the lowest-ranked atom rather than the strings, and `(`, `%`, `#`, `+`, `-` all
sort before `.`, so a longer component string can beat a shorter one once the separator
is appended.

## What this does not fix

- **One big symmetric component**: C60 5 s, a 30-prism 7 s. That needs what InChI's
  `CanonGraph` does (McKay 1981): keep the orbits found so far for the whole tree and
  branch on one atom per orbit, instead of one first-leaf walk per tied sibling.
- **Size alone**: a C100 alkane takes 3.2 s (C50 0.9 s). Refinement is quadratic or worse.
- **Stereo**, which is wrong today regardless of speed.

## Tests to add

- `k` copies of a fragment, for the fragments and `k` in the table above, with a time
  budget.
- Relabeling invariance on multi-component rows (the 73 rows listed above), as
  `Tests/Oracle.lean:117` does for Delaney.
- `canonical(A.B) = canonical(B.A)` and the sorted-pair law on random pairs of rows.
- Connected rows: new string equals old string, all of Delaney.

## Suggested order

Stereo first. Then this, as steps 1–5 with option 1 for the weakened theorem. Then orbit
accumulation for single components.
