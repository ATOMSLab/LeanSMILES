# Design notes: molecular representation in Lean

What a SMILES string becomes inside this library, why it has the shape it has,
and how it compares with the alternatives (RDKit, pysmiles, and the
`canonical-smiles` branch of this repository).

## 1. Three layers, not two

"Is RDKit storing a string or a graph?" has a three-part answer, and the
library is organized around it:

| Layer | What it is | Here |
|---|---|---|
| **String** | the syntax | `String`, from `CSVparser` |
| **Ordered labeled graph** | atoms numbered in order of appearance, bonds with kinds, decorations | `Molecule n` (`LeanSMILES/Chem/Molecule.lean`) |
| **Molecule up to relabeling** | what "same molecule?" means | `canonicalize` / `canonicalSmiles` (`LeanSMILES/SMILES/Canon.lean`) |

RDKit and pysmiles both parse into the middle layer and both have to work to
reach the third.  The ordered graph remembers the string in two places — the
atom numbering, and the neighbor order that `@`/`@@` and `/`/`\` refer to —
which is why `Molecule.relabel` exists as an explicit operation and why
stereo marks are *recorded* on atoms and bonds but not *interpreted*.

## 2. The typed representation

```lean
structure Molecule (n : ℕ) where
  atoms : Vector Atom n
  bonds : List (Bond n)
  nodup : (bonds.map Bond.edge).Nodup          -- no two bonds join the same pair

structure Bond (n : ℕ) where
  src dst : Fin n                              -- cannot dangle
  kind : BondKind                              -- single | double | triple | quadruple | aromatic
  dir : Option BondDir                         -- `/` `\`, recorded
  ne : src ≠ dst                               -- no self-bond
```

Design choices, and the reason for each:

* **Size in the type.** `Fin n` is the atom type, so `Molecule.graph : SimpleGraph (Fin n)`
  gets `Fintype`, decidable adjacency and all of Mathlib's finite-graph
  lemmas for free, and a relabeling is an `Equiv.Perm (Fin n)`.  `Vector Atom n`
  rather than `Array Atom` because `Vector.ofFn` keeps the size *definitional*,
  which is what lets `relabel` be written without casts.
* **Invariants are the type.** RDKit checks "endpoint in range", "no self-bond"
  and "no duplicate bond" at run time; here they are the fields `src dst : Fin n`,
  `ne`, and `nodup`.  The parser discharges them *by decision* once
  (`State.toMolecule`), and nothing downstream re-checks.  `nodup` is exactly
  what makes "molecule = simple graph with labels" true, so Mathlib's
  `edgeFinset.card` counts the bonds (`card_edgeFinset`).
* **Bonds as a `List`, not an `Array`.**  Membership, `map`, `Nodup` and
  decidability all have the lemmas for lists; the parser uses arrays
  internally and converts once.
* **`BondKind` is the data, `ℚ` is a view.**  `BondKind.order : BondKind → ℚ`
  puts the aromatic bond at `3/2`.  Featurization one-hots the kind, matrices
  sum the order, and no `Float` appears anywhere (`LeanLearn/Scalar.lean` is for the ML
  side).  There is no zero-order kind: the SMILES dot is the *absence* of a
  bond, and a salt is a disconnected graph.
* **`Element` is a 118-constructor enumeration** in atomic-number order, so
  `atomicNumber` is the constructor index and `Fintype.card Element = 118` is
  `decide`.  The wildcard `*` is `Atom.element = none`, not an element, so
  theorems about `Element` are about real elements.
* **Two hydrogen counts**, as in RDKit: `explicitH` (written in brackets) and
  `implicitH` (inferred).  A bracket atom is "an atom whose `explicitH` is
  `some _`", and the writer brackets exactly those again, so what you wrote is
  what you get back.

## 3. The Mathlib views (`LeanSMILES/Chem/Graph.lean`)

| Definition / theorem | Statement |
|---|---|
| `graph : SimpleGraph (Fin n)` | adjacent ⇔ some bond joins them; `DecidableRel` |
| `adjMatrix : Matrix (Fin n) (Fin n) ℚ` | bond-order weighted; `isSymm_adjMatrix`, `adjMatrix_apply_self` |
| `adjMatrix_ne_zero_iff` | weighted entry nonzero ⇔ `graph.Adj` |
| `graph_adjMatrix_eq` | Mathlib's 0/1 `adjMatrix` is the indicator of the weighted one |
| `edgeFinset_eq`, `card_edgeFinset` | Mathlib's edge set is the bond list; its size is `numBonds` |
| `sum_degrees` | handshake lemma: `∑ degree = 2 * numBonds` |
| `relabelIso σ` | `graph ≃g (relabel σ).graph` |
| `canonicalizeIso` | canonicalization is a graph isomorphism |

Both views are *derived* from the bond list, so the theorems above say the
two derivations agree.  The matrix → graph direction closes the loop:

| Definition / theorem | Statement |
|---|---|
| `BondKind.ofOrder?`, `order_injective` | `ofOrder? k.order = some k`; an order determines the kind |
| `bondBetween_eq_some_iff` | by `nodup`, the bond found on an edge is *the* bond there |
| `adjMatrix_eq_order_iff` | `adjMatrix i j = k.order ↔ ∃ b ∈ bonds, b.edge = s(i,j) ∧ b.kind = k` |
| `toGraph_adjMatrix` | Mathlib's 0/1 round trip, instantiated at `graph` |
| `graphOfMatrix`, `graphOfMatrix_adjMatrix` | the graph of the nonzero entries; `graphOfMatrix adjMatrix = graph` |
| `IsBondMatrix` | symmetric, zero diagonal, nonzero entries are bond orders; `isBondMatrix_adjMatrix` |
| `ofAdjMatrix atoms A : Molecule n` | total decoder: one bond per pair `i < j` whose entry is a bond order |
| `adjMatrix_ofAdjMatrix` | `IsBondMatrix A → (ofAdjMatrix atoms A).adjMatrix = A` |
| `graph_ofAdjMatrix_adjMatrix`, `bondKind_ofAdjMatrix_adjMatrix` | molecule → matrix → molecule keeps the graph and every bond kind |

What no symmetric matrix can carry is the `src → dst` orientation of a bond,
and with it the `/` `\` marks: `ofAdjMatrix` recovers everything but `Bond.dir`.

**Matrices as subtypes** (`LeanSMILES/Chem/BondMatrix.lean`).  Going beyond
RDKit where Lean's type system makes it cheap: "this matrix comes from a
molecule" is in the type.

| Definition / theorem | Statement |
|---|---|
| `BondMatrix n := {A // IsBondMatrix A}` | the weighted matrix; `B i j`, `B.kindAt i j`, `B.graph`, `B.toMolecule atoms` |
| `BondMatrix.check`, `check_iff`, `ofMatrix?` | `IsBondMatrix` is decidable; any matrix can be checked into the subtype at run time |
| `FlatMatrix n := {A // A.IsAdjMatrix}` | the 0/1 matrix, Mathlib's predicate; `F.graph` by `IsAdjMatrix.toGraph` |
| `BondMatrix.flatten`, `graph_flatten` | forget the orders; the graph is unchanged |
| `Molecule.toBondMatrix` | backed by the materialized `adjTable`, so `B i j` is O(1); `val_toBondMatrix : B.1 = adjMatrix` |
| `Molecule.toFlatMatrix`, `flatten_toBondMatrix` | the graph's own 0/1 matrix; flattening the bond matrix gives it |
| `normalize`, `IsNormal` | forget bond orientation and bond-list order; a fixed point of `normalize` (decidable) |
| `IsNormal.bond_spec` | in normal form every bond runs `src < dst` with no direction mark |
| `normalEquiv` | **`{m // m.IsNormal} ≃ Vector Atom n × BondMatrix n`** — nothing is lost |

The `Equiv` is the honest form of "the matrix stores everything": it does, for
molecules that have forgotten what a symmetric matrix cannot hold.  For Morgan
fingerprints and functional-group matching that is exactly the right
information — neither looks at `/` `\` marks or at the order bonds were written.

## 4. Parsing (`LeanSMILES/SMILES/Token.lean`, `Parse.lean`)

Tokenizer: bracket atoms are decoded into one `Atom` token (isotope, symbol
with greedy two-letter matching, `@`/`@@`, `H` count, charge, class);
bare atoms are the OpenSMILES organic subset; everything else is a bond
symbol, `.`, `(`, `)`, or a ring label (`1`–`9`, `%nn`).

Parser: the same state machine as RDKit and pysmiles — anchor, pending bond,
branch stack, open rings, after-dot flag — so atom indices are string order.
Syntax rules adopted from RDKit (confirmed by its fuzzing oracle, see §7):
no bond symbol at the start, end, before `(` `)` `.`, or twice in a row; no
empty branch `()`; no ring digit right after `(`; no leading, trailing or
double `.`; no self-bond or duplicate bond via ring closures; `/` `\` leave the
bond kind implicit (aromatic between aromatic atoms).  Conflicting bond
symbols at the two ends of a ring closure are an error (OpenSMILES), where
RDKit lets the opening end win.

**Not checked: valence.**  This is deliberate.  `parse` adds the one rule
SMILES itself specifies — implicit hydrogens on bare organic-subset atoms from
the default valences — and nothing else: no aromaticity perception, no
kekulization, no charge-separation rewrites, no strict valence check.  Those
are a chemistry model, not syntax, and they need human choices.

The one place the spec underdetermines that rule is aromatic atoms: §3.1.5
sums bond orders but never says what an aromatic bond contributes, and §3.5
only asks that electrons be assignable "without violating the valence rules".
Summing aromatic bonds at `3/2` and applying the rule literally gives the
nitrogen of `Cn1cccc1` and the sulfur of thiophene a hydrogen they cannot
have.  `implicitHydrogens` therefore snaps an aromatic atom whose sum
overshoots its lowest valence down to the largest valence it does not
exceed, when within `3/2` of it — RDKit's rule, and the one that makes
hydrogen counts agree with RDKit on all 1 128 Delaney molecules.

## 5. Writing and canonicalization (`Write.lean`, `Canon.lean`)

The writer is Weininger's two-pass DFS (find ring closures, then emit with
lowest-free-digit allocation and parenthesised branches), parameterised by a
rank on atoms; everything it decides, it decides from ranks and bond kinds.

Canonicalization is **color refinement + exhaustive tie-breaking**:

1. Invariant per atom (degree, Z, H, aromatic, charge, isotope, bracketed,
   class, chirality mark) → ranks.
2. Refine by sorted (neighbor rank, bond kind) until the partition stops
   splitting — Morgan / Weisfeiler–Lehman.
3. If atoms remain tied: individualize *each* atom of the lowest tied class in
   turn, refine, recurse.  Write a SMILES for every discrete leaf; keep the
   lexicographically smallest string (and its ranks).

Step 3 is where this differs from RDKit (Schneider, Sayle & Landrum 2015),
which individualizes one tied atom and never backtracks.  That is fast and
right whenever the tie is a true symmetry, but refinement does not guarantee
that, so RDKit's output is not *provably* canonical on general graphs — the
`canonical-smiles` branch's scope document makes this point and proposes the
exhaustive mode as the fix.  Here the set of leaves is label-independent, so
the minimum is label-independent, which is the theorem we want:

```
canonicalSmiles (relabel σ m) = canonicalSmiles m      -- `canonicalSmiles_relabel`, Canonicity.lean
```

The full search costs one leaf per element of the automorphism group when
every tie is a true symmetry (more when refinement leaves non-equivalent atoms
tied), at a few milliseconds per leaf.  Size is not the issue — taxol
(62 atoms) and vancomycin (101) each have one tied pair and 2 leaves — symmetry
is: tetraphenylmethane 384 leaves (4!·2⁴), 1,3,5-tri-*tert*-butylbenzene 1 296
(6·6³), tetra-*tert*-butylmethane 31 104 (4!·6⁴, 17 s), and a 53-atom
second-generation *tert*-butyl dendrimer about 7 × 10¹³ (4!·1296⁴).

`search` prunes as nauty does.  Before exploring the subtree under a tied
atom it walks that subtree to its first leaf and asks whether an already
explored sibling's first leaf is an automorphic image of it.  The candidate
automorphism is the permutation carrying one leaf's rank order onto the
other's, and it is *checked* — it must fix the data, fix the current ranking,
and send the sibling to the atom — before the subtree is skipped; soundness
rests on the check alone (`Canonicity`: the pruned and the full search have
the same minimum).  Every case above collapses to a single explored leaf:
tetra-*tert*-butylmethane in 0.2 s, the dendrimer in 17 s.  There is no
budget.  What stays exponential is refinement-tied atoms that are *not*
symmetric, as in regular graphs, where a 62-atom cage explores 62 leaves in
3.5 s.

The search reads the molecule as `MolData` — atoms plus bond matrix, the
normal-form data — because there an automorphism is a literal equality
`d.relabel γ = d`.  The matrix is a table field, built row by row from each
atom's bonds (`adjMatrix` entry by entry would scan the bond list n² times).

## 6. Compared with the `canonical-smiles` branch

The branch (`LeanSMILES/Canonical/*`) is the mirror image of this design, and
the two are complementary rather than competing.

| | `canonical-smiles` branch (`Chem.Mol`) | this branch (`Molecule n`) |
|---|---|---|
| Representation | `Array Atom`, `Array Bond`, `Nat` indices | `Vector Atom n`, `List (Bond n)`, `Fin n` indices |
| Invariants | checked at run time, like RDKit | in the type (`Fin n`, `ne`, `nodup`) |
| Elements | table of 27 elements as `Nat` + strings | 118-constructor `Element` |
| Bond order | half-units (`Nat`), RDKit enum | `BondKind` with `order : ℚ` |
| Mathlib | none (planned `toSimpleGraph`) | `SimpleGraph`, `Matrix ℚ`, theorems |
| Chemistry | full RDKit sanitization: cleanup, kekulize, aromaticity, strict valence (860 lines) | implicit H only |
| Canonical SMILES | RDKit's ranking and walk, string-identical to RDKit on 1 128/1 128 Delaney | exhaustive minimum with automorphism pruning, canonical by theorem (`canonicalSmiles_relabel`), not RDKit's string |
| Stereo | skipped | recorded, not written |
| Test oracles | `datasets/*-oracle.csv`, `fuzz-validity.tsv` (reused here) | — |

What each should take from the other: the branch's `Sanitize` is exactly a
`Molecule n → Molecule n` pass (it only changes atom fields and bond kinds),
so it could run on this representation unchanged in shape; and its RDKit
ranking could be a second `canonical` mode here — RDKit-matching output for
interoperability, exhaustive output for the theorem.  Its oracle files are
already the test suite of this branch (§7).

## 7. What is tested (`lake exe validity-test`, `lake exe oracle-test`)

* **Validity**: 10 000 randomly broken SMILES with RDKit's accept/reject
  verdict.  Everything RDKit accepts must parse (parser bugs = 0).  Strings
  RDKit rejects but this parser accepts are expected — RDKit's valence model —
  and are counted and shown.
  *Result:* 2 601/2 601 RDKit-accepted strings parse; 0 parser bugs.  1 815 of
  the 7 399 RDKit-rejected strings parse here — pentavalent carbons, `Br#B`,
  lowercase atoms outside rings, and the like: valence and aromaticity, not
  syntax.
* **Oracle**: the 1 128 Delaney molecules.  Atom count, bond count, element
  symbols and connectivity must equal RDKit's (syntax).  Bond types and
  hydrogen counts after RDKit's aromaticity model are reported, not required.
  The canonical SMILES must survive a reparse and be unchanged under two
  relabelings of the atoms (`finRotate`, `Fin.revPerm`).
  *Result:* syntax 1 128/1 128, reparse 1 128/1 128, relabeling invariance
  1 128/1 128.  For information: as-written bond types equal RDKit's
  post-aromaticity ones on 1 000/1 128 (the same 1 000 the branch's scope
  document reports for "graph as written"), hydrogen counts on 1 089/1 128,
  and our canonical string coincides with RDKit's on 789/1 128 — with a
  different walk and tie-breaking rule, that is incidental agreement, not a
  goal.
* **Morgan** (`lake exe morgan-test`, `LeanSMILES/Fingerprint/Morgan.lean`):
  ring membership (bond on a cycle ⇔ not a bridge) must equal RDKit's
  `atom_in_ring` on every molecule; wherever the as-written bond types and
  hydrogen counts equal RDKit's sanitized ones, the unfolded identifiers with
  counts and the folded bits must be identical; and the identifiers must be
  unchanged under relabeling.
  *Result:* ring membership 1 128/1 128; fingerprint = RDKit on 971/971 of the
  molecules whose graph = RDKit's; relabeling invariance 1 128/1 128.  Overall
  971/1 128 — the 157 misses are exactly the molecules whose graph RDKit's
  aromaticity model or nitro rewrite changes, i.e. the sanitization passes
  still to be ported (§9).

## 8. A Lean-specific lesson

The first version of `Canon` represented ranks as functions `Fin n → ℕ`
closing over a `let`-bound vector.  Lean eta-expands definitions to full
arity, so every rank lookup recomputed the whole vector, and each refinement
round nested another recomputation — exponential time, found when one
`#eval` ran for nine CPU-minutes.  Ranks are now `Vector ℕ n` data; the rule
is: a definition that *returns a function* should not do work before the
lambda.

A second one, found when the Morgan examples hung the build and again when
the caffeine walkthrough was killed for memory: `#eval` of a value whose
*type* mentions `(Mol.ofSmiles! s).n` — a `Vector α _`, a `List (Bond _)`, a
`Matrix (Fin _) (Fin _) ℚ` — ran for minutes while the same computation
wrapped in `IO.println (repr …)` took seconds.  So the cost was never the
evaluation: it is the `#eval` command inspecting the result type, during
which the elaborator's `whnf` unfolds the definition down to
`(Mol.ofSmiles! s).n` and then runs the parser *symbolically* — instant for
ethanol, unbounded for an aromatic ring.  Marking the binding
`@[irreducible]` fixed it while `opaque` did too and `set_option eval.pp false`
did not, which is the signature of the elaborator (which respects
`irreducible`), not the kernel (which ignores it).

The fix is therefore one attribute at the source: `Mol.ofSmiles!` is
`@[irreducible]`, so `(Mol.ofSmiles! s).n` is atomic to the elaborator however
the result is bound, and `#eval`s of dependent values need no `.toList`, no
`opaque`, no non-dependent wrapper.  The price is that a proof about a
*concrete* parse cannot unfold it with `rfl`; none does, and none should —
theorems are about `Molecule n`, and a concrete fact is `decide`d or run.
Compiled code (`lake exe …`) is unaffected either way.

## 9. Next steps

1. **The canonicity theorem** — done, with no hypothesis:
   `canonicalSmiles_relabel` in `SMILES/Canonicity.lean`,
   `(m.relabel σ).canonicalSmiles = m.canonicalSmiles`.  Refinement commutes
   with relabeling and the leaf list is permuted, as expected; the writer
   needed no proof at all, because `writeRanked` was redefined as "relabel
   into rank order, then write in index order", so its commuting is
   `relabel_relabel`; and pruning is sound because it acts only on symmetries
   it has checked.
2. **Round trip**: `parse (toSmiles m) ≅ m` as labeled graphs.
3. **Degree lemma**: `graph.degree i = degree i` (needs `nodup`).
4. **Chemistry as passes**: port the branch's sanitization as
   `Molecule n → Molecule n` functions, each with its own tests, each optional.
5. **Stereo**: interpret `@`/`@@` as a parity over the neighbor order, and
   write `/` `\` from the walk.
6. **Featurization**: ~~Morgan fingerprints~~ — done, `LeanSMILES/Fingerprint/Morgan.lean`
   (§7); next, `Atom → Fin k` one-hots and feeding `morganVector` to the ML
   side once the ML algorithms (`Scalar.lean`'s `ScalarLike`, the branch's
   logistic regression) are cleaned up.

## Sources

* D. Weininger, A. Weininger, J. L. Weininger, "SMILES. 2. Algorithm for
  generation of unique SMILES notation", *J. Chem. Inf. Comput. Sci.* **29**, 97 (1989).
* N. Schneider, R. A. Sayle, G. A. Landrum, "Get Your Atoms in Order — An
  Open-Source Implementation of a Novel and Robust Molecular Canonicalization
  Algorithm", *J. Chem. Inf. Model.* **55**, 2111 (2015).
* B. D. McKay, A. Piperno, "Practical graph isomorphism, II", *J. Symbolic
  Comput.* **60**, 94 (2014) — the individualization-refinement scheme.
* OpenSMILES specification, opensmiles.org.
* pysmiles (P. C. Kroon), `read_smiles.py` — the syntax/semantics split that
  `base_smiles_parser` makes explicit.
* RDKit `Code/GraphMol/SmilesParse/`, and the `canonical-smiles` branch's
  `docs/scope-canonical-smiles-morgan.md` for file-and-line references.
