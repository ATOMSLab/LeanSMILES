# Scope: canonical SMILES and Morgan fingerprints in Lean 4

**Goal.** Starting from the SMILES strings that `CSVparser.load` already gives us, compute in Lean:

1. a **canonical SMILES** for each molecule, and
2. its **Morgan fingerprint** (radius 2, 2048 bits, ECFP4-like),

matching RDKit's output exactly where that is realistic, and **proving** properties that RDKit only tests.

Everything below was checked against RDKit **2026.09.1** (source tag `Release_2026_09_1`) on the 1,128 molecules in `datasets/delaney-processed.csv`.

---

## 1. How RDKit does it

### 1.1 The shared front end: SMILES → molecular graph

Both outputs start from the same graph, so the parser is the foundation of everything.

```
SMILES string
  │  lex + parse (grammar)            SmilesParse/SmilesParse.cpp, smiles.yy
  ▼
atoms + bonds, ring-closure digits joined, unwritten bonds typed
  │  (bond between two lowercase atoms = AROMATIC, else SINGLE)   SmilesParseOps.cpp:350-375
  ▼
sanitize                                    MolOps.cpp:616-710
  ├─ cleanUp          (e.g. nitro N(=O)=O  →  [N+](=O)[O-])
  ├─ valence check + implicit H count       Atom.cpp:458
  ├─ kekulize
  ├─ ring perception (SSSR)
  ├─ aromaticity perception (Hückel 4n+2 over fused ring systems)
  └─ conjugation, hybridization, chirality cleanup
  ▼
molecular graph  ──►  canonical SMILES
                 └─►  Morgan fingerprint
```

### 1.2 Canonical SMILES = canonical atom ranking + a deterministic walk

**Atom ranking.** The algorithm is Schneider, Sayle & Landrum, *J. Chem. Inf. Model.* 2015, "Get Your Atoms in Order" (`new_canon.h`, `new_canon.cpp`).

1. **Start.** Put every atom in one class.
2. **Compare atoms on their own properties.** Atoms are compared field by field (`new_canon.h:323-520`), in this order: current class, degree, atomic number, isotope, total H count, formal charge, then stereo fields when isomeric output is on.
3. **Compare atoms by their neighbours.** If two atoms tie on step 2, compare their neighbour lists. Each neighbour is a (bond type, neighbour's current class) pair, and the list is sorted in descending order (`new_canon.h:546-598`).
4. **Refine until stable.** Split classes and re-check the neighbours of any atom whose class changed, until nothing changes (`RefinePartitions`, `new_canon.h:728-833`). This is the same idea as Morgan's iteration, and as Weisfeiler–Lehman colour refinement.
5. **Break ties.** If symmetric atoms are still tied, split off one atom from the tied class, refine again, and repeat until every atom has a unique rank (`BreakTies`, `new_canon.h:836-886`). There is **no backtracking**.

**Writing the string** (`Canon.cpp`, `SmilesWrite.cpp`).

1. **Start atom.** Begin at the lowest-ranked atom.
2. **Find ring closures.** One depth-first pass finds the ring-closure bonds.
3. **Emit tokens.** A second pass writes the string.
   - **Neighbour order:** ring closures first, then non-ring branches, then ring continuation. Ties go to the lower rank (`Canon.cpp:890-913, 1075-1086`).
   - **Branches:** every child except the last is wrapped in `( )`.
   - **Ring-closure digits:** use the smallest free digit, and reuse digits once they are freed (`SmilesWrite.cpp:436-476`).
4. **Brackets and hydrogens.** Brackets are used only when needed: not in the organic subset, charged, isotope, explicit H on aromatic N, and so on (`atomNeedsBracket`, `SmilesWrite.cpp:97-154`). Outside brackets, hydrogens are left implicit.
5. **Disconnected pieces.** Fragment strings are sorted and joined with `.`.

**Example:** `OCC`, `C(O)C` and `[CH3][CH2][OH]` all become `CCO`, and `C1=CC=CC=C1` becomes `c1ccccc1`.

### 1.3 Morgan fingerprint

A complete, **verified** pure-Python reference is in [`reference/morgan_ref.py`](reference/morgan_ref.py). It is ~90 lines, and it matches RDKit's bits and unfolded IDs on **all 1,128 Delaney molecules**. Use it as the spec and the test oracle for the Lean version.

The algorithm (`Fingerprints/MorganGenerator.cpp`, `FingerprintUtil.cpp`, `RDGeneral/hash/hash.hpp`):

1. **Hash primitive.** All arithmetic is unsigned 32-bit with wrap-around, using boost's
   `hash_combine(seed, v) = seed ^ (v + 0x9e3779b9 + (seed << 6) + (seed >> 2))`.
2. **Radius-0 ID per atom.** Hash the list `[atomic number, total degree incl. H, total H, formal charge, isotope mass delta]`, and append `1` if the atom is in any ring. Aromaticity is **not** part of the atom ID.
3. **Each radius r = 1, 2.** For each atom:
   1. Collect `(bond type, neighbour's current ID)` pairs. The bond type is an enum: SINGLE=1, DOUBLE=2, TRIPLE=3, AROMATIC=12.
   2. Sort the pairs.
   3. Compute the new ID as `hash_combine(seed = r−1, own ID)`, then fold in each pair.
4. **Deduplication.** If two atoms' environments cover the same set of bonds, keep only the one with the smaller (ID, atom index). Any environment already seen in an earlier round is dropped. Dropped atoms are "dead": they contribute ID 0 in later rounds.
5. **Folding.** `bit = ID mod 2048`.

**Details that must be exact.** Getting any of these wrong breaks the match (checked by deliberately breaking each one):
- the seed is the layer index, not 0;
- pairs are sorted by bond type first;
- each pair is hashed on its own (starting from seed 0) before being folded in;
- the bond type is the enum value (12 for aromatic), not a bond order like 1.5;
- deduplication keeps the smallest (ID, atom index);
- dead atoms contribute 0.

**Python API gotcha.** `GetMorganGenerator`'s default radius is **3**, not 2, so always pass `radius=2`. Its `includeRingMembership=` keyword is silently ignored.

---

## 2. What the Delaney data actually needs

| Feature | Molecules | Share |
|---|---|---|
| Aromatic (after RDKit sanitization) | 662 | 58.7% |
| Written with lowercase aromatic atoms | 665 | 59.0% |
| Any ring | 811 | 71.9% |
| Bracket atoms in input (e.g. `[nH]`) | 31 | 2.7% |
| Formal charges after sanitization | 59 | 5.2% (58 are nitro groups RDKit rewrites) |
| Stereo (`@`, `/`, `\`) | 8 | 0.7% |
| Isotopes / non-organic elements / multiple fragments | 0 | 0% |

**Key finding: we can skip aromaticity perception at first.** Delaney already writes its aromatic rings in lowercase, so the parser gets aromatic bonds for free. Two small rules recover almost everything else that RDKit's sanitization changes:

1. **Rule 1:** an aromatic bond that is **not in a ring** becomes single. This fixes biphenyl-type ring-to-ring links.
2. **Rule 2:** nitro `N(=O)=O` becomes `[N+](=O)[O-]`.

| Graph given to the algorithms | Morgan bits = RDKit | Canonical SMILES = RDKit |
|---|---|---|
| As written, no perception | 1000 / 1128 (88.7%) | — |
| As written + rules 1–2 | **1114 / 1128 (98.8%)** | **1114 / 1128 (98.8%)** |

The remaining 14 molecules need real aromaticity perception. They are fused systems such as fluorene and fluoranthene, where a ring bond between lowercase atoms sits in a ring that is not itself aromatic, plus two N-oxides and a flavin.

The canonical SMILES column measures how good our **graph** is: RDKit's own canonicalizer ran on our rule-adjusted graph. The Lean canonicalizer must also reproduce RDKit's ranking and walk exactly to reach that ceiling.

> **Update:** real aromaticity perception is now implemented (section 4.2). Rules 1–2 have been replaced by RDKit's own cleanup, kekulization and aromaticity steps, so all 1,128 molecules, including the 14, now get RDKit's exact graph.

---

## 3. Proposed Lean architecture

```
LeanSMILES/
  Data/CSVparser.lean          (exists)
  Canonical/Molecule.lean      ✅ elements, RDKit valence lists; structure Atom, Bond, Mol
  Canonical/Parse.lean         ✅ SMILES parser: organic subset, brackets, branches, ring closures, %nn
  Canonical/Sanitize.lean      ✅ implicit H, ring membership, cleanUp, valence checks, ring set,
                                  kekulization, aromaticity; molFromSmiles
  Canonical/Write.lean         ✅ canonical ranking + DFS writer; canonicalSmiles
  Canonical/Morgan.lean        ✅ port of reference/morgan_ref.py; morganBits, morganIds, tanimoto
  Proofs/...                   theorems (section 5)
tools/rdkit_oracle.py          ✅ dumps RDKit's answers per molecule → CSV for Lean tests
```

**Pieces confirmed working in this Lean/Mathlib version (v4.30.0-rc1):**
- **32-bit hashing:** wrap-around `UInt32` arithmetic (`^^^`, `<<<`, `>>>`) gives the same `hash_combine` result as the Python reference.
- **Parsing:** `Std.Internal.Parsec` parses SMILES-style tokens.
- **Graphs for proofs:** Mathlib has `SimpleGraph.Iso`, `SimpleGraph.IsBridge` and `isBridge_iff_adj_and_forall_cycle_notMem` (a bond is a bridge if and only if it lies on no cycle). That last lemma lets us prove ring membership correct.

**Design choice:** compute on simple `Array`-based structures, which are fast and easy to `#eval`. For proofs, give a function `Mol.toSimpleGraph : Mol → SimpleGraph (Fin n)`.

---

## 4. Phased plan

| Phase | Deliverable | Done when | Rough effort |
|---|---|---|---|
| **0. Oracle** ✅ | `tools/rdkit_oracle.py` writes `datasets/delaney-oracle.csv` (see 4.1) | CSV exists | done |
| **1. Graph** ✅ | `Mol` types, SMILES parser, implicit H, ring membership, **RDKit sanitization incl. aromaticity** | Per-atom and per-bond data agrees with RDKit (see 4.2) | done |
| **2. Morgan** ✅ | `Canonical/Morgan.lean` (port of the reference) | 1,128/1,128 exact bit match (see 4.4) | done |
| **3. Canonical SMILES** ✅ | `Canonical/Write.lean` (`Chem.canonicalSmiles`) | 1,128/1,128 exact string match (see 4.3) | done |
| **4. Proofs** | Theorems from section 5, easiest first | Each one `sorry`-free | open-ended |
| 5. Optional | Stereo | — | large |

### 4.1 The oracle file

Regenerate it with the `ench470` environment, or any Python that has RDKit 2026.09.1:

```bash
python tools/rdkit_oracle.py
```

`datasets/delaney-oracle.csv` has one row per molecule. Row `i` lines up with `records[i]` from `CSVparser.load`, and the `smiles` column is identical to `records[i].smiles` for all 1,128 rows. Multi-value columns are space-separated.

| Column | Use it to test |
|---|---|
| `index`, `smiles` | Lining rows up with Lean's `records` |
| `canonical_smiles` | RDKit's default `MolToSmiles` (with stereo marks) |
| `canonical_smiles_nostereo` | Phase 3: `MolToSmiles(isomericSmiles=False)`, what `Chem.canonicalSmiles` gives |
| `morgan_bits` | Phase 2 (on-bits, radius 2, 2048 bits) |
| `morgan_ids` | Phase 2 debugging (unfolded `id:count` pairs, before folding) |
| `num_atoms`, `num_bonds` | Phase 1 parser (heavy atoms only) |
| `atom_symbols`, `atom_total_hs`, `atom_charges`, `atom_in_ring` | Phase 1, per atom in input order (RDKit keeps the SMILES atom order). These are values after sanitization, so nitro N/O show charges +1 and −1. |
| `bonds` | Phase 1, per bond `i-j:t` (i < j, sorted), `t` = RDKit bond type 1/2/3/12 (aromatic) |
| `needs_aromaticity` | `1` if the old shortcut (graph as written + rules 1–2) could not match. Kept as a label for the hard cases; the Lean code no longer needs to exclude them. |

`docs/reference/morgan_ref.py` reproduces `morgan_bits` and `morgan_ids` on all 1,128 rows. The output is deterministic: rerunning gives a byte-identical file.

The same command writes further test files with the same columns:

| File | Molecules |
|---|---|
| `datasets/delaney-kekule-oracle.csv` | The 1,128 Delaney molecules re-written in Kekulé form (`C1=CC=CC=C1`, no lowercase), so aromaticity must be *perceived*. Atom order follows the new strings. |
| `datasets/hydrogen-cases-oracle.csv`, `…-kekule-oracle.csv` | 494 molecules with hydrogens written as atoms (incl. isotopic, charged and stereo-defining ones), from `datasets/hydrogen-cases.csv` |
| `datasets/isotope-cases-oracle.csv`, `…-kekule-oracle.csv` | 500 Delaney molecules with up to 3 random isotope labels each (real, exceptional and made-up isotopes), from `datasets/isotope-cases.csv` |
| `datasets/aromaticity-cases-oracle.csv`, `…-kekule-oracle.csv` | 56 hand-picked hard cases (azulene, pyrene, tropone, `[cH-]1cccc1`, N-oxides, [18]annulene, …), from `datasets/aromaticity-cases.csv`: `python tools/rdkit_oracle.py datasets/aromaticity-cases.csv datasets/aromaticity-cases-oracle.csv datasets/aromaticity-cases-kekule-oracle.csv` |

### 4.2 Phase 1 status

Run the test from the repository root:

```bash
lake exe phase1-test                     # Delaney, as written and in Kekulé form
lake exe phase1-test datasets/aromaticity-cases-oracle.csv datasets/aromaticity-cases-kekule-oracle.csv
lake exe canonical-validity-test                   # broken SMILES: accepted/rejected exactly like RDKit?
```

**Result:** every molecule matches RDKit atom by atom and bond by bond (atom and bond counts, element symbols, total H counts, formal charges, ring membership, bond types including aromatic), and Lean rejects exactly the SMILES RDKit rejects.

| Test set | Matches RDKit |
|---|---|
| Delaney as written / Kekulé form | **1,128 / 1,128**, **1,128 / 1,128** |
| 56 hard aromaticity cases, both forms | **56 / 56**, **56 / 56** |
| `datasets/fuzz-validity.tsv`: 10,000 randomly broken SMILES, accept vs reject | **all agree**, except 63 with elements Lean does not support yet (reported separately) |
| One-off checks (not in the repo), both forms each: NCI `first_5K.smi` (4,830), ENCH 470 EGFR actives / inactives / FDA drugs (100 / 100 / 5), ThermoProperties isomeric and canonical SMILES (5,618 and 4,250), 3,997 broken-but-valid fuzz SMILES | **all match** |

`Chem.molFromSmiles` mirrors RDKit's `MolFromSmiles` (`Canonical/Sanitize.lean`): parse (with RDKit's syntax rules) → remove hydrogen atoms (`removeHs`) → freeze H counts → cleanup → **strict valence check** → cache valences → ring set → kekulize (RDKit's walk) → radicals → aromaticity → final H counts (`adjustHs`) → **strict valence check again**. The Python reference for the middle steps is `docs/reference/aromaticity_ref.py`, checked by `docs/reference/verify.py`.

**Hydrogens written as atoms** (`[H]C([H])([H])[H]`, `[H]O[H]`): like RDKit's `MolFromSmiles` (`removeHs` with `updateExplicitCount`, `SmilesParse.cpp:473-477`, `AddHs.cpp:840-1082`), ordinary hydrogen atoms are removed right after parsing and counted on their neighbour. Kept: hydrogens with no bond or several bonds, isotopes (`[2H]`), hydrides (`[H-]`), H bonded only to H (`[H][H]`), H on atoms with non-tetrahedral stereo (`@SP`, `@TB`, `@OH`), and H attached by `/` or `\` to a two-neighbour atom with a double bond (`[H]/C=C/F`). Test set: `datasets/hydrogen-cases*.csv` (494 molecules, all match on all three tests in both forms); one-off checks also matched on every NCI molecule (4,858) and every ThermoProperties molecule (5,618, of which 331 have a stereo bond to a hydrogen) written with all hydrogens as atoms.

**Found by the broken-SMILES (fuzz) test, now fixed:**
- **Syntax:** RDKit rejects bonds at the start or end, two bonds in a row, a bond before `(` `)` `.`, empty branches `()`, a ring digit right after `(` or `(=`, `%` with one digit, duplicate bonds via ring closures (`C1C1`), and malformed chirality (`@@3`, `@I`). The bond written at the *opening* ring digit wins; `/` `\` between aromatic atoms keep the bond aromatic.
- **Valence:** RDKit's strict valence check runs twice, after cleanup and again at the very end (`C=oC` only fails the second).
- **Cached values:** RDKit's aromaticity reads valences and H counts cached *before* kekulization (matters for arynes `c#c` and odd `[nH]=C`).
- **Final H counts** are recomputed on the final graph; atoms that are or were aromatic get lost implicit Hs back as explicit Hs (`adjustHs`).
- **Kekulé structure:** RDKit's own queue-based walk is now ported, so the double-bond positions match even in rings that stay non-aromatic (`Cc1cccc2ncc12`).

| File | What it does |
|---|---|
| `Canonical/Molecule.lean` | Symbols, RDKit's allowed-valence lists, outer electrons; `Atom`, `Bond`, `BondOrder`, `Mol` (arrays; atoms in SMILES order, same as RDKit) |
| `Canonical/Parse.lean` | `Smiles.parse`: a hand-written left-to-right scanner covering organic subset, lowercase aromatic atoms, bracket atoms, `- = # : / \`, branches, ring closures `1`–`9` and `%nn`, and `.`, with RDKit's syntax rules |
| `Canonical/Sanitize.lean` | One section per step: implicit H (port of `Atom.cpp:350-613`, half-units), ring membership (a bond is in a ring iff not a bridge, the Mathlib `IsBridge` notion), RDKit `cleanUp` (`MolOps.cpp:51-329`), ring set (relevant cycles), kekulization (RDKit's walk), aromaticity (donor types, Hückel 4n+2, fused groups ≤ 6 rings); `Chem.molFromSmiles` |
| `Tests/Phase1.lean` | `lake exe phase1-test`: per-atom / per-bond comparison with an oracle file |
| `Tests/CanonicalValidity.lean` | `lake exe canonical-validity-test`: accept/reject agreement on `datasets/fuzz-validity.tsv` (made by `tools/rdkit_fuzz.py`) |
| `Examples/molgraph.lean` | Small `#eval` examples |

**Things learned while matching RDKit:**
- **Nitro rule:** RDKit charge-separates `N(=O)=O` by giving −1 to the **first** `=O` in bond order. The same rule turns the N-oxide `n1=O` into `[n+]1[O-]`.
- **Hydrogen rule for aromatic atoms:** aromatic atoms whose bond total exceeds their default valence snap down to an allowed valence when within 1.5 (`Atom.cpp:369-400`). After that, any half-valence is rounded up.
- **H counts are frozen before kekulization** for the intermediate steps, as in RDKit; the final counts are recomputed at the end (`adjustHs`, above).
- **Fused rings** are tried together only if they share exactly one bond and have ≤ 24 bonds each, in groups of at most 6 rings. That is why fluorene's CH2 ring stays non-aromatic, while azulene, fluoranthene and pyrene become fully aromatic.
- **Stereo:** `/` and `\` are read as single bonds and chirality marks are skipped. This is enough here, because Morgan (by default) and the atom data do not use stereo.

### 4.3 Phase 3 status: canonical SMILES

`Chem.canonicalSmiles` (`Canonical/Write.lean`) ports RDKit's canonical atom ranking (`new_canon.h/.cpp`: class refinement on degree, element, H count, charge compared as unsigned, neighbour classes; the special symmetry pass; tie breaking) and its SMILES writer (`Canon.cpp`, `SmilesWrite.cpp`), from the verified Python reference `docs/reference/canon_ref.py`.

```bash
lake exe canonical-test        # Delaney, as written and in Kekulé form
lake exe canonical-test datasets/aromaticity-cases-oracle.csv datasets/aromaticity-cases-kekule-oracle.csv
```

It equals RDKit's `MolToSmiles(mol, isomericSmiles=False)` on all Delaney molecules (both forms) and the 56 hard cases (both forms). One-off checks outside the repo also matched on the NCI sample (4,830, both forms), the ENCH 470 ThermoProperties and EGFR sets, 3,997 odd-but-valid fuzz SMILES, and 29,790 randomly re-written SMILES. Not covered: stereo marks and isotopes in the output. One approximation from the reference: "atom in more than one ring" (used only to decide whether the special symmetry pass runs) is taken as "has ≥ 3 ring bonds"; it never changed an output in testing.

`LeanSMILES/Examples/canonical.lean` shows typical use.

### 4.4 Phase 2 status: Morgan fingerprints

`Chem.morganBits` / `Mol.morganIds` (`Canonical/Morgan.lean`) port `docs/reference/morgan_ref.py`: radius-0 invariants (element, degree incl. H, H count, charge as uint32, mass shift, in-ring), layer-seeded `hash_combine` over sorted (bond type, neighbour id) pairs, bond-set deduplication keeping the smallest (id, atom), dead atoms contributing 0, folding by `id mod fpSize`.

```bash
lake exe canonical-morgan-test           # Delaney, as written and in Kekulé form
lake exe canonical-morgan-test datasets/aromaticity-cases-oracle.csv datasets/aromaticity-cases-kekule-oracle.csv
```

Both the folded bits and the unfolded identifiers with counts equal RDKit's (`radius=2, fpSize=2048`) on all Delaney molecules, the 56 hard cases and 500 isotope-labelled molecules (`datasets/isotope-cases*.csv`), in both forms. One-off checks outside the repo also matched on the NCI sample (4,830), the ENCH 470 ThermoProperties and EGFR sets, 3,997 fuzzed SMILES and 3,000 more isotope-labelled molecules, in both forms.

**Isotopes.** RDKit's invariant includes `int(mass − atomic weight)`: the exact isotope mass from RDKit's table, or the isotope number for isotopes not in the table (`Atom.cpp:644-655`). `isotopeMassShift` (`Canonical/Molecule.lean`) reproduces this from each element's atomic weight plus the 82 known isotopes whose exact mass gives a different answer than the isotope number (e.g. `[2H]` → 1, while `[13C]` → 0). The table is generated by `tools/rdkit_isotope_table.py`, which also checks the rule against RDKit for every isotope 1–400 of every supported element.

`LeanSMILES/Examples/morgan.lean` shows typical use (bits, radius, Tanimoto similarity, bit vector).

### 4.5 Classification: logistic regression on Morgan fingerprints

`LeanSMILES/ML/Logistic.lean` fits scikit-learn's L2-regularized logistic regression (`½‖w‖² + C Σ log(1 + e^(−ỹ score))`, intercept not penalized) by Nesterov-accelerated gradient descent with gradient-based restart. The step size comes from a power-iteration estimate of the curvature. Samples are sparse 0/1 vectors (Morgan on-bits). It is written over `ScalarLike` plus a small `ExpLog` class (`exp`, `log`), with `Float` and `ℝ` instances.

Task (ENCH 470 Lecture 21): EGFR actives (100) vs inactives (100) from ChEMBL, radius-2 / 2048-bit Morgan bits, scikit-learn's `train_test_split(test_size=0.20, random_state=0)` (stored in `datasets/egfr-classification.csv` by `tools/sklearn_egfr.py`), `C = 1`.

```bash
lake exe logistic-test
```

| | scikit-learn | Lean |
|---|---|---|
| Train / test accuracy | 0.99375 / 0.925 | 0.99375 / 0.925 |
| Test confusion matrix | [[20, 2], [1, 17]] | [[20, 2], [1, 17]] |
| Predicted class, all 205 molecules (incl. FDA drugs) | — | identical |
| Largest probability difference | — | 1.1 × 10⁻⁷ |
| FDA drugs P(active): gefitinib, erlotinib, lapatinib, afatinib, osimertinib | 0.988, 0.991, 0.991, 0.999, 0.136 | the same |

Training takes 1,283 iterations (about 1 s compiled). `LeanSMILES/Examples/classification.lean` walks through the lecture in Lean.

**Hackathon recommendation:** do phases 0–2 plus the ring-membership and Morgan-invariance proofs. Morgan is short, fully specified and verified, so "fingerprints computed in Lean, bit-identical to RDKit, with a proof" is a strong, achievable result. Phase 3 is the bigger engineering piece.

---

## 5. What we could prove

From easiest to hardest:

1. **Ring membership is correct.** Our bridge-based `inRing` agrees with "lies on a cycle" in Mathlib's `SimpleGraph`. Mathlib's bridge lemmas do most of the work.
2. **Morgan doesn't depend on atom numbering.** Renumbering the atoms leaves the set of unfolded IDs unchanged, and therefore the bits too. The core lemma is that each step only uses sorted neighbour data.
3. **Refinement is well behaved.** The refined partition is equitable and is preserved by graph isomorphisms. After tie-breaking, the ranks are a permutation of `0 … n−1`.
4. **The writer produces valid SMILES.** Branch parentheses and ring digits are balanced, and every digit is free when it is opened.
5. **Round trip:** `parse (write g) ≅ g` as labelled graphs, including H counts.
6. **Canonicity:** `write (renumber π g) = write g` for every permutation π.

> **Caveat (important for item 6):** RDKit's tie-breaking picks one atom from each tied class *without backtracking*. That is only guaranteed correct when the tied atoms are truly symmetric (automorphic). Colour refinement does not guarantee this: there are graphs where atoms tie but are not symmetric. So item 6 is **false for RDKit's algorithm on general graphs**. Options:
> - prove it only for molecules where refinement already separates every atom, or where every remaining tie is a true symmetry; or
> - add a second, "provably canonical" mode that tries every choice at each tie and keeps the lexicographically smallest output (the nauty/InChI approach). It's slower, but item 6 becomes a clean theorem.
>
> Keep the RDKit-matching mode for comparing against RDKit, and the provably canonical mode for the theorem.

---

## 6. Out of scope for v1 (and what each would cost later)

| Feature | Cost | Notes |
|---|---|---|
| Charges, isotopes, general brackets in output | Low | Extra comparison fields and bracket-writing rules |
| ~~Aromaticity perception (RDKit model)~~ | ✅ done | See 4.2 |
| ~~Removing explicit hydrogen atoms (RDKit's `removeHs`)~~ | ✅ done | See 4.2 |
| Canonical Kekulé form (needed only to *write* Kekulé SMILES) | Medium | Port RDKit's queue-based walk exactly |
| Stereo (tetrahedral, E/Z) | High | Parity under the walk order; only 8 Delaney molecules |
| Morgan options (chirality, count simulation, FCFP features) | Low–Medium | Documented in `MorganGenerator.cpp`; off by default |

---

## 7. Sources

- RDKit source, tag `Release_2026_09_1`: `Code/GraphMol/{SmilesParse,Fingerprints}/`, `new_canon.{h,cpp}`, `Canon.cpp`, `MolOps.cpp`, `Code/RDGeneral/hash/hash.hpp`. File:line references above are from this tag.
- N. Schneider, R. A. Sayle, G. A. Landrum, "Get Your Atoms in Order — An Open-Source Implementation of a Novel and Robust Molecular Canonicalization Algorithm," *J. Chem. Inf. Model.* **55**, 2111 (2015).
- D. Rogers, M. Hahn, "Extended-Connectivity Fingerprints," *J. Chem. Inf. Model.* **50**, 742 (2010).
- D. Weininger, A. Weininger, J. L. Weininger, "SMILES. 2. Algorithm for generation of unique SMILES notation," *J. Chem. Inf. Comput. Sci.* **29**, 97 (1989).
