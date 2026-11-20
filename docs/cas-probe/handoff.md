# Handoff: CAS, InChI and LeanSMILES canonical forms

Written 2026-11-17. Covers the session of 2026-11-16 and 17 on branch
`claude/cas-molecular-representation-b2b0ac`.

## State

- **Nothing is committed.** `docs/cas-probe/` and `docs/scope-componentwise-canonical.md`
  are untracked. No Lean source was changed. (Since committed as `4b79de7` and merged
  into PR #38; see the update under "Three LeanSMILES gaps".)
- Every LeanSMILES number here comes from the `worker` binary built 2026-10-28 in the main
  checkout (`/Users/tylerjosephson/Documents/LeanSMILES/.lake/build/bin/worker`). It has
  the automorphism pruning from `4bff8ea`. Source at `4cf7a72` is a week newer and was
  **not** rebuilt, so the three LeanSMILES gaps below are unconfirmed at HEAD.
- This worktree has no build of its own.

## What was asked, and the short answers

1. **Can CAS's published SMILES reveal a weakness in how CAS represents molecules?**
   Partly. The strings on CAS Common Chemistry have real defects (wrong substance,
   different substances with the same string, isotopes and some stereo dropped), but
   nothing shows a canonicalization failure, and CAS's own paper says these strings are
   exports from a proprietary record. The weakness is in the export layer, not the
   registry. Details: [README.md](README.md).
2. **Is one string per molecule all you can see?** Up to two (`Canonical SMILES`, and
   `SMILES` when there is stereo), plus InChI and InChIKey. They are stored values; there
   is no way to feed CAS variants of one molecule.
3. **Has anyone proved InChI is unique?** No. There is no proof and no specification
   other than the C source. The nearest prior art is a formalization of the McKay–Piperno
   scheme in Isabelle/HOL (Banković, Drecun, Marić, LMCS 2023), which does not cover
   InChI and is not in Lean.
4. **How does InChI handle high symmetry?** `ichican2.c` implements McKay's 1981
   algorithm: it keeps the orbits found so far for the whole search tree, branches on one
   atom per orbit, and backjumps. LeanSMILES prunes only among siblings.
5. **What were InChI's published failures and how does LeanSMILES do on them?** See
   "InChI's known failures" below.
6. **Scope component-wise canonicalization.** Done, as a proposal only:
   [scope-componentwise-canonical.md](../scope-componentwise-canonical.md).

## Results worth carrying forward

### Speed on symmetric structures

[symmetry_inchi.out](symmetry_inchi.out), rerun 2026-11-17 with the three *tert*-butyl
alkanes added. InChI takes under 5 ms on every case and always gives one InChI.
LeanSMILES always gives one string when it finishes. The first row of that file
(neopentane, 0.25 s) includes the worker's cold start; alone it takes 0.04 s.

| Structure | Atoms | Symmetries | LeanSMILES |
|---|---|---|---|
| tetra-*tert*-butylmethane | 17 | 31 104 | 0.2 s |
| Tutte–Coxeter graph as (CH)30 | 30 | 1 440 | 1.3 s |
| *tert*-butyl dendrimer | 53 | about 7 × 10¹³ | 6 s |
| C60 | 60 | 120 | 5 s |
| 30-prism as (CH)60 | 60 | | 7 s |
| 8 × cubane, disconnected | 64 | | 23 s |
| 20 × neopentane, disconnected | 100 | | over 120 s |

Two readings:

- **Cost now follows atom count, not symmetry count.** The dendrimer has 10¹¹ times the
  symmetries of C60 and takes about the same time. The pruning removed the symmetry
  blow-up; what is left is one first-leaf walk per tied atom.
- **Repeated identical fragments are the realistic worst case**
  ([fragment_scaling.out](fragment_scaling.out)): large hydrates, solvates, mixtures.
  Everyday salts and hydrates are fine (alum with twelve waters 0.3 s).

The symmetry counts for the dendrimer and C60 are known values, not computed by the
script, which only counts for 30 atoms or fewer.

### InChI's known failures

Goodman et al. 2021 (J. Cheminform. 13:40) renumbered 111 476 790 PubChem structures 16
times each. InChI v1.06 gave more than one InChI for 547 of them (v1.05: 2 300). The list
of CIDs is in `INCHI-1-DOC/KNOWNISSUES.pdf` in the InChI repository. Of the 547, 534 have
a `/p` layer and 530 contain nitrogen: the failures are in hydrogen and charge
normalization, not in the graph canonicalizer.

I sampled 45 of the 547 plus the one `CANON_ERR` structure
([inchi_known_issues.out](inchi_known_issues.out)):

| | One string | Unstable | Timed out |
|---|---|---|---|
| InChI 1.07.3 via RDKit, 40 renumberings | 12 | 34 | 0 |
| LeanSMILES, stereo stripped, 4 renumberings, 40 s cap | 43 | 0 | 3 |
| LeanSMILES, stereo as given | 38 | 5 | 3 |

- The varying layer is `/h` in 33 of the 34.
- All 5 LeanSMILES failures are among the 9 structures that have stereo.
- The 3 timeouts are the 148-, 184- and 196-atom structures.
- **Caveats.** Renumbering went through RDKit, not Molfiles as in the paper. LeanSMILES
  is stable here because it does no protonation or mobile-hydrogen normalization at all,
  so this is a pass on an easier problem.

### Three LeanSMILES gaps found along the way

From [lean_stable.out](lean_stable.out) and the README table. Fix or confirm these
before any "ours is better" claim.

1. **Tetrahedral stereo is carried as a label.** The `@`/`@@` mark is not re-derived for
   the new neighbour order, so two writings of L-alanine give L- and D-alanine strings,
   and stereo-bearing molecules give 2 to 9 strings under renumbering.
2. **Double-bond stereo is dropped.** Maleic and fumaric acid give the same string.
3. **Aromatized output loses the H on an unbracketed N.** `C1=CNC=C1` becomes `c1ccnc1`
   (`Perceive.lean:239–241`).

**Update, 2026-11-17, at the merge of this probe into the aromatization branch
(PR #38).** The three gaps were checked on the library at that head (in Lean, with
`SMILES.parseAromatized` and `canonicalSmiles`; the worker was not rebuilt and the
`.out` files here were not rerun). All three are closed by work that reached `main`
after the probe's worker was built:

1. L-alanine written `N[C@@H](C)C(=O)O`, `C[C@H](N)C(=O)O` and `OC(=O)[C@@H](N)C`
   gives `C[C@H](N)C(=O)O` each time, and D-alanine gives `C[C@@H](N)C(=O)O` (#32).
2. Maleic acid gives `O=C(O)/C=C\C(=O)O` and fumaric acid `O=C(O)/C=C/C(=O)O` (#32).
3. `C1=CNC=C1` and `c1cc[nH]c1` both give `c1cc[nH]c1` (#37).

So the failure counts in the tables above that come from these gaps (the 5 failures
with stereo as given) describe the 2026-10-28 worker, not the library now. They have
not been recounted.

## Where the strategy landed

- Tyler's position: LeanSMILES cannot "specify" InChI alone, but could with IUPAC. He
  does not want to check molecules against a specification written in C; he wants the
  specification in Lean, with the C code as an oracle to test against, as LeanSMILES
  already does with RDKit. Credibility is the obstacle, hence a collaboration.
- The evidence supports that framing. LeanSMILES's asset is a proof
  (`Molecule.canonicalSmiles_relabel`, no hypothesis), not a faster or richer
  representation. InChI is about 1 000 times faster on these tests (the worker's time
  includes depiction and fingerprints, so the true gap is smaller) and handles stereo,
  tautomers and charges. Its surviving failures are in the normalization layer that
  nobody has written down.
- **Best opening for IUPAC:** 34 live cases, from their own list, where the unspecified
  layer still breaks in 1.07.3.
- **Pitch to CAS:** "verified exports" is the honest version, and it needs stereo
  semantics and a round-trip theorem first.

## Open questions for Tyler

- Is there a warm path to anyone on the InChI Trust or IUPAC side?
- Commit `docs/cas-probe/` and the scope note, or keep them out of the repo? The CAS
  strings in `cas.tsv` are CC BY-NC 4.0, which matters if the repo is used commercially.
- Which comes first: stereo, or the component-wise change?

## Suggested next steps

1. Rebuild the worker at HEAD and rerun `lean_check.py stable` and
   `inchi_known_issues.py` to confirm the three gaps. (The gaps are closed, see the
   update above; the rerun, to recount the tables, is still to do.)
2. Stereo: re-derive tetrahedral marks from neighbour order, write `/` and `\`. (Done, #32.)
3. Fix the aromatized N–H. (Done, #37.)
4. Component-wise canonicalization, steps 1 to 5 of the scope note (about 400 to 450
   lines of proof).
5. Orbit accumulation in `search`, for single large components.
6. Rerun the 46 known-failure structures from Molfiles to remove the RDKit caveat, then
   extend to all 547.

## Leads not followed

- "Deleted or Replaced CAS RNs" counts are high for hard-to-normalize structures
  (3-phenylsydnone 10, C60 18) and zero for cubane and adamantane. Could reflect
  re-registration trouble; famous compounds collect them anyway. Unproven.
- The writer behind CAS's `Canonical SMILES` was not identified. CDK could not be tested
  (no Java on this machine).
- cis-Cyclooctene and maleic acid record pages came back empty and were not retried.

## Files

| File | What |
|---|---|
| [README.md](README.md) | The CAS probe write-up |
| `panel.tsv`, `cas.tsv` | 81 test molecules; 65 CAS records typed in by hand |
| `check_cas.py`, `.out` | Self-consistency of CAS's strings against the record's InChIKey |
| `toolkits.py`, `.tsv` | RDKit against OpenBabel under 200 reorderings |
| `lean_check.py`, `lean_stable.out` | LeanSMILES on CAS's strings and under reordering |
| `symmetry_inchi.py`, `.out` | Symmetric graphs: InChI against LeanSMILES |
| `fragment_scaling.out` | Repeated-fragment timings (run by hand, no script kept) |
| `inchi_known_issues.py`, `.out` | The 46 InChI known-failure structures |
| [../scope-componentwise-canonical.md](../scope-componentwise-canonical.md) | Scope proposal |

```bash
PY=~/miniforge3/envs/rmg_env/bin/python
W=/Users/tylerjosephson/Documents/LeanSMILES/.lake/build/bin/worker
$PY docs/cas-probe/symmetry_inchi.py $W 50 120
$PY docs/cas-probe/inchi_known_issues.py $W 40 40
```

The README has the commands for the CAS and toolkit checks.

## Practical notes

- **Python:** `~/miniforge3/envs/rmg_env/bin/python` has RDKit 2025.09.5 (bundles InChI
  1.07.3), OpenBabel 3.1.0 and networkx. RDKit and OpenBabel crash if imported in one
  process; `toolkits.py` runs them in separate passes and calls `obabel` as a command.
- **CAS:** the Common Chemistry API needs a key from CAS. Records were read as web pages
  one at a time. Do not script the site without a key.
- **PubChem:** `inchi_known_issues.py` fetches SMILES by CID with `curl`; it needs
  network access.
- **Not kept:** `work.json` (regenerate with `toolkits.py rd1`), the copy of
  `KNOWNISSUES.pdf`, and the scripts behind the molecule drawings were in a temporary
  folder. The drawings themselves exist only in the chat.

## Sources

- Jacobs et al., "CAS Common Chemistry in 2021", J. Chem. Inf. Model. 2022, 62, 2737.
- Goodman, Pletnev, Thiessen, Bolton, Heller, "InChI version 1.06", J. Cheminform. 2021,
  13:40.
- InChI source and `INCHI-1-DOC/KNOWNISSUES.pdf`: github.com/IUPAC-InChI/InChI.
- McKay, "Practical graph isomorphism", Congressus Numerantium 30 (1981).
- Banković, Drecun, Marić, formalization of the McKay–Piperno scheme, LMCS 2023.
