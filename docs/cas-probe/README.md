# What CAS's published strings reveal (probe of 2026-11-16)

A black-box look at the structure strings CAS publishes on
[CAS Common Chemistry](https://commonchemistry.cas.org), on 65 records chosen to be hard:
high symmetry, awkward resonance, metals, radicals, isotopes, and families of
stereoisomers. The same molecules were run through RDKit 2025.09.5, OpenBabel 3.1.0 and
LeanSMILES (the `worker` binary built 2026-10-28 in the main checkout; source at HEAD is
a week newer, so the LeanSMILES results need a rebuild to confirm).

CAS data here is © CAS, licensed CC BY-NC 4.0 (attribution, **non-commercial**).

## What you can see from outside

- A record shows up to **two** strings plus an InChI and InChIKey: `Canonical SMILES`
  (no stereo, no isotopes) and, only when the record has tetrahedral or double-bond
  stereo, `SMILES`. They are stored values. Searching by SMILES is a lookup, not a
  canonicalizer you can feed variants to.
- The two strings come from **different writers**: different atom order and different
  style (`O=C(O)C(N)C` vs `[C@@H](C(O)=O)(C)N` for L-alanine).
- CAS's own paper (Jacobs et al., *J. Chem. Inf. Model.* 2022, 62, 2737) says the
  authoritative record is in a proprietary encoding and that the exported forms "have the
  potential to be flawed". **These strings are an export layer, not the registry.**
- The public API now needs a key from CAS. The records here were read as web pages, one
  at a time, and typed into `cas.tsv`. Every string was checked by recomputing the
  InChIKey printed on the same record (RDKit, and OpenBabel where RDKit refuses).

## Defects found in the published strings

| What | Evidence |
|---|---|
| A string that denotes the wrong substance | Ozone `10028-15-6` has SMILES `O`, which is water. No InChI on the record. |
| Different substances, identical strings | Water, heavy water and ozone all `O`. Cisplatin and transplatin: same SMILES, same InChIKey. (R)-, (S)- and racemic BINOL: same SMILES, same InChIKey. D-chiro-inositol is identical to unspecified inositol (no stereo anywhere on the record). |
| Isotopes never written | Benzene-d6 is `C=1C=CC=CC1`; D₂O is `O`. The InChI carries the isotope layer, no SMILES does. |
| Stereo dropped by the "isomeric" writer | Esomeprazole: InChI has the sulfoxide centre (`/t24-/m0/s1`), the `SMILES` field has no stereo mark at all. |
| No structure string at all | TEMPO, nitric oxide (radicals), tropylium tetrafluoroborate (delocalized cation), P₄, trans-cyclooctene. |
| Valence conventions are inconsistent | Pentavalent N for nitro, pyridine N-oxide and trimethylamine oxide (`O=N(C)(C)C`), but charge-separated for azide, diazomethane, sydnone and CO. `[C-]#[O+]` for CO alone, neutral `C#O` inside Ni(CO)₄. |
| Strings a strict parser refuses | RDKit rejects 4 of 70: cisplatin, transplatin (`[Cl-]` with a bond), Ni(CO)₄, diborane (`[H]` with two bonds). OpenBabel and LeanSMILES accept all 70. |
| SMILES and InChI disagree on the graph | Ferrocene: the SMILES bonds Fe to ten carbons, the InChI on the same record has three disconnected pieces. Same pattern for MeMgBr and NaCp. |
| Mixed InChI flavours | Six records (both inositols, both HCH isomers, both decalins) print non-standard `InChI=1/…` with keys ending `NA-N`. A full-key join against any standard-InChI database cannot match those. |

## What did *not* show a defect

- **Graph canonicalization.** Across every stereoisomer family (alanines, inositols,
  hexachlorocyclohexanes, decalins, BINOLs, omeprazoles) the `Canonical SMILES` is the same
  string for every member. Nothing here shows it depending on how the record was drawn.
- **Kekulé structures.** Every Kekulé string, including C60, kekulene and
  hexabenzocoronene, reproduces the record's InChIKey.
- Two hypotheses I raised and killed: that kekulene's string had carbons without a double
  bond (misread by eye), and that CAS's InChIKeys for cyclooctatetraene/annulenes depend
  on which Kekulé structure was drawn (they don't; both drawings give the same key).

One suggestive but unproven signal about the registry itself: "Deleted or Replaced CAS
RNs" counts. 3-Phenylsydnone (mesoionic) has 10, two of them minted in the last couple of
years; C60 has 18; tropylium BF₄ 10; cubane, adamantane, triphenylene, azulene have 0.
That is what repeated re-registration of a hard-to-normalize structure would look like,
but the paper gives other causes (trade-name registrations), and famous compounds
collect them anyway (CO has 12). Treat as a lead, not a finding.

## The same tests on RDKit, OpenBabel and LeanSMILES

200 random atom orderings per molecule for the toolkits, 25 for LeanSMILES (6 for the
eight largest).

| | RDKit | OpenBabel | LeanSMILES |
|---|---|---|---|
| Constitution only (62 molecules incl. cubane, dodecahedrane, C60, kekulene, bullvalene) | 1 string each | 1 string each | 1 string each (C60 ≈ 5 s per ordering) |
| scyllo-inositol | **2 strings** | **2 strings** | **8 strings** |
| myo-inositol | 1 | 1 | **9 strings** |
| alanine, tartaric acids, 1,4-dimethylcyclohexanes | 1 | 1 | **2–3 strings** |
| esomeprazole | 1 | **2 strings** | **2 strings** |
| cis/trans-cyclooctene | **2 strings** each | 1 (stereo dropped) | 1 (stereo dropped) |
| diborane | rejected | accepted | accepted |

RDKit and OpenBabel also disagree on what is aromatic for P₄, porphine, phthalocyanine,
borazine, squaric acid and [18]annulene (`toolkits.tsv`, columns `rd_arom`, `ob_arom`).

Three things LeanSMILES does today that would sink a "ours is better" pitch:

1. **Tetrahedral stereo is carried as a label, not as geometry.** `C[C@H](N)C(O)=O` and
   `N[C@@H](C)C(O)=O` are both L-alanine; LeanSMILES returns `C[C@H](N)C(=O)O` for the
   first and `C[C@@H](N)C(=O)O`, D-alanine's string, for the second. The canonicity
   theorem is about relabeling atoms of one `Molecule`; it says nothing about two
   writings of the same stereocentre, and the `@` mark is not re-derived for the new
   neighbour order.
2. **Double-bond stereo is dropped.** Maleic and fumaric acid both give
   `O=C(O)C=CC(=O)O`. CAS's `SMILES` field does better.
3. **Aromatized output loses the hydrogen on an unbracketed N.** `C1=CNC=C1` (pyrrole,
   written the way CAS writes it) aromatizes to `c1ccnc1`; `c1cc[nH]c1` stays
   `c1cc[nH]c1`. Same molecule, two "canonical" strings, and the first is one RDKit
   cannot read. `Perceive.lean:239–241` keeps that H implicit, so I expect it at HEAD too.

Where LeanSMILES is ahead of CAS's strings on this panel: isotopes are kept, and the
constitution result is a theorem rather than an observation.

## Files

| File | What |
|---|---|
| `panel.tsv` | the 81 molecules, with registry numbers and reference SMILES |
| `cas.tsv` | 65 CAS records as transcribed: name, formula, InChIKey, both strings, replaced-RN count |
| `check_cas.py`, `check_cas.out` | coverage, parse, self-consistency and same-string checks on `cas.tsv` |
| `toolkits.py`, `toolkits.tsv` | RDKit vs OpenBabel: canonical strings, aromatic-atom counts, stability under reordering |
| `lean_check.py`, `lean_stable.out` | LeanSMILES on CAS's strings and under reordering |

```bash
PY=~/miniforge3/envs/rmg_env/bin/python
$PY docs/cas-probe/check_cas.py docs/cas-probe/cas.tsv
$PY docs/cas-probe/toolkits.py rd1 docs/cas-probe/panel.tsv /tmp/work.json 200
$PY docs/cas-probe/toolkits.py ob  /tmp/work.json
$PY docs/cas-probe/toolkits.py rd2 /tmp/work.json > docs/cas-probe/toolkits.tsv
$PY docs/cas-probe/lean_check.py stable .lake/build/bin/worker /tmp/work.json 25
```

## Limits

- 65 records out of roughly 500 000 public ones, picked by hand to be nasty. These are
  existence proofs, not rates.
- cis-Cyclooctene and maleic acid pages came back empty and were not retried.
- I could not identify the writer behind `Canonical SMILES`. Its style (Kekulé, ring
  digits never reused, bond symbol before the ring-opening digit) is also LeanSMILES's
  own style, so it is not a fingerprint of any one toolkit. No Java here, so CDK was not
  tested directly.
