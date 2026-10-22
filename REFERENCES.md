# References

This file credits the prior work LeanSMILES builds on: the code it adapts, the
datasets it ships, the course material it includes, and the literature on
molecular representations it formalizes. Each entry says what it is credited
for. BibTeX for every entry is in [`references.bib`](references.bib); the key
follows each entry.

## Lean and its libraries

- de Moura, L. & Ullrich, S. (2021), *The Lean 4 theorem prover and programming
  language*, Automated Deduction – CADE 28, LNCS 12699, 625–635.
  [doi:10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37).
  The language and proof assistant LeanSMILES is written in. `mouraLean4Theorem2021`
- The mathlib Community (2020), *The Lean mathematical library*, CPP 2020,
  367–381. [doi:10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824).
  Supplies `ℝ`, `Real.sqrt`, `Real.rpow`, `Finset.sum` and the tactics used in
  [`LeanSMILES/Scalar.lean`](LeanSMILES/Scalar.lean).
  `mathlibcommunityLeanMathematicalLibrary2020`
- The Lean Community, [*Batteries*](https://github.com/leanprover-community/batteries).
  Supplies the `Rat`-to-`Float` conversion behind the `RatEmbed Float`
  instance. `leanprovercommunityBatteries`

## Code adapted from other projects

- ATOMS Lab, *LeanCatalyst: Formally verified microkinetic modeling*
  ([repository](https://github.com/ATOMSLab/LeanCatalyst), private).
  [`LeanSMILES/Scalar.lean`](LeanSMILES/Scalar.lean) is extracted from
  `LeanCatalyst/Scalar.lean` at commit `65d1e87`, unchanged apart from the
  namespace and docstrings. `atomslabLeanCatalyst2026`
- Matemb, O., [*LeanBisection*](https://github.com/Oscario0/LeanBisection).
  LeanCatalyst credits this development as foundational input to its
  scalar-polymorphic design: generic code, a `Real` proof surface, and
  executable instantiations. `Scalar.lean` inherits that design.
  `matembLeanBisection2025`

## Formalizing chemistry in Lean

- Bobbin, M.P., Sharlin, S., Feyzishendi, P., Dang, A.H., Wraback, C.M. &
  Josephson, T.R. (2024), *Formalizing chemical physics using the Lean theorem
  prover*, Digital Discovery 3(2), 264–280.
  [doi:10.1039/D3DD00077J](https://doi.org/10.1039/D3DD00077J). ATOMS Lab's
  earlier work formalizing chemistry in Lean; LeanSMILES carries the approach
  to molecular representations. `bobbinFormalizingChemicalPhysics2024`

## Molecular representations

- Weininger, D. (1988), *SMILES, a chemical language and information system. 1.
  Introduction to methodology and encoding rules*, Journal of Chemical
  Information and Computer Sciences 28(1), 31–36.
  [doi:10.1021/ci00057a005](https://doi.org/10.1021/ci00057a005). The original
  definition of SMILES. `weiningerSMILESChemicalLanguage1988`
- Weininger, D., Weininger, A. & Weininger, J.L. (1989), *SMILES. 2. Algorithm
  for generation of unique SMILES notation*, Journal of Chemical Information and
  Computer Sciences 29(2), 97–101.
  [doi:10.1021/ci00062a008](https://doi.org/10.1021/ci00062a008). Canonical
  SMILES: one string per molecule. `weiningerSMILESAlgorithmGeneration1989`
- James, C.A. (2016), [*OpenSMILES specification*](http://opensmiles.org/opensmiles.html),
  version 1.0. The open, community-maintained grammar for SMILES, and the
  natural target for a formal grammar. `jamesOpenSMILESSpecification2016`
- Heller, S.R., McNaught, A., Pletnev, I., Stein, S. & Tchekhovskoi, D. (2015),
  *InChI, the IUPAC International Chemical Identifier*, Journal of
  Cheminformatics 7, 23.
  [doi:10.1186/s13321-015-0068-4](https://doi.org/10.1186/s13321-015-0068-4).
  A standard identifier with one canonical form, where canonical SMILES
  depends on the toolkit that writes it. `hellerInChIIUPACInternational2015`
- O'Boyle, N. & Dalke, A. (2018), *DeepSMILES: An adaptation of SMILES for use
  in machine-learning of chemical structures*, ChemRxiv.
  [doi:10.26434/chemrxiv.7097960.v1](https://doi.org/10.26434/chemrxiv.7097960.v1).
  A SMILES variant that removes the need to pair ring-closure digits and
  parentheses.
  `oboyleDeepSMILESAdaptationSMILES2018`
- Krenn, M., Häse, F., Nigam, A., Friederich, P. & Aspuru-Guzik, A. (2020),
  *Self-referencing embedded strings (SELFIES): A 100% robust molecular string
  representation*, Machine Learning: Science and Technology 1(4), 045024.
  [doi:10.1088/2632-2153/aba947](https://doi.org/10.1088/2632-2153/aba947).
  A string representation in which every string decodes to a valid molecule.
  `krennSelfreferencingEmbeddedStrings2020`
- Wigh, D.S., Goodman, J.M. & Lapkin, A.A. (2022), *A review of molecular
  representation in the age of machine learning*, WIREs Computational Molecular
  Science 12(5), e1603.
  [doi:10.1002/wcms.1603](https://doi.org/10.1002/wcms.1603). A survey of the
  representations above and their alternatives.
  `wighReviewMolecularRepresentation2022`

## Datasets

- [`datasets/delaney-processed.csv`](datasets/delaney-processed.csv), read by
  [`LeanSMILES/Data/CSVparser.lean`](LeanSMILES/Data/CSVparser.lean): measured
  aqueous solubilities and ESOL predictions for 1,128 compounds.
  - Delaney, J.S. (2004), *ESOL: Estimating aqueous solubility directly from
    molecular structure*, Journal of Chemical Information and Computer Sciences
    44(3), 1000–1005.
    [doi:10.1021/ci034243x](https://doi.org/10.1021/ci034243x). The source of
    the data and of the ESOL model. `delaneyESOLEstimatingAqueous2004`
  - Wu, Z., Ramsundar, B., Feinberg, E.N., Gomes, J., Geniesse, C., Pappu,
    A.S., Leswing, K. & Pande, V. (2018), *MoleculeNet: A benchmark for
    molecular machine learning*, Chemical Science 9(2), 513–530.
    [doi:10.1039/C7SC02664A](https://doi.org/10.1039/C7SC02664A). The benchmark
    that distributes this processed CSV as its ESOL set.
    `wuMoleculeNetBenchmarkMolecular2018`
- [`ench470-content/winequality-white.csv`](ench470-content/winequality-white.csv):
  physicochemical measurements and quality scores for white wines.
  - Cortez, P., Cerdeira, A., Almeida, F., Matos, T. & Reis, J. (2009),
    *Modeling wine preferences by data mining from physicochemical properties*,
    Decision Support Systems 47(4), 547–553.
    [doi:10.1016/j.dss.2009.05.016](https://doi.org/10.1016/j.dss.2009.05.016).
    `cortezModelingWinePreferences2009`
  - The same authors (2009), *Wine Quality*, UCI Machine Learning Repository.
    [doi:10.24432/C56S3T](https://doi.org/10.24432/C56S3T). `cortezWineQuality2009`
- [`ench470-content/Chembl_EGFR_actives_ML.csv`](ench470-content/Chembl_EGFR_actives_ML.csv),
  [`Chembl_EGFR_inactives_ML.csv`](ench470-content/Chembl_EGFR_inactives_ML.csv)
  and [`EGFR-FDA.csv`](ench470-content/EGFR-FDA.csv): 100 EGFR actives, 100
  inactives, and SMILES for five FDA-approved EGFR inhibitors (gefitinib,
  erlotinib, lapatinib, afatinib, osimertinib). All three are byte-identical
  copies of files from TeachOpenCADD's original introductory notebooks;
  `EGFR-FDA.csv` is their `EGFR-course.csv` renamed. Those notebooks describe
  the actives and inactives as ChEMBL IC50 data but record no ChEMBL release
  or activity cutoff, and give the FDA list no source beyond the label "FDA
  approved EGFR inhibitors". No primary source is known for that list.
  - Volkamer, A. (2018), *TeachOpenCADD introductory notebooks*,
    [`introductory_notebooks/data/`](https://github.com/volkamerlab/teachopencadd/tree/bf80aae857f52446dac7f251bd3aef17def32d35/introductory_notebooks/data)
    at commit `bf80aae` (2018-11-09). The direct source of all three files.
    The folder was deleted from the repository in July 2020 (`0c34266`), so
    the link pins the commit. `volkamerTeachOpenCADDIntroductoryNotebooks2018`
  - Gaulton, A. et al. (2012), *ChEMBL: a large-scale bioactivity database for
    drug discovery*, Nucleic Acids Research 40(D1), D1100–D1107.
    [doi:10.1093/nar/gkr777](https://doi.org/10.1093/nar/gkr777). The founding
    ChEMBL paper. `gaultonChEMBLLargescaleBioactivity2012`
  - Zdrazil, B. et al. (2024), *The ChEMBL Database in 2023: a drug discovery
    platform spanning multiple bioactivity data types and time periods*,
    Nucleic Acids Research 52(D1), D1180–D1192.
    [doi:10.1093/nar/gkad1004](https://doi.org/10.1093/nar/gkad1004). A
    recent ChEMBL update. `zdrazilChEMBLDatabase20232024`
- [`ench470-content/ThermoProperties.csv`](ench470-content/ThermoProperties.csv):
  molecular weight, critical temperature, acentric factor and boiling point for
  6,031 compounds.
  - Joss, L. & Müller, E.A. (2019), *Machine learning for fluid property
    correlations: Classroom examples with MATLAB*, Journal of Chemical
    Education 96(4), 697–703.
    [doi:10.1021/acs.jchemed.8b00692](https://doi.org/10.1021/acs.jchemed.8b00692).
    The source of the data. `jossMachineLearningFluid2019`
  - [`ThermoPropertiesSMILES.csv`](ench470-content/ThermoPropertiesSMILES.csv)
    adds SMILES generated by Samiha Sharlin, who looked up each compound by
    name with the code in the Lecture 18 notebook (that notebook's
    extra-credit problem). The isomeric SMILES come from the NCI/CADD Chemical
    Identifier Resolver and the canonical SMILES from PubChem (see Software).
    "Did not work" marks a failed lookup.

## Teaching material

- Josephson, T.R. (2021), *ENCH 470 course materials*, University of Maryland,
  Baltimore County, Fall 2021. The notebooks and data in
  [`ench470-content/`](ench470-content/). `josephsonENCH470CourseMaterials2021`
- Sydow, D., Morger, A., Driller, M. & Volkamer, A. (2019), *TeachOpenCADD: a
  teaching platform for computer-aided drug design using open source packages
  and data*, Journal of Cheminformatics 11, 29.
  [doi:10.1186/s13321-019-0351-x](https://doi.org/10.1186/s13321-019-0351-x).
  The Lecture 21 notebook is adapted from Andrea Volkamer's
  [TeachOpenCADD](https://github.com/volkamerlab/teachopencadd) material.
  `sydowTeachOpenCADDTeachingPlatform2019`
- Sydow, D. et al. (2022), *TeachOpenCADD 2022: open source and FAIR Python
  pipelines to assist in structural bioinformatics and cheminformatics
  research*, Nucleic Acids Research 50(W1), W753–W760.
  [doi:10.1093/nar/gkac267](https://doi.org/10.1093/nar/gkac267). The 2022
  update of TeachOpenCADD. `sydowTeachOpenCADD2022Open2022`

## Methods used in the course notebooks

- Morgan, H.L. (1965), *The generation of a unique machine description for
  chemical structures—a technique developed at Chemical Abstracts Service*,
  Journal of Chemical Documentation 5(2), 107–113.
  [doi:10.1021/c160017a018](https://doi.org/10.1021/c160017a018). The atom
  neighborhood algorithm behind Morgan fingerprints.
  `morganGenerationUniqueMachine1965`
- Rogers, D. & Hahn, M. (2010), *Extended-connectivity fingerprints*, Journal of
  Chemical Information and Modeling 50(5), 742–754.
  [doi:10.1021/ci100050t](https://doi.org/10.1021/ci100050t). ECFP, the
  circular fingerprints RDKit's Morgan fingerprints follow.
  `rogersExtendedConnectivityFingerprints2010`
- Rogers, D.J. & Tanimoto, T.T. (1960), *A computer program for classifying
  plants*, Science 132(3434), 1115–1118.
  [doi:10.1126/science.132.3434.1115](https://doi.org/10.1126/science.132.3434.1115).
  An early published source for the Tanimoto coefficient.
  `rogersComputerProgramClassifying1960`
- Bajusz, D., Rácz, A. & Héberger, K. (2015), *Why is Tanimoto index an
  appropriate choice for fingerprint-based similarity calculations?*, Journal of
  Cheminformatics 7, 20.
  [doi:10.1186/s13321-015-0069-3](https://doi.org/10.1186/s13321-015-0069-3).
  `bajuszWhyTanimotoIndex2015`
- Landrum, G. (2018), [*Using the new fingerprint bit rendering
  code*](http://rdkit.blogspot.com/2018/10/using-new-fingerprint-bit-rendering-code.html),
  RDKit Blog. The guide Lecture 18 follows for drawing fingerprint bits.
  `landrumUsingNewFingerprint2018`
- Tibshirani, R. (1996), *Regression shrinkage and selection via the lasso*,
  Journal of the Royal Statistical Society Series B 58(1), 267–288.
  [doi:10.1111/j.2517-6161.1996.tb02080.x](https://doi.org/10.1111/j.2517-6161.1996.tb02080.x).
  LASSO, used in the ML mini-project. `tibshiraniRegressionShrinkageSelection1996`
- Singh, K.P. & Gupta, S. (2012), *Artificial intelligence based modeling for
  predicting the disinfection by-products in water*, Chemometrics and
  Intelligent Laboratory Systems 114, 122–131.
  [doi:10.1016/j.chemolab.2012.03.014](https://doi.org/10.1016/j.chemolab.2012.03.014).
  Cited in the ML mini-project's regression example.
  `singhArtificialIntelligenceBased2012`

## Software and services used by the course notebooks

- [RDKit](https://www.rdkit.org), open-source cheminformatics.
  [doi:10.5281/zenodo.591637](https://doi.org/10.5281/zenodo.591637).
  `landrumRDKitOpensourceCheminformatics`
- Kim, S. et al. (2025), *PubChem 2025 update*, Nucleic Acids Research 53(D1),
  D1516–D1525. [doi:10.1093/nar/gkae1059](https://doi.org/10.1093/nar/gkae1059).
  `kimPubChem2025Update2025`
- Swain, M., [*PubChemPy*](https://github.com/mcs07/PubChemPy), the Python
  client Lecture 18 uses to query PubChem. `swainPubChemPy`
- NCI/CADD Group, [*Chemical Identifier
  Resolver*](https://cactus.nci.nih.gov/chemical/structure), the name-to-SMILES
  service Lecture 18 uses. `nciCADDChemicalIdentifierResolver`
- Pedregosa, F. et al. (2011), *Scikit-learn: Machine learning in Python*,
  Journal of Machine Learning Research 12, 2825–2830.
  [jmlr.org](https://jmlr.org/papers/v12/pedregosa11a.html).
  `pedregosaScikitlearnMachineLearning2011`
- McKinney, W. (2010), *Data structures for statistical computing in Python*,
  Proceedings of the 9th Python in Science Conference, 56–61.
  [doi:10.25080/Majora-92bf1922-00a](https://doi.org/10.25080/Majora-92bf1922-00a).
  pandas. `mckinneyDataStructuresStatistical2010`
- Harris, C.R. et al. (2020), *Array programming with NumPy*, Nature 585,
  357–362. [doi:10.1038/s41586-020-2649-2](https://doi.org/10.1038/s41586-020-2649-2).
  `harrisArrayProgrammingNumPy2020`
- Hunter, J.D. (2007), *Matplotlib: A 2D graphics environment*, Computing in
  Science & Engineering 9(3), 90–95.
  [doi:10.1109/MCSE.2007.55](https://doi.org/10.1109/MCSE.2007.55).
  `hunterMatplotlib2DGraphics2007`
- Waskom, M. (2021), *seaborn: statistical data visualization*, Journal of Open
  Source Software 6(60), 3021.
  [doi:10.21105/joss.03021](https://doi.org/10.21105/joss.03021).
  `waskomSeabornStatisticalData2021`
- Plotly Technologies Inc., [*Plotly Python graphing
  library*](https://plotly.com/python/). `plotlyPlotlyPythonGraphing`
- Kluyver, T. et al. (2016), *Jupyter Notebooks—a publishing format for
  reproducible computational workflows*, in *Positioning and Power in Academic
  Publishing*, IOS Press, 87–90.
  [doi:10.3233/978-1-61499-649-1-87](https://doi.org/10.3233/978-1-61499-649-1-87).
  `kluyverJupyterNotebooksPublishing2016`

## Adding a reference

1. Add the entry under the section it belongs to here, saying what LeanSMILES
   uses it for, with its key at the end.
2. Add the BibTeX to [`references.bib`](references.bib), in the same section
   order. Take the details from the DOI registry, not from memory:
   ```bash
   curl -sL -H "Accept: application/x-bibtex" https://doi.org/<DOI>
   ```
3. Name the key `authorFirstThreeWordsYear`, as in the entries above.
4. When code is adapted from another project, also name the source, and the
   commit if there is one, in the adapted file's module docstring, as
   [`Scalar.lean`](LeanSMILES/Scalar.lean) does.
