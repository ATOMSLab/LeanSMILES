const cleanCmdField = (s = '') => String(s).replace(/[\t\r\n]/g, '')

export function explainParseError(constructorStr = '', message = '') {
  if (constructorStr.includes('ringAfterBranch ')) {
    return 'OpenSMILES §2.2 grammar requires ring-closure digits immediately after the atom (`atom ringbond* branch*`), before any branch `(...)`. Move the ring digit before the branch, e.g. `C1(C)CC1` instead of `C(C)1CC1`.'
  }
  if (constructorStr.includes('ringAfterBranchOpen')) {
    return 'A ring-closure digit cannot appear immediately after `(`. Attach it to an atom instead.'
  }
  if (constructorStr.includes('emptyBranch')) {
    return 'Empty branches `()` are invalid in OpenSMILES. Put at least one atom inside the parentheses.'
  }
  if (constructorStr.includes('unclosedBranch') || constructorStr.includes('unmatchedBranchClose')) {
    return 'Every opening parenthesis `(` for a branch must have a matching closing parenthesis `)`.'
  }
  if (constructorStr.includes('unclosedRing')) {
    return 'Every ring-closure digit must appear in pairs to open and close the cycle (e.g. `C1CCCCC1`).'
  }
  if (constructorStr.includes('conflictingRingBond')) {
    return 'OpenSMILES rejects conflicting bond symbols on the two ends of the same ring closure (e.g. `C=1CC-1`). Write the bond symbol on one end or use matching symbols.'
  }
  if (constructorStr.includes('selfBond')) {
    return 'A ring closure cannot connect an atom to itself (`src ≠ dst` is a type invariant of `Bond n`).'
  }
  if (constructorStr.includes('duplicateBond')) {
    return 'Two atoms cannot be joined by more than one bond (`nodup` invariant on `SimpleGraph (Fin n)`).'
  }
  if (constructorStr.includes('bondWithoutAtom')) {
    return 'A bond symbol (`-`, `=`, `#`, `$`, `:`) must sit between two atoms—never at the start, end, or twice in a row.'
  }
  if (constructorStr.includes('danglingDot')) {
    return 'The fragment separator `.` must separate two complete fragments and cannot appear at the start, end, or adjacent to parentheses.'
  }
  if (constructorStr.includes('badBracket')) {
    return 'Bracket atoms follow `[isotope? symbol chiral? hcount? charge? class?]` (OpenSMILES §3.1). Check hydrogen counts (single digit `H0`–`H9`), aromaticity, and class numbers.'
  }
  if (constructorStr.includes('unknownElement')) {
    return 'Unrecognized element symbol. Bare atoms must be in the organic subset (`B, C, N, O, P, S, F, Cl, Br, I, *`); all other 118 IUPAC elements must be written in brackets `[...]`.'
  }
  return `OpenSMILES syntax check failed: ${message}`
}

export const leanTemplates = {
  // The worker program itself is Worker.lean at the repository root, built by
  // `lake build worker`; the methods below write the request lines it reads.

  parseMolecule(smiles) {
    return `parse\t${cleanCmdField(smiles)}`
  },

  compareTanimoto(smilesA, smilesB) {
    return `tanimoto\t${cleanCmdField(smilesA)}\t${cleanCmdField(smilesB)}`
  },

  loadDataset(datasetId = 'delaney') {
    return `dataset\t${cleanCmdField(datasetId)}`
  },

  fitPipeline(tsvPath, modelType = 'sparse-ridge', alpha = '1.0', targetLabel = 'target') {
    return `fit\t${cleanCmdField(tsvPath)}\t${cleanCmdField(modelType)}\t${cleanCmdField(String(alpha))}\t${cleanCmdField(targetLabel)}`
  },
}
