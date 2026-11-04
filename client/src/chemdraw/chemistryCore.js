// 2D Molecular Graph Geometry & OpenSMILES / V2000 Serializer for LeanSMILES
// All chemical verification (OpenSMILES syntax, formal charge shell bounds,
// covalent/hypervalent valence rules, Kekulé matching, Hückel 4n+2 aromaticity,
// canonical numbering, and Morgan ECFP fingerprints) is executed in Lean 4
// by `Worker.lean`. This module handles ONLY 2D canvas geometry, superatom
// template expansion, and raw graph-to-SMILES / V2000 serialization.

export const ELEMENT_SYMBOLS = [
  'H', 'He', 'Li', 'Be', 'B', 'C', 'N', 'O', 'F', 'Ne',
  'Na', 'Mg', 'Al', 'Si', 'P', 'S', 'Cl', 'Ar', 'K', 'Ca',
  'Sc', 'Ti', 'V', 'Cr', 'Mn', 'Fe', 'Co', 'Ni', 'Cu', 'Zn',
  'Ga', 'Ge', 'As', 'Se', 'Br', 'Kr', 'Rb', 'Sr', 'Y', 'Zr',
  'Nb', 'Mo', 'Tc', 'Ru', 'Rh', 'Pd', 'Ag', 'Cd', 'In', 'Sn',
  'Sb', 'Te', 'I', 'Xe', 'Cs', 'Ba', 'La', 'Ce', 'Pr', 'Nd',
  'Pm', 'Sm', 'Eu', 'Gd', 'Tb', 'Dy', 'Ho', 'Er', 'Tm', 'Yb',
  'Lu', 'Hf', 'Ta', 'W', 'Re', 'Os', 'Ir', 'Pt', 'Au', 'Hg',
  'Tl', 'Pb', 'Bi', 'Po', 'At', 'Rn', 'Fr', 'Ra', 'Ac', 'Th',
  'Pa', 'U', 'Np', 'Pu', 'Am', 'Cm', 'Bk', 'Cf', 'Es', 'Fm',
  'Md', 'No', 'Lr', 'Rf', 'Db', 'Sg', 'Bh', 'Hs', 'Mt', 'Ds',
  'Rg', 'Cn', 'Nh', 'Fl', 'Mc', 'Lv', 'Ts', 'Og',
]

const ELEMENT_BY_LOWER = new Map(ELEMENT_SYMBOLS.map((s) => [s.toLowerCase(), s]))
const ELEMENT_SET = new Set(ELEMENT_SYMBOLS)

// Two-letter uppercase strings that spell common organic functional groups rather than
// transition/superheavy elements (Nh, Co, Cn, Ho, Hs, Bh, Fl, Mc, Pm, Cf, Po).
const FORMULA_TWO_LETTER_LABELS = new Set([
  'NH', 'CO', 'CN', 'OH', 'SH', 'BH', 'CH', 'PH', 'FH', 'CF', 'PO',
])

const SMILES_ORGANIC_SUBSET = new Set(['B', 'C', 'N', 'O', 'P', 'S', 'F', 'Cl', 'Br', 'I'])
const SMILES_AROMATIC_SUBSET = new Set(['B', 'C', 'N', 'O', 'P', 'S'])

// Superatom / functional-group templates expanded into explicit atoms & bonds before Lean 4 parsing
export const ABBREVIATIONS = [
  {
    label: 'OH', aliases: ['HO'], name: 'hydroxyl', formula: 'OH', attachmentCount: 1,
    atoms: [{ element: 'O', hydrogens: 1, x: 0, y: 0 }],
    bonds: [],
  },
  {
    label: 'NH2', aliases: ['H2N'], name: 'amino', formula: 'NH2', attachmentCount: 1,
    atoms: [{ element: 'N', hydrogens: 2, x: 0, y: 0 }],
    bonds: [],
  },
  {
    label: 'SH', aliases: ['HS'], name: 'thiol', formula: 'SH', attachmentCount: 1,
    atoms: [{ element: 'S', hydrogens: 1, x: 0, y: 0 }],
    bonds: [],
  },
  {
    label: 'Me', aliases: ['CH3', 'H3C'], name: 'methyl', formula: 'CH3', attachmentCount: 1,
    atoms: [{ element: 'C', hydrogens: 3, x: 0, y: 0 }],
    bonds: [],
  },
  {
    label: 'Et', aliases: ['C2H5'], name: 'ethyl', formula: 'C2H5', attachmentCount: 1,
    atoms: [
      { element: 'C', hydrogens: 2, x: 0, y: 0 },
      { element: 'C', hydrogens: 3, x: 0.5, y: -0.866 },
    ],
    bonds: [[0, 1, 'single']],
  },
  {
    label: 'nPr', aliases: [], bondedSpellings: ['Pr'], name: 'n-propyl', formula: 'C3H7', attachmentCount: 1,
    atoms: [
      { element: 'C', hydrogens: 2, x: 0, y: 0 },
      { element: 'C', hydrogens: 2, x: 0.5, y: -0.866 },
      { element: 'C', hydrogens: 3, x: 1.5, y: -0.866 },
    ],
    bonds: [[0, 1, 'single'], [1, 2, 'single']],
  },
  {
    label: 'iPr', aliases: [], name: 'isopropyl', formula: 'C3H7', attachmentCount: 1,
    atoms: [
      { element: 'C', hydrogens: 1, x: 0, y: 0 },
      { element: 'C', hydrogens: 3, x: 0.5, y: -0.866 },
      { element: 'C', hydrogens: 3, x: 0.5, y: 0.866 },
    ],
    bonds: [[0, 1, 'single'], [0, 2, 'single']],
  },
  {
    label: 'tBu', aliases: [], name: 'tert-butyl', formula: 'C4H9', attachmentCount: 1,
    atoms: [
      { element: 'C', hydrogens: 0, x: 0, y: 0 },
      { element: 'C', hydrogens: 3, x: 1, y: 0 },
      { element: 'C', hydrogens: 3, x: 0, y: -1 },
      { element: 'C', hydrogens: 3, x: 0, y: 1 },
    ],
    bonds: [[0, 1, 'single'], [0, 2, 'single'], [0, 3, 'single']],
  },
  {
    label: 'Ph', aliases: ['C6H5'], name: 'phenyl', formula: 'C6H5', attachmentCount: 1,
    atoms: [
      { element: 'C', hydrogens: 0, x: 0, y: 0 },
      { element: 'C', hydrogens: 1, x: 0.5, y: 0.866 },
      { element: 'C', hydrogens: 1, x: 1.5, y: 0.866 },
      { element: 'C', hydrogens: 1, x: 2, y: 0 },
      { element: 'C', hydrogens: 1, x: 1.5, y: -0.866 },
      { element: 'C', hydrogens: 1, x: 0.5, y: -0.866 },
    ],
    bonds: [
      [0, 1, 'double'], [1, 2, 'single'], [2, 3, 'double'],
      [3, 4, 'single'], [4, 5, 'double'], [5, 0, 'single'],
    ],
  },
  {
    label: 'COMe', aliases: ['MeCO', 'Ac'], bondedSpellings: ['Ac'], name: 'acetyl', formula: 'C2H3O', attachmentCount: 1,
    atoms: [
      { element: 'C', hydrogens: 0, x: 0, y: 0 },
      { element: 'C', hydrogens: 3, x: 0.5, y: -0.866 },
      { element: 'O', hydrogens: 0, x: 0.5, y: 0.866 },
    ],
    bonds: [[0, 1, 'single'], [0, 2, 'double']],
  },
  {
    label: 'OMe', aliases: ['MeO', 'OCH3'], name: 'methoxy', formula: 'CH3O', attachmentCount: 1,
    atoms: [
      { element: 'O', hydrogens: 0, x: 0, y: 0 },
      { element: 'C', hydrogens: 3, x: 0.5, y: -0.866 },
    ],
    bonds: [[0, 1, 'single']],
  },
  {
    label: 'OEt', aliases: ['EtO'], name: 'ethoxy', formula: 'C2H5O', attachmentCount: 1,
    atoms: [
      { element: 'O', hydrogens: 0, x: 0, y: 0 },
      { element: 'C', hydrogens: 2, x: 0.5, y: -0.866 },
      { element: 'C', hydrogens: 3, x: 1.5, y: -0.866 },
    ],
    bonds: [[0, 1, 'single'], [1, 2, 'single']],
  },
  {
    label: 'OAc', aliases: ['AcO'], name: 'acetoxy', formula: 'C2H3O2', attachmentCount: 1,
    atoms: [
      { element: 'O', hydrogens: 0, x: 0, y: 0 },
      { element: 'C', hydrogens: 0, x: 0.5, y: -0.866 },
      { element: 'C', hydrogens: 3, x: 1.5, y: -0.866 },
      { element: 'O', hydrogens: 0, x: 0, y: -1.732 },
    ],
    bonds: [[0, 1, 'single'], [1, 2, 'single'], [1, 3, 'double']],
  },
  {
    label: 'CO2H', aliases: ['COOH', 'HO2C', 'HOOC'], name: 'carboxy', formula: 'CHO2', attachmentCount: 1,
    atoms: [
      { element: 'C', hydrogens: 0, x: 0, y: 0 },
      { element: 'O', hydrogens: 0, x: 0.5, y: 0.866 },
      { element: 'O', hydrogens: 1, x: 0.5, y: -0.866 },
    ],
    bonds: [[0, 1, 'double'], [0, 2, 'single']],
  },
  {
    label: 'CO2Me', aliases: ['COOMe', 'MeO2C'], name: 'methoxycarbonyl', formula: 'C2H3O2', attachmentCount: 1,
    atoms: [
      { element: 'C', hydrogens: 0, x: 0, y: 0 },
      { element: 'O', hydrogens: 0, x: 0.5, y: 0.866 },
      { element: 'O', hydrogens: 0, x: 0.5, y: -0.866 },
      { element: 'C', hydrogens: 3, x: 1.5, y: -0.866 },
    ],
    bonds: [[0, 1, 'double'], [0, 2, 'single'], [2, 3, 'single']],
  },
  {
    label: 'CHO', aliases: ['OHC'], name: 'formyl', formula: 'CHO', attachmentCount: 1,
    atoms: [
      { element: 'C', hydrogens: 1, x: 0, y: 0 },
      { element: 'O', hydrogens: 0, x: 0.5, y: -0.866 },
    ],
    bonds: [[0, 1, 'double']],
  },
  {
    label: 'CN', aliases: ['NC'], name: 'cyano', formula: 'CN', attachmentCount: 1,
    atoms: [
      { element: 'C', hydrogens: 0, x: 0, y: 0 },
      { element: 'N', hydrogens: 0, x: 1, y: 0 },
    ],
    bonds: [[0, 1, 'triple']],
  },
  {
    label: 'CF3', aliases: ['F3C'], name: 'trifluoromethyl', formula: 'CF3', attachmentCount: 1,
    atoms: [
      { element: 'C', hydrogens: 0, x: 0, y: 0 },
      { element: 'F', hydrogens: 0, x: 1, y: 0 },
      { element: 'F', hydrogens: 0, x: 0, y: -1 },
      { element: 'F', hydrogens: 0, x: 0, y: 1 },
    ],
    bonds: [[0, 1, 'single'], [0, 2, 'single'], [0, 3, 'single']],
  },
  {
    label: 'NO2', aliases: ['O2N'], name: 'nitro', formula: 'NO2', attachmentCount: 1,
    atoms: [
      { element: 'N', hydrogens: 0, charge: 1, x: 0, y: 0 },
      { element: 'O', hydrogens: 0, x: 0.5, y: 0.866 },
      { element: 'O', hydrogens: 0, charge: -1, x: 0.5, y: -0.866 },
    ],
    bonds: [[0, 1, 'double'], [0, 2, 'single']],
  },
  {
    label: 'Boc', aliases: [], name: 'tert-butoxycarbonyl', formula: 'C5H9O2', attachmentCount: 1,
    atoms: [
      { element: 'C', hydrogens: 0, x: 0, y: 0 },
      { element: 'O', hydrogens: 0, x: 0.5, y: 0.866 },
      { element: 'O', hydrogens: 0, x: 0.5, y: -0.866 },
      { element: 'C', hydrogens: 0, x: 1.5, y: -0.866 },
      { element: 'C', hydrogens: 3, x: 1.5, y: -1.866 },
      { element: 'C', hydrogens: 3, x: 1.5, y: 0.134 },
      { element: 'C', hydrogens: 3, x: 2.5, y: -0.866 },
    ],
    bonds: [
      [0, 1, 'double'], [0, 2, 'single'], [2, 3, 'single'],
      [3, 4, 'single'], [3, 5, 'single'], [3, 6, 'single'],
    ],
  },
  {
    label: 'TMS', aliases: [], name: 'trimethylsilyl', formula: 'C3H9Si', attachmentCount: 1,
    atoms: [
      { element: 'Si', hydrogens: 0, x: 0, y: 0 },
      { element: 'C', hydrogens: 3, x: 1, y: 0 },
      { element: 'C', hydrogens: 3, x: 0, y: -1 },
      { element: 'C', hydrogens: 3, x: 0, y: 1 },
    ],
    bonds: [[0, 1, 'single'], [0, 2, 'single'], [0, 3, 'single']],
  },
  {
    label: 'Tos', aliases: ['Ts'], bondedSpellings: ['Ts'], name: 'tosyl', formula: 'C7H7O2S', attachmentCount: 1,
    atoms: [
      { element: 'S', hydrogens: 0, x: 0, y: 0 },
      { element: 'O', hydrogens: 0, x: 0, y: -1 },
      { element: 'O', hydrogens: 0, x: 0, y: 1 },
      { element: 'C', hydrogens: 0, x: 1, y: 0 },
      { element: 'C', hydrogens: 1, x: 1.5, y: 0.866 },
      { element: 'C', hydrogens: 1, x: 2.5, y: 0.866 },
      { element: 'C', hydrogens: 0, x: 3, y: 0 },
      { element: 'C', hydrogens: 3, x: 4, y: 0 },
      { element: 'C', hydrogens: 1, x: 2.5, y: -0.866 },
      { element: 'C', hydrogens: 1, x: 1.5, y: -0.866 },
    ],
    bonds: [
      [0, 1, 'double'], [0, 2, 'double'], [0, 3, 'single'],
      [3, 4, 'double'], [4, 5, 'single'], [5, 6, 'double'],
      [6, 7, 'single'], [6, 8, 'single'], [8, 9, 'double'], [9, 3, 'single'],
    ],
  },
]

const ABBREV_BY_KEY = new Map()
const ABBREV_BY_LOWER = new Map()
for (const entry of ABBREVIATIONS) {
  for (const key of [entry.label, ...(entry.aliases || [])]) {
    ABBREV_BY_KEY.set(key, entry)
    ABBREV_BY_LOWER.set(key.toLowerCase(), entry)
  }
}

export function lookupAbbreviation(rawLabel) {
  const sym = (rawLabel || '').trim()
  return ABBREV_BY_KEY.get(sym) || null
}

// Parse simple condensed single-heavy-atom labels like NH, NH2, OH, SH, CH3, PH2
function parseSingleHeavyHydride(rawLabel) {
  const sym = (rawLabel || '').trim()
  const m =
    sym.match(/^(Cl|Br|Si|Se|As|B|C|N|O|P|S|F|I)H(\d*)$/) ||
    sym.match(/^H(\d*)(Cl|Br|Si|Se|As|B|C|N|O|P|S|F|I)$/)
  if (!m) return null
  if (/^(Cl|Br|Si|Se|As|B|C|N|O|P|S|F|I)/.test(sym)) {
    return { element: m[1], hydrogens: m[2] ? Number(m[2]) : 1 }
  }
  return { element: m[2], hydrogens: m[1] ? Number(m[1]) : 1 }
}

export function elementFromAtomLabel(rawLabel) {
  const sym = (rawLabel || '').trim()
  if (!sym) return null
  if (sym === 'D' || sym === 'T') return 'H'
  if (FORMULA_TWO_LETTER_LABELS.has(sym.toUpperCase())) return null
  if (ELEMENT_SET.has(sym)) return sym
  return null
}

// Normalize user-typed inline atom or functional group label
export function normalizeAtomLabel(raw) {
  const trimmed = (raw || '').trim()
  if (!trimmed) return 'C'
  if (ABBREV_BY_KEY.has(trimmed)) return trimmed
  const lowerAbbrev = ABBREV_BY_LOWER.get(trimmed.toLowerCase())
  if (lowerAbbrev) return lowerAbbrev.label
  if (FORMULA_TWO_LETTER_LABELS.has(trimmed.toUpperCase())) return trimmed.toUpperCase()
  const el = ELEMENT_BY_LOWER.get(trimmed.toLowerCase())
  if (el) return el
  return trimmed
}

// Expand superatom abbreviations into explicit atoms & bonds while keeping `parentAtomId`
// so every expanded vertex in Lean 4 (`Fin n`) maps back to its drawn canvas atom.
export function expandLabelGroups(drawnAtoms, drawnBonds) {
  const nextAtoms = []
  const nextBonds = [...drawnBonds]
  const expandedNames = []

  const degreeByAtom = new Map(drawnAtoms.map((a) => [a.id, 0]))
  for (const b of drawnBonds) {
    degreeByAtom.set(b.fromAtomId, (degreeByAtom.get(b.fromAtomId) || 0) + 1)
    degreeByAtom.set(b.toAtomId, (degreeByAtom.get(b.toAtomId) || 0) + 1)
  }

  for (const atom of drawnAtoms) {
    const abbrev = lookupAbbreviation(atom.element)
    const degree = degreeByAtom.get(atom.id) || 0
    // Single-atom hydrides (OH, NH2, SH, Me) with 1 attachment bond can stay compact on the
    // 1-to-1 vertex index map; multi-atom superatoms (OMe, NO2, CO2H, Ph, Boc, etc.) expand
    // when their attachment degree matches.
    if (
      !abbrev ||
      abbrev.atoms.length <= 1 ||
      (degree > 0 && degree !== abbrev.attachmentCount) ||
      (atom.formalCharge || 0) !== 0
    ) {
      nextAtoms.push({ ...atom, parentAtomId: atom.id })
      continue
    }

    expandedNames.push(`${atom.element.trim()} → ${abbrev.name} (${abbrev.formula})`)
    const subAtomIds = abbrev.atoms.map((_, idx) => (idx === 0 ? atom.id : `${atom.id}_g${idx}`))
    abbrev.atoms.forEach((sub, idx) => {
      nextAtoms.push({
        id: subAtomIds[idx],
        parentAtomId: atom.id,
        element: sub.element,
        formalCharge: sub.charge || 0,
        radicals: 0,
        x: atom.x + sub.x * 28,
        y: atom.y + sub.y * 28,
      })
    })
    abbrev.bonds.forEach(([fromIdx, toIdx, order], bIdx) => {
      nextBonds.push({
        id: `${atom.id}_gb${bIdx}`,
        fromAtomId: subAtomIds[fromIdx],
        toAtomId: subAtomIds[toIdx],
        order,
      })
    })
  }

  return { atoms: nextAtoms, bonds: nextBonds, expandedNames }
}

function smilesChargeSuffix(charge) {
  if (!charge) return ''
  const sign = charge > 0 ? '+' : '-'
  const mag = Math.abs(charge)
  return mag === 1 ? sign : `${sign}${mag}`
}

function pairKey(a, b) {
  return a < b ? `${a}::${b}` : `${b}::${a}`
}

// Format a single atom token for OpenSMILES so Lean 4's `SMILES.parse` receives the exact
// drawn element, aromaticity, isotope, explicit hydrogen count, or formal charge.
function formatAtomOpenSmiles(atom, isAromaticIncident) {
  if (!atom) return { token: 'C', isAromatic: false, unrecognized: false }
  const raw = (atom.element || 'C').trim()
  const charge = atom.formalCharge || 0

  if (raw === 'D' || raw === 'T') {
    return {
      token: `[${raw === 'D' ? 2 : 3}H${smilesChargeSuffix(charge)}]`,
      isAromatic: false,
      unrecognized: false,
    }
  }

  const hydride = parseSingleHeavyHydride(raw)
  const el = elementFromAtomLabel(raw) || hydride?.element || null

  if (!el) {
    // Unknown or unexpanded label: pass raw label into brackets so Lean 4's tokenizer/parser
    // returns its own formal ParseError / TokenizeError verdict.
    return {
      token: `[${raw}${smilesChargeSuffix(charge)}]`,
      isAromatic: false,
      unrecognized: true,
    }
  }

  const isArom = Boolean(isAromaticIncident && SMILES_AROMATIC_SUBSET.has(el))
  const sym = isArom ? el.toLowerCase() : el

  // If the user explicitly drew an aromatic hydride (like pyrrole `NH` in an aromatic ring),
  // emit `[nH]` so OpenSMILES records the explicit H on the aromatic nitrogen.
  if (isArom) {
    const expH = hydride ? hydride.hydrogens : 0
    if (charge !== 0 || expH > 0) {
      const hPart = expH > 0 ? `H${expH === 1 ? '' : expH}` : ''
      return {
        token: `[${sym}${hPart}${smilesChargeSuffix(charge)}]`,
        isAromatic: true,
        unrecognized: false,
      }
    }
    return { token: sym, isAromatic: true, unrecognized: false }
  }

  if (charge !== 0) {
    const expH = hydride ? hydride.hydrogens : 0
    const hPart = expH > 0 ? `H${expH === 1 ? '' : expH}` : ''
    return {
      token: `[${el}${hPart}${smilesChargeSuffix(charge)}]`,
      isAromatic: false,
      unrecognized: false,
    }
  }

  if (el === 'H') {
    return { token: '[H]', isAromatic: false, unrecognized: false }
  }

  if (!SMILES_ORGANIC_SUBSET.has(el)) {
    const expH = hydride ? hydride.hydrogens : 0
    const hPart = expH > 0 ? `H${expH === 1 ? '' : expH}` : ''
    return { token: `[${el}${hPart}]`, isAromatic: false, unrecognized: false }
  }

  return { token: el, isAromatic: false, unrecognized: false }
}

// OpenSMILES bond symbol matching `LeanSMILES.Molecule.bondSymbol` in `LeanSMILES/SMILES/Write.lean`:
// - Between two aromatic atoms: single bond is `-`, aromatic bond is `""` (implicit).
// - Otherwise: single is `""`, aromatic is `:`, double is `=`, triple is `#`.
function formatBondOpenSmiles(order, uArom, vArom) {
  if (order === 'double') return '='
  if (order === 'triple') return '#'
  if (order === 'aromatic') return uArom && vArom ? '' : ':'
  if (uArom && vArom) return '-'
  return ''
}

// Serialize the drawn 2D canvas graph into an OpenSMILES string for Lean 4 evaluation,
// recording the exact 1-to-1 vertex mapping (`drawnAtomIdByLeanIdx` and `leanIdxByDrawnAtomId`)
// between canvas atoms and Lean 4's `Fin n` indices `0 .. n-1`.
export function serializeDrawnGraph(drawnAtoms, drawnBonds) {
  if (!drawnAtoms.length) {
    return {
      smiles: '',
      expandedAtoms: [],
      expandedBonds: [],
      expandedNames: [],
      drawnAtomIdByLeanIdx: [],
      leanIdxByDrawnAtomId: new Map(),
      degreeByDrawnId: new Map(),
    }
  }

  const degreeByDrawnId = new Map(drawnAtoms.map((a) => [a.id, 0]))
  for (const b of drawnBonds) {
    degreeByDrawnId.set(b.fromAtomId, (degreeByDrawnId.get(b.fromAtomId) || 0) + 1)
    degreeByDrawnId.set(b.toAtomId, (degreeByDrawnId.get(b.toAtomId) || 0) + 1)
  }

  const { atoms, bonds, expandedNames } = expandLabelGroups(drawnAtoms, drawnBonds)
  const adj = new Map(atoms.map((a) => [a.id, []]))
  const bondByPair = new Map()
  const hasAromaticBond = new Set()

  for (const b of bonds) {
    if (adj.has(b.fromAtomId) && adj.has(b.toAtomId)) {
      adj.get(b.fromAtomId).push(b.toAtomId)
      adj.get(b.toAtomId).push(b.fromAtomId)
      bondByPair.set(pairKey(b.fromAtomId, b.toAtomId), b)
      if (b.order === 'aromatic') {
        hasAromaticBond.add(b.fromAtomId)
        hasAromaticBond.add(b.toAtomId)
      }
    }
  }

  const tokenByAtomId = new Map()
  const aromByAtomId = new Map()
  for (const atom of atoms) {
    const info = formatAtomOpenSmiles(atom, hasAromaticBond.has(atom.id))
    tokenByAtomId.set(atom.id, info.token)
    aromByAtomId.set(atom.id, info.isAromatic)
  }

  const parentByExpandedId = new Map(atoms.map((a) => [a.id, a.parentAtomId || a.id]))
  const emittedExpandedIds = []

  const visitedComp = new Set()
  const components = []
  for (const atom of atoms) {
    if (visitedComp.has(atom.id)) continue
    const comp = []
    const q = [atom.id]
    visitedComp.add(atom.id)
    while (q.length > 0) {
      const u = q.pop()
      comp.push(u)
      for (const v of adj.get(u) || []) {
        if (!visitedComp.has(v)) {
          visitedComp.add(v)
          q.push(v)
        }
      }
    }
    components.push(comp)
  }

  const renderComponent = (compIds) => {
    const rootId = compIds[0]
    const visited = new Set()
    const classifiedEdges = new Set()
    const ringClosureEdges = new Set()
    const treeChildren = new Map()

    const buildTree = (u) => {
      visited.add(u)
      const children = []
      for (const v of adj.get(u) || []) {
        const ek = pairKey(u, v)
        if (classifiedEdges.has(ek)) continue
        classifiedEdges.add(ek)
        if (visited.has(v)) {
          ringClosureEdges.add(ek)
        } else {
          children.push(v)
          buildTree(v)
        }
      }
      treeChildren.set(u, children)
    }
    buildTree(rootId)

    const openRingDigits = new Map()
    const freedDigits = []
    let nextDigit = 1
    const acquireDigit = () => {
      if (freedDigits.length > 0) {
        freedDigits.sort((a, b) => a - b)
        return freedDigits.shift()
      }
      return nextDigit++
    }
    const fmtDigit = (d) => (d < 10 ? String(d) : `%${String(d).padStart(2, '0')}`)

    const emit = (u) => {
      emittedExpandedIds.push(u)
      const uArom = aromByAtomId.get(u) || false

      const closures = (adj.get(u) || [])
        .map((v) => ({ v, ek: pairKey(u, v) }))
        .filter(({ ek }) => ringClosureEdges.has(ek))
        .map(({ v, ek }) => {
          const open = openRingDigits.get(ek)
          if (open !== undefined) {
            openRingDigits.delete(ek)
            freedDigits.push(open)
            return fmtDigit(open)
          }
          const d = acquireDigit()
          openRingDigits.set(ek, d)
          const bOrder = bondByPair.get(ek)?.order || 'single'
          const vArom = aromByAtomId.get(v) || false
          return `${formatBondOpenSmiles(bOrder, uArom, vArom)}${fmtDigit(d)}`
        })
        .join('')

      const children = (treeChildren.get(u) || []).map((childId) => {
        const bOrder = bondByPair.get(pairKey(u, childId))?.order || 'single'
        const vArom = aromByAtomId.get(childId) || false
        return `${formatBondOpenSmiles(bOrder, uArom, vArom)}${emit(childId)}`
      })

      const branches = children.slice(0, -1).map((c) => `(${c})`).join('')
      const cont = children.length > 0 ? children[children.length - 1] : ''
      return `${tokenByAtomId.get(u) || 'C'}${closures}${branches}${cont}`
    }

    return emit(rootId)
  }

  const smiles = components.map(renderComponent).join('.')
  const drawnAtomIdByLeanIdx = emittedExpandedIds.map((expId) => parentByExpandedId.get(expId) || expId)
  const leanIdxByDrawnAtomId = new Map()
  drawnAtomIdByLeanIdx.forEach((drawnId, leanIdx) => {
    if (!leanIdxByDrawnAtomId.has(drawnId)) {
      leanIdxByDrawnAtomId.set(drawnId, leanIdx)
    }
  })

  return {
    smiles,
    expandedAtoms: atoms,
    expandedBonds: bonds,
    expandedNames,
    emittedExpandedIds,
    drawnAtomIdByLeanIdx,
    leanIdxByDrawnAtomId,
    degreeByDrawnId,
  }
}

// V2000 Molfile serializer using drawn 2D coordinates (fallback when Lean 4 molBlock is not active)
export function graphToMolfileV2000(drawnAtoms, drawnBonds, title = 'LeanSMILES-ChemDraw') {
  const { atoms, bonds } = expandLabelGroups(drawnAtoms, drawnBonds)
  const indexById = new Map(atoms.map((a, i) => [a.id, i + 1]))
  const padNum = (v, w) => String(v).padStart(w, ' ')
  const fmtCoord = (v) => ((v || 0) / 36).toFixed(4).padStart(10, ' ')

  const countsLine = `${padNum(atoms.length, 3)}${padNum(bonds.length, 3)}  0  0  0  0  0  0  0  0999 V2000`
  const atomLines = atoms.map((a) => {
    const el = elementFromAtomLabel(a.element) || parseSingleHeavyHydride(a.element)?.element || '*'
    const symbol = el.padEnd(3, ' ')
    return `${fmtCoord(a.x)}${fmtCoord(-a.y)}${fmtCoord(0)} ${symbol} 0  0  0  0  0  0  0  0  0  0  0  0`
  })
  const bondOrderCode = (order) => {
    if (order === 'double') return 2
    if (order === 'triple') return 3
    if (order === 'aromatic') return 4
    return 1
  }
  const bondStereoCode = (b) => {
    if (b.stereo === 'up') return 1
    if (b.stereo === 'down') return 6
    return 0
  }
  const bondLines = bonds.map((b) => {
    const a1 = indexById.get(b.fromAtomId) || 1
    const a2 = indexById.get(b.toAtomId) || 1
    return `${padNum(a1, 3)}${padNum(a2, 3)}${padNum(bondOrderCode(b.order), 3)}${padNum(bondStereoCode(b), 3)}  0  0  0`
  })

  const charged = atoms
    .map((a, i) => ({ idx: i + 1, charge: a.formalCharge || 0 }))
    .filter((x) => x.charge !== 0)
  const chgLines = []
  for (let i = 0; i < charged.length; i += 8) {
    const slice = charged.slice(i, i + 8)
    chgLines.push(
      `M  CHG${padNum(slice.length, 3)}${slice.map((e) => `${padNum(e.idx, 4)}${padNum(e.charge, 4)}`).join('')}`
    )
  }

  return [title, '  LeanSMILES-2D', '', countsLine, ...atomLines, ...bondLines, ...chgLines, 'M  END'].join('\n')
}

// Compute the open 120° skeletal sprouting angle from an existing atom
export function preferredSproutAngle(atom, atoms, bonds) {
  const atomById = new Map(atoms.map((a) => [a.id, a]))
  const neighbors = bonds
    .filter((b) => b.fromAtomId === atom.id || b.toAtomId === atom.id)
    .map((b) => atomById.get(b.fromAtomId === atom.id ? b.toAtomId : b.fromAtomId))
    .filter(Boolean)

  if (neighbors.length === 0) return -Math.PI / 6 // 30° up-right
  if (neighbors.length === 1) {
    const nb = neighbors[0]
    const incoming = Math.atan2(atom.y - nb.y, atom.x - nb.x)
    const cand1 = incoming + Math.PI / 3
    const cand2 = incoming - Math.PI / 3
    return Math.sin(cand1) < Math.sin(cand2) ? cand1 : cand2
  }

  const angles = neighbors
    .map((nb) => Math.atan2(nb.y - atom.y, nb.x - atom.x))
    .sort((a, b) => a - b)

  let bestGap = -1
  let bestAngle = -Math.PI / 2
  for (let i = 0; i < angles.length; i += 1) {
    const a1 = angles[i]
    const a2 = i + 1 < angles.length ? angles[i + 1] : angles[0] + Math.PI * 2
    const gap = a2 - a1
    if (gap > bestGap) {
      bestGap = gap
      bestAngle = a1 + gap / 2
    }
  }
  return bestAngle
}

// Generate ring vertices & bonds either centered at (cx, cy) or fused onto an existing bond
export function buildRingTemplate(templateType, { cx = 320, cy = 210, fuseBond = null, atoms = [], bondLength = 52 }) {
  if (!fuseBond && (templateType === 'chair1' || templateType === 'chair2')) {
    const flip = templateType === 'chair2' ? -1 : 1
    const s = bondLength * 0.85
    const offsets = [
      { dx: -1.35 * s, dy: 0.35 * s * flip },
      { dx: -0.45 * s, dy: -0.35 * s * flip },
      { dx: 0.55 * s, dy: -0.08 * s * flip },
      { dx: 1.35 * s, dy: -0.35 * s * flip },
      { dx: 0.45 * s, dy: 0.35 * s * flip },
      { dx: -0.55 * s, dy: 0.08 * s * flip },
    ]
    return {
      points: offsets.map((o) => ({
        x: Math.round((cx + o.dx) * 10) / 10,
        y: Math.round((cy + o.dy) * 10) / 10,
        element: 'C',
      })),
      orders: ['single', 'single', 'single', 'single', 'single', 'single'],
      fused: false,
    }
  }

  const spec = {
    benzene: { n: 6, orders: ['double', 'single', 'double', 'single', 'double', 'single'], elements: [] },
    aromatic6: { n: 6, orders: ['aromatic', 'aromatic', 'aromatic', 'aromatic', 'aromatic', 'aromatic'], elements: [] },
    cyclohexane: { n: 6, orders: ['single', 'single', 'single', 'single', 'single', 'single'], elements: [] },
    cyclopentane: { n: 5, orders: ['single', 'single', 'single', 'single', 'single'], elements: [] },
    cyclobutane: { n: 4, orders: ['single', 'single', 'single', 'single'], elements: [] },
    cyclopropane: { n: 3, orders: ['single', 'single', 'single'], elements: [] },
    cycloheptane: { n: 7, orders: Array(7).fill('single'), elements: [] },
    cyclooctane: { n: 8, orders: Array(8).fill('single'), elements: [] },
    pyridine: { n: 6, orders: ['double', 'single', 'double', 'single', 'double', 'single'], elements: ['N'] },
    pyrrole: { n: 5, orders: ['single', 'double', 'single', 'double', 'single'], elements: ['NH'] },
  }[templateType] || { n: 6, orders: ['single', 'single', 'single', 'single', 'single', 'single'], elements: [] }

  const { n, orders, elements } = spec
  const radius = bondLength / (2 * Math.sin(Math.PI / n))

  if (!fuseBond) {
    const points = Array.from({ length: n }, (_, i) => {
      const angle = -Math.PI / 2 + (i * 2 * Math.PI) / n
      return {
        x: Math.round((cx + radius * Math.cos(angle)) * 10) / 10,
        y: Math.round((cy + radius * Math.sin(angle)) * 10) / 10,
        element: elements[i] || 'C',
      }
    })
    return { points, orders, fused: false }
  }

  const a1 = atoms.find((a) => a.id === fuseBond.fromAtomId)
  const a2 = atoms.find((a) => a.id === fuseBond.toAtomId)
  if (!a1 || !a2) return { points: [], orders: [], fused: false }

  const dx = a2.x - a1.x
  const dy = a2.y - a1.y
  const len = Math.hypot(dx, dy) || bondLength
  const ux = dx / len
  const uy = dy / len
  const apothem = len / (2 * Math.tan(Math.PI / n))
  const r = len / (2 * Math.sin(Math.PI / n))
  const mx = (a1.x + a2.x) / 2
  const my = (a1.y + a2.y) / 2

  const cLeft = { x: mx - uy * apothem, y: my + ux * apothem }
  const cRight = { x: mx + uy * apothem, y: my - ux * apothem }

  const otherAtoms = atoms.filter((a) => a.id !== a1.id && a.id !== a2.id)
  const minDist = (center) => {
    if (otherAtoms.length === 0) return Infinity
    return Math.min(...otherAtoms.map((a) => Math.hypot(a.x - center.x, a.y - center.y)))
  }
  const chosenCenter = minDist(cLeft) >= minDist(cRight) ? cLeft : cRight
  const startAngle = Math.atan2(a1.y - chosenCenter.y, a1.x - chosenCenter.x)
  const a2Angle = Math.atan2(a2.y - chosenCenter.y, a2.x - chosenCenter.x)
  let step = a2Angle - startAngle
  while (step <= -Math.PI) step += Math.PI * 2
  while (step > Math.PI) step -= Math.PI * 2
  const dir = step >= 0 ? 1 : -1
  const dTheta = dir * ((2 * Math.PI) / n)

  const newPoints = []
  for (let i = 2; i < n; i += 1) {
    const ang = startAngle + i * dTheta
    newPoints.push({
      x: Math.round((chosenCenter.x + r * Math.cos(ang)) * 10) / 10,
      y: Math.round((chosenCenter.y + r * Math.sin(ang)) * 10) / 10,
      element: elements[i] || 'C',
    })
  }

  return { points: newPoints, orders, fused: true, a1Id: a1.id, a2Id: a2.id }
}

// Build a 120° zig-zag alkane chain from fromPt toward toPt
export function buildChainPoints(fromPt, toPt, bondLength = 52) {
  const dx = toPt.x - fromPt.x
  const dy = toPt.y - fromPt.y
  const dist = Math.hypot(dx, dy)
  const stepDist = bondLength * Math.cos(Math.PI / 6)
  const count = Math.max(1, Math.min(18, Math.round(dist / stepDist)))
  const baseAngle = dist > 4 ? Math.atan2(dy, dx) : 0
  const pts = [{ x: Math.round(fromPt.x * 10) / 10, y: Math.round(fromPt.y * 10) / 10 }]
  let curX = fromPt.x
  let curY = fromPt.y
  for (let i = 0; i < count; i += 1) {
    const offset = (i % 2 === 0 ? -1 : 1) * (Math.PI / 6)
    const ang = baseAngle + offset
    curX += Math.cos(ang) * bondLength
    curY += Math.sin(ang) * bondLength
    pts.push({
      x: Math.round(curX * 10) / 10,
      y: Math.round(curY * 10) / 10,
    })
  }
  return pts
}

// 2D spring-relaxation cleanup to regularize bond lengths & angles
export function cleanupStructure2D(atoms, bonds, selectedIds = null, bondLength = 52) {
  if (atoms.length < 2) return atoms
  const activeSet = selectedIds && selectedIds.size > 0 ? selectedIds : new Set(atoms.map((a) => a.id))
  const pos = new Map(atoms.map((a) => [a.id, { x: a.x, y: a.y }]))

  for (let iter = 0; iter < 36; iter += 1) {
    const delta = new Map(atoms.map((a) => [a.id, { dx: 0, dy: 0 }]))
    for (const b of bonds) {
      const p1 = pos.get(b.fromAtomId)
      const p2 = pos.get(b.toAtomId)
      if (!p1 || !p2) continue
      const vx = p2.x - p1.x
      const vy = p2.y - p1.y
      const d = Math.hypot(vx, vy) || 1
      const diff = (d - bondLength) * 0.25
      const ux = (vx / d) * diff
      const uy = (vy / d) * diff
      if (activeSet.has(b.fromAtomId)) {
        delta.get(b.fromAtomId).dx += ux
        delta.get(b.fromAtomId).dy += uy
      }
      if (activeSet.has(b.toAtomId)) {
        delta.get(b.toAtomId).dx -= ux
        delta.get(b.toAtomId).dy -= uy
      }
    }
    for (let i = 0; i < atoms.length; i += 1) {
      for (let j = i + 1; j < atoms.length; j += 1) {
        const id1 = atoms[i].id
        const id2 = atoms[j].id
        const p1 = pos.get(id1)
        const p2 = pos.get(id2)
        const vx = p2.x - p1.x
        const vy = p2.y - p1.y
        const d = Math.hypot(vx, vy) || 0.1
        const minDist = bondLength * 0.82
        if (d < minDist) {
          const push = (minDist - d) * 0.14
          const rx = (vx / d) * push
          const ry = (vy / d) * push
          if (activeSet.has(id1)) {
            delta.get(id1).dx -= rx
            delta.get(id1).dy -= ry
          }
          if (activeSet.has(id2)) {
            delta.get(id2).dx += rx
            delta.get(id2).dy += ry
          }
        }
      }
    }
    for (const [id, d] of delta.entries()) {
      const p = pos.get(id)
      p.x += d.dx
      p.y += d.dy
    }
  }

  return atoms.map((a) => {
    const p = pos.get(a.id)
    return {
      ...a,
      x: Math.round(p.x * 10) / 10,
      y: Math.round(p.y * 10) / 10,
    }
  })
}
