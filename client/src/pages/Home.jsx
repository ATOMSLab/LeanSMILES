import React from 'react'
import { useNavigate } from 'react-router-dom'
import { ArrowRight } from 'lucide-react'
import { Card, Badge, Button, CodeBlock, DataTable } from '../components/UI'

const LIBRARIES = [
  {
    title: 'LeanSMILES',
    code: 'Chem · SMILES · Fingerprint · Aromaticity',
    desc: 'SMILES parser, typed Molecule n, canonical SMILES, Hückel 4n+2 aromaticity, formal charge checks, and radius-2 Morgan fingerprints.',
  },
  {
    title: 'LeanLearn',
    code: 'Regression · Solvers · Parity · Proofs',
    desc: 'Closed-form & iterative OLS/Ridge, Householder-QR, SparseRidge on 2048 Morgan bits, SVG parity plots, and ℝ convergence certificates.',
  },
  {
    title: 'Pipelines',
    code: 'Representation · Certificates · Delaney',
    desc: 'Formally verified molecular regression pipelines connecting Molecule n representations (Mol → ℚᵈ) to certified solvers.',
  },
]

const THEOREMS = [
  { name: 'canonicalSmiles_relabel', statement: '(m.relabel σ).canonicalSmiles = m.canonicalSmiles', note: 'Canonical SMILES is independent of input atom order' },
  { name: 'morganBits_relabel', statement: '(m.relabel σ).morganBits 2 = m.morganBits 2', note: 'Morgan fingerprint is order-invariant up to radius 2' },
  { name: 'Finset.tanimotoMetricSpace', statement: 'dist A B = |A ∆ B| / |A ∪ B|', note: 'Tanimoto distance is a formal metric on bit sets (fails on ℝ vectors)' },
  { name: 'chargesConsistent_relabel', statement: '(m.relabel σ).chargesConsistent ↔ m.chargesConsistent', note: 'Formal charge bounds (-shellVacancy ≤ charge ≤ Z) preserved under relabeling' },
  { name: 'normalEquiv', statement: '{m // m.IsNormal} ≃ Vector Atom n × BondMatrix n', note: 'Lossless equivalence between normal-form molecule and bond matrix' },
]

export default function Home() {
  const navigate = useNavigate()

  return (
    <div className="space-y-10">
      <div className="py-6">
        <Badge active>Lean 4 · Mathlib · LeanLearn · Pipelines</Badge>
        <h1 className="text-3xl sm:text-4xl font-semibold tracking-tight text-slate-900 mt-4 max-w-2xl">
          Formalizing molecular representations in Lean.
        </h1>
        <p className="text-slate-500 mt-3 max-w-xl text-sm leading-relaxed">
          Typed molecular graphs <code className="text-slate-800 font-mono">Molecule n</code>, canonical SMILES, RDKit Hückel aromaticity perception, Morgan circular fingerprints, and certified machine learning pipelines.
        </p>

        <div className="flex items-center gap-3 mt-6">
          <Button onClick={() => navigate('/lab')} className="inline-flex items-center gap-1.5">
            Open SMILES Interpreter <ArrowRight size={14} />
          </Button>
          <Button variant="secondary" onClick={() => navigate('/datasets')}>
            Datasets &amp; ML Pipeline
          </Button>
        </div>
      </div>

      <div className="grid sm:grid-cols-3 gap-4">
        {LIBRARIES.map((l) => (
          <Card key={l.title} title={l.title} subtitle={l.code}>
            <p className="text-xs text-slate-500 leading-relaxed">{l.desc}</p>
          </Card>
        ))}
      </div>

      <div className="grid md:grid-cols-2 gap-6">
        <Card title="Quickstart" subtitle="LeanSMILES.SMILES.Canon & Aromaticity">
          <CodeBlock
            code={`public section
open LeanSMILES LeanSMILES.SMILES

-- A parse is an Except: the molecule, or a positioned error.
parse "CCO" --> Except.ok Molecule 3 ["C", "C", "O"] [0-1, 1-2]
parse "c1cc[nH]c1" --> Except.ok Molecule 5 ["c", "c", "c", "[nH]", "c"]

-- Three strings, one molecule, one canonical SMILES.
(Mol.ofSmiles! "OCC").canonicalSmiles --> "CCO"
(Mol.ofSmiles! "C(O)C").canonicalSmiles --> "CCO"
(Mol.ofSmiles! "CCO").canonicalSmiles --> "CCO"

-- Camphene written two ways (ThermoPropertiesSMILES.csv).
(Mol.ofSmiles! "CC1(C)C2CCC(C2)C1=C").canonicalSmiles --> "C=C1C2CCC(C2)C1(C)C"
(Mol.ofSmiles! "CC1(C2CCC(C2)C1=C)C").canonicalSmiles --> "C=C1C2CCC(C2)C1(C)C"`}
          />
        </Card>

        <Card title="Findings About External Tools" subtitle="Uncovered by formalization & theorem proving">
          <div className="space-y-3.5 text-xs text-slate-500 leading-relaxed">
            <div>
              <p className="font-medium text-slate-800">1. RDKit canonical SMILES is not always canonical</p>
              <p className="mt-0.5">
                On a 12-carbon cubic graph with non-equivalent tied atoms, RDKit returns 8 different strings by input order. LeanSMILES proves a unique minimum via <code className="text-teal-700 font-mono">canonicalSmiles_relabel</code>.
              </p>
            </div>
            <div className="border-t border-slate-100 pt-2.5">
              <p className="font-medium text-slate-800">2. RDKit Morgan fingerprints depend on atom order from radius 3</p>
              <p className="mt-0.5">
                In <code className="font-mono">C1=C(CO)C=C1CC</code> vs <code className="font-mono">C1(CC)=CC(CO)=C1</code>, non-symmetric ring carbons tie at radius 2, yielding different ECFP6 bits at radius 3. LeanSMILES proves order-invariance up to radius 2 (<code className="text-teal-700 font-mono">morganBits_relabel</code>).
              </p>
            </div>
            <div className="border-t border-slate-100 pt-2.5">
              <p className="font-medium text-slate-800">3. OpenSMILES aromatic implicit hydrogens</p>
              <p className="mt-0.5">
                OpenSMILES §3.1.5 underdetermines aromatic bond orders. <code className="text-teal-700 font-mono">Molecule.implicitHydrogens</code> formalizes the valence-snapping rule.
              </p>
            </div>
          </div>
        </Card>
      </div>

      <Card title="Formal Theorems" subtitle="LeanSMILES & LeanLearn">
        <DataTable
          columns={[
            { key: 'name', label: 'Theorem', render: (v) => <code className="text-teal-700 font-medium">{v}</code> },
            { key: 'statement', label: 'Statement', render: (v) => <code className="text-slate-700 font-mono">{v}</code> },
            { key: 'note', label: 'Description' },
          ]}
          rows={THEOREMS}
        />
      </Card>
    </div>
  )
}
