import React from 'react'
import { useNavigate } from 'react-router-dom'
import { ArrowRight } from 'lucide-react'
import { Card, Badge, Button, DataTable } from '../components/UI'
import PipelineScheme from '../components/PipelineScheme'

// Three short explanations for a visitor who knows neither chemistry
// software nor proof assistants, before any code or theorem appears.
const PRIMER = [
  {
    title: 'Molecular representations',
    body: (
      <>
        Chemists write molecules as <strong className="font-medium text-slate-800">SMILES</strong> strings:{' '}
        <code className="font-mono text-slate-800">CCO</code> is ethanol, two carbons and an oxygen in a row. Software
        turns the string into a graph of atoms and bonds, then into numbers, such as simple counts or a{' '}
        <strong className="font-medium text-slate-800">fingerprint</strong> (a list of which small fragments the
        molecule contains). Models use these numbers to predict properties like solubility, boiling point, or drug
        activity.
      </>
    ),
  },
  {
    title: 'Lean 4',
    body: (
      <>
        Lean is a programming language that is also a proof assistant: you write a function and a theorem about it in
        the same file, and Lean checks the proof. Every part of this pipeline is a Lean program, and we write proofs
        about how it behaves. We mark any claim that still lacks a proof.
      </>
    ),
  },
  {
    title: 'This project',
    body: (
      <>
        Three Lean libraries take a molecule from SMILES to a predicted property. They parse SMILES, assign
        aromaticity, and compute fingerprints the way RDKit does, then fit ridge regression. On the Delaney solubility
        benchmark, the Lean pipeline matches scikit-learn (test R² 0.67, RMSE 1.26). The gradient descent solver that
        trains the model comes with a proof that it converges. Writing the proofs also turned up problems in widely
        used tools and standards.
      </>
    ),
  },
]

const LIBRARIES = [
  {
    title: 'LeanSMILES',
    code: 'The chemistry',
    desc: 'Parses SMILES into a typed molecule graph and assigns aromaticity the way RDKit does. It also writes a canonical SMILES (proved unique), computes Morgan fingerprints, and draws molecules.',
  },
  {
    title: 'LeanLearn',
    code: 'The machine learning',
    desc: 'Ridge regression, closed-form and iterative, with R², RMSE and MAE, parity plots, and proofs that the iterative solvers converge.',
  },
  {
    title: 'Pipelines',
    code: 'Chemistry + ML',
    desc: 'A pipeline combines a dataset, a molecular representation, and a solver, in exact rational arithmetic. Before each fit, Lean checks that the data meet the conditions of the solver\'s convergence proof. When they do, the proof covers the model you get.',
  },
]

const THEOREMS = [
  { name: 'canonicalSmiles_relabel', statement: '(m.relabel σ).canonicalSmiles = m.canonicalSmiles', note: 'Canonical SMILES is independent of input atom order' },
  { name: 'morganBits_relabel', statement: '(m.relabel σ).morganBits 2 = m.morganBits 2', note: 'Morgan fingerprint is order-invariant up to radius 2' },
  { name: 'Finset.tanimotoMetricSpace', statement: 'dist A B = |A ∆ B| / |A ∪ B|', note: 'Tanimoto distance is a formal metric on bit sets (fails on ℝ vectors)' },
  { name: 'chargesConsistent_relabel', statement: '(m.relabel σ).chargesConsistent ↔ m.chargesConsistent', note: 'Formal charge bounds (-shellVacancy ≤ charge ≤ Z) preserved under relabeling' },
  { name: 'normalEquiv', statement: '{m // m.IsNormal} ≃ Vector Atom n × BondMatrix n', note: 'Lossless equivalence between normal-form molecule and bond matrix' },
  { name: 'Problem.loss_gradientDescent_le', statement: 'L(θₖ) ≤ L(u) + ‖u‖² / (2ηk)', note: 'After k steps of size η (with 2ηΛ ≤ 1), gradient descent from 0 is within ‖u‖²/(2ηk) of any competitor u: an O(1/k) convergence rate for the solver this site runs.' },
  { name: 'Pipeline.checkGDData_sound', statement: 'checkGDData = true → trainLoss ≤ loss u + ‖u‖²/(2ηk)', note: 'Lean checks the step-size condition exactly on the training set, so the bound holds for the fit shown on the Regression page' },
]

export default function Home() {
  const navigate = useNavigate()

  return (
    <div className="space-y-10">
      <div className="py-6">
        <Badge active>Lean 4 · Mathlib · LeanSMILES · LeanLearn · Pipelines</Badge>
        <h1 className="text-3xl sm:text-4xl font-semibold tracking-tight text-slate-900 mt-4 max-w-2xl">
          Formally verified cheminformatics
        </h1>
        <p className="text-slate-500 mt-3 max-w-xl text-sm leading-relaxed">
          LeanSMILES parses SMILES, computes fingerprints, and fits regression models, all in Lean 4, with proofs that
          Lean checks. Try it on a molecule or fit a model to a dataset.
        </p>

        <div className="flex items-center gap-3 mt-6">
          <Button onClick={() => navigate('/lab')} className="inline-flex items-center gap-1.5">
            Open SMILES Interpreter <ArrowRight size={14} />
          </Button>
          <Button variant="secondary" onClick={() => navigate('/datasets')}>
            Regression on Datasets
          </Button>
        </div>
      </div>

      <Card
        title="Programming, proving and testing"
        subtitle="A typical cheminformatics pipeline, and where LeanSMILES adds proofs and tests"
      >
        <PipelineScheme />
      </Card>

      <div className="max-w-2xl space-y-5">
        {PRIMER.map((p) => (
          <p key={p.title} className="text-sm text-slate-600 leading-relaxed">{p.body}</p>
        ))}
      </div>

      <div>
        <p className="text-[11px] uppercase tracking-wide text-slate-400 mb-3">The libraries</p>
        <div className="grid sm:grid-cols-3 gap-4">
          {LIBRARIES.map((l) => (
            <Card key={l.title} title={l.title} subtitle={l.code}>
              <p className="text-xs text-slate-500 leading-relaxed">{l.desc}</p>
            </Card>
          ))}
        </div>
      </div>

      <Card title="What the proofs revealed" subtitle="Issues in RDKit and the OpenSMILES standard">
        <div className="grid md:grid-cols-3 gap-x-6 gap-y-3.5 text-xs text-slate-500 leading-relaxed">
          <div>
            <p className="font-medium text-slate-800">1. RDKit's canonical SMILES is not always canonical</p>
            <p className="mt-0.5">
              A canonical SMILES should be the same no matter what order the atoms are listed in. For some molecules
              RDKit gives more than one: a 12-carbon cubic graph gets 8 different strings depending on input order.
              LeanSMILES always gives one, proved by{' '}
              <code className="text-teal-700 font-mono">canonicalSmiles_relabel</code>.
            </p>
          </div>
          <div className="border-t md:border-t-0 md:border-l border-slate-100 pt-2.5 md:pt-0 md:pl-6">
            <p className="font-medium text-slate-800">2. RDKit Morgan fingerprints can change with atom order at radius 3</p>
            <p className="mt-0.5">
              <code className="font-mono">C1=C(CO)C=C1CC</code> and <code className="font-mono">C1(CC)=CC(CO)=C1</code> are the
              same molecule, but RDKit gives them different radius-3 bits. Up to radius 2, the bits do not depend on atom
              order, proved by <code className="text-teal-700 font-mono">morganBits_relabel</code>.
            </p>
          </div>
          <div className="border-t md:border-t-0 md:border-l border-slate-100 pt-2.5 md:pt-0 md:pl-6">
            <p className="font-medium text-slate-800">3. OpenSMILES is ambiguous about aromatic hydrogens</p>
            <p className="mt-0.5">
              The standard (§3.1.5) does not fully determine the bond orders of aromatic atoms, so their hydrogen counts
              can be ambiguous. LeanSMILES picks one rule, defined in{' '}
              <code className="text-teal-700 font-mono">Molecule.implicitHydrogens</code>.
            </p>
          </div>
        </div>
      </Card>

      <Card title="Some of the theorems" subtitle="LeanSMILES, LeanLearn & Pipelines">
        <DataTable
          columns={[
            { key: 'name', label: 'Theorem', render: (v) => <code className="text-teal-700 font-medium">{v}</code> },
            { key: 'statement', label: 'Statement', render: (v) => <code className="text-slate-700 font-mono">{v}</code> },
            { key: 'note', label: 'Description' },
          ]}
          rows={THEOREMS}
        />
      </Card>

      <div className="border-t border-slate-100 pt-6 space-y-3 text-xs text-slate-400 leading-relaxed max-w-2xl">
        <p>
          Built by AI coding agents, directed by our team, at the{' '}
          <a
            href="https://llmhackathon.github.io"
            target="_blank"
            rel="noreferrer"
            className="text-teal-700 hover:underline"
          >
            Open Scientific Intelligence (OSI) Hackathon
          </a>
          , to show that formally verified scientific software can be built quickly. Next, we'll document the approach so
          researchers in other fields can use it.
        </p>
        <p>
          <span className="font-medium text-slate-600">Special thanks to the team!</span> Demarko Fulcher, Ejike David
          Ugwuanyi, Kevin Ishimwe, Samiha Sharlin, Hao Liu, Alex Haibel, Izzy Shahmoradi, Tyler R. Josephson
        </p>
        <p>
          This is based on work sponsored in part by the NSF CAREER Award #2236769, DARPA for the SciFy program under
          agreement number HR00112520301, the Army Research Office/Army Research Laboratory via grant
          #W911-NF-24-1-0399, an Amazon Research Award, and a Simons Foundation Pivot Fellowship.
        </p>
      </div>
    </div>
  )
}
