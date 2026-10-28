import React from 'react'
import { useNavigate } from 'react-router-dom'
import { ArrowRight } from 'lucide-react'
import { Card, Badge, Button, DataTable } from '../components/UI'

// Three short explanations for a visitor who knows neither chemistry
// software nor proof assistants, before any code or theorem appears.
const PRIMER = [
  {
    title: 'Molecular representations',
    subtitle: 'From a string to numbers a model can use',
    body: (
      <>
        Chemists write a molecule as a <strong className="font-medium text-slate-800">SMILES</strong> string:{' '}
        <code className="font-mono text-slate-800">CCO</code> is ethanol, two carbons and an oxygen in a row. Software reads
        that string into a graph (atoms joined by bonds), and turns the graph into numbers: simple counts, or a{' '}
        <strong className="font-medium text-slate-800">fingerprint</strong>, a list of which small fragments the molecule
        contains. Cheminformatics is the practice of building those representations and predicting properties from them,
        such as solubility, boiling point, or activity against a drug target.
      </>
    ),
  },
  {
    title: 'Lean 4',
    subtitle: 'A programming language that checks proofs',
    body: (
      <>
        Lean is a programming language that is also a proof assistant: the same file can define a function and prove a
        theorem about it, and the computer checks every step. Here the parser, the fingerprint and the regression solvers
        are Lean programs, and the claims about them are Lean theorems — this canonical SMILES does not depend on the order
        the atoms were written in; this solver ends within ε of the best possible training loss. Where a theorem is still
        missing, the site says so.
      </>
    ),
  },
  {
    title: 'This project',
    subtitle: 'SMILES to prediction, entirely in Lean',
    body: (
      <>
        Three libraries take a molecule from its SMILES string to a machine-learning prediction with nothing else in
        between: parsing, aromaticity perception and fingerprints as RDKit does them, then ridge and logistic regression
        with their metrics. On the Delaney solubility benchmark the Lean pipeline matches scikit-learn (test R² 0.67, RMSE
        1.26); on an EGFR activity set it reaches a test F1 of 0.92. The fingerprint model's trained weights are
        themselves certified after training by an exact residual check. Along the way the proofs turned up three issues
        in widely used tools and standards.
      </>
    ),
  },
]

const LIBRARIES = [
  {
    title: 'LeanSMILES',
    code: 'The chemistry',
    desc: 'Parses SMILES into a typed molecule graph, perceives aromaticity the way RDKit does, writes a canonical SMILES that is proved unique, computes Morgan fingerprints, and draws molecules.',
  },
  {
    title: 'LeanLearn',
    code: 'The machine learning',
    desc: 'Ridge and logistic regression, closed-form and iterative, with R², RMSE, F1 and ROC AUC, parity plots, and proofs that the iterative solvers converge.',
  },
  {
    title: 'Pipelines',
    code: 'The join',
    desc: 'A pipeline is data, representation and solver, all in exact rational arithmetic. After training, the residual of the normal equations at the trained weights is checked exactly, and a theorem turns that check into a bound on how far they are from the optimum — for the five-count pipeline and for ridge on 2048 Morgan bits alike.',
  },
]

const THEOREMS = [
  { name: 'canonicalSmiles_relabel', statement: '(m.relabel σ).canonicalSmiles = m.canonicalSmiles', note: 'Canonical SMILES is independent of input atom order' },
  { name: 'morganBits_relabel', statement: '(m.relabel σ).morganBits 2 = m.morganBits 2', note: 'Morgan fingerprint is order-invariant up to radius 2' },
  { name: 'Finset.tanimotoMetricSpace', statement: 'dist A B = |A ∆ B| / |A ∪ B|', note: 'Tanimoto distance is a formal metric on bit sets (fails on ℝ vectors)' },
  { name: 'chargesConsistent_relabel', statement: '(m.relabel σ).chargesConsistent ↔ m.chargesConsistent', note: 'Formal charge bounds (-shellVacancy ≤ charge ≤ Z) preserved under relabeling' },
  { name: 'normalEquiv', statement: '{m // m.IsNormal} ≃ Vector Atom n × BondMatrix n', note: 'Lossless equivalence between normal-form molecule and bond matrix' },
  { name: 'Pipeline.checkResidual_sound', statement: 'checkResidual θ ε = true → loss θ ≤ loss u + ε', note: 'Trained weights whose exact residual passes the check are within ε of every competitor — checked after training, at any λ' },
]

export default function Home() {
  const navigate = useNavigate()

  return (
    <div className="space-y-10">
      <div className="py-6">
        <Badge active>Lean 4 · Mathlib · LeanSMILES · LeanLearn · Pipelines</Badge>
        <h1 className="text-3xl sm:text-4xl font-semibold tracking-tight text-slate-900 mt-4 max-w-2xl">
          Molecules, machine learning and proofs — in one language.
        </h1>
        <p className="text-slate-500 mt-3 max-w-xl text-sm leading-relaxed">
          LeanSMILES reads a molecule from its SMILES string, builds the representations that cheminformatics runs on,
          trains a model on them, and proves that the pieces behave as claimed — all in Lean 4. Try it on a molecule, or
          fit a model on a dataset.
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

      <div className="grid md:grid-cols-3 gap-4">
        {PRIMER.map((p) => (
          <Card key={p.title} title={p.title} subtitle={p.subtitle}>
            <p className="text-xs text-slate-500 leading-relaxed">{p.body}</p>
          </Card>
        ))}
      </div>

      <Card
        title="Programming, proving and testing"
        subtitle="A typical cheminformatics pipeline, and what LeanSMILES proves and tests along it"
      >
        <img
          src="/leansmiles-scheme.png"
          alt="Scheme: the pipeline from a training set of SMILES and labels through parsing, fingerprints and model training to predictions (programming); the theorems proved along it, such as canonical SMILES being unique and soundness checks before training (proving); and accuracy checks against RDKit and scikit-learn (testing)"
          className="w-full h-auto rounded-xl border border-slate-200/70"
        />
      </Card>

      <div>
        <p className="text-[11px] uppercase tracking-wide text-slate-400 mb-3">The three libraries</p>
        <div className="grid sm:grid-cols-3 gap-4">
          {LIBRARIES.map((l) => (
            <Card key={l.title} title={l.title} subtitle={l.code}>
              <p className="text-xs text-slate-500 leading-relaxed">{l.desc}</p>
            </Card>
          ))}
        </div>
      </div>

      <Card title="What the proofs turned up" subtitle="Three issues in widely used tools and standards">
        <div className="grid md:grid-cols-3 gap-x-6 gap-y-3.5 text-xs text-slate-500 leading-relaxed">
          <div>
            <p className="font-medium text-slate-800">1. RDKit's canonical SMILES is not always canonical</p>
            <p className="mt-0.5">
              A canonical SMILES is meant to be the one string for a molecule, however its atoms were listed. For some
              molecules RDKit gives several — a 12-carbon cubic graph gets 8, depending on the input order. Ours gives
              one, and the theorem <code className="text-teal-700 font-mono">canonicalSmiles_relabel</code> says so.
            </p>
          </div>
          <div className="border-t md:border-t-0 md:border-l border-slate-100 pt-2.5 md:pt-0 md:pl-6">
            <p className="font-medium text-slate-800">2. RDKit Morgan fingerprints depend on atom order from radius 3</p>
            <p className="mt-0.5">
              <code className="font-mono">C1=C(CO)C=C1CC</code> and <code className="font-mono">C1(CC)=CC(CO)=C1</code> are the
              same molecule but get different radius-3 bits. LeanSMILES proves order-invariance up to radius 2 (
              <code className="text-teal-700 font-mono">morganBits_relabel</code>), which is where it stops holding.
            </p>
          </div>
          <div className="border-t md:border-t-0 md:border-l border-slate-100 pt-2.5 md:pt-0 md:pl-6">
            <p className="font-medium text-slate-800">3. OpenSMILES leaves aromatic hydrogen counts open</p>
            <p className="mt-0.5">
              The standard (§3.1.5) does not fully determine the bond orders, and so the hydrogens, of aromatic atoms.{' '}
              <code className="text-teal-700 font-mono">Molecule.implicitHydrogens</code> pins down the rule.
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
          Built by AI coding agents guided by human experts at the{' '}
          <a
            href="https://llmhackathon.github.io"
            target="_blank"
            rel="noreferrer"
            className="text-teal-700 hover:underline"
          >
            Open Scientific Intelligence (OSI) Hackathon
          </a>
          , as a demonstration that formally verified scientific software can be made quickly. Next: documenting the
          approach so that scientists and engineers in other fields can use it.
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
