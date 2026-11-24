import React from 'react'
import { ArrowRight, ArrowDown, Code2, ShieldCheck, FlaskConical } from 'lucide-react'

const PROGRAMMING_STEPS = [
  {
    title: 'Training / test set with SMILES + labels',
    sub: '(e.g. solubility, drug activity)',
  },
  {
    title: 'SMILES parsing and validation',
  },
  {
    title: 'Fingerprint generation',
  },
  {
    title: 'Train ML model(s)',
  },
  {
    title: 'Predict properties',
  },
]

const PROVING_TOP_ROW = [
  'Canonical SMILES is unique',
  'Relabeling invariance of fingerprints',
  'Tanimoto similarity is a metric',
  'Input SMILES are valid',
]

const TESTING_STEPS = [
  'Check accuracy, compare model performance',
  'Tight agreement with RDKit and scikit-learn tests',
]

function SchemeNode({ title, sub, tone = 'purple' }) {
  const borderStyles =
    tone === 'emerald'
      ? 'border-emerald-300/80 hover:border-emerald-400'
      : tone === 'sky'
        ? 'border-sky-300/80 hover:border-sky-400'
        : 'border-purple-300/80 hover:border-purple-400'

  return (
    <div
      className={`h-full min-h-[78px] rounded-xl bg-white/95 border ${borderStyles} shadow-2xs px-3 py-3 flex flex-col items-center justify-center text-center transition`}
    >
      <p className="text-xs font-medium text-slate-800 leading-snug text-balance break-words">
        {title}
      </p>
      {sub && (
        <p className="text-[11px] text-slate-500 mt-1 leading-snug text-balance break-words">
          {sub}
        </p>
      )}
    </div>
  )
}

export default function PipelineScheme() {
  return (
    <div className="rounded-2xl border border-slate-200/85 overflow-hidden shadow-2xs">
      {/* TOP BAND: PROGRAMMING */}
      <div className="bg-[#f2edf9] border-b border-[#dfd5ef] p-4 sm:p-5">
        <div className="flex flex-wrap items-center justify-between gap-2 mb-3.5">
          <div className="inline-flex items-center gap-2">
            <span className="inline-flex items-center justify-center w-5 h-5 rounded-md bg-purple-600/12 text-purple-800 shrink-0">
              <Code2 size={13} />
            </span>
            <span className="text-sm font-semibold tracking-tight text-slate-900">
              Programming
            </span>
          </div>
          <span className="text-xs font-medium text-purple-950/70">
            Typical cheminformatics pipeline
          </span>
        </div>

        {/* 5 equal columns with dedicated arrow tracks on desktop */}
        <div className="grid grid-cols-1 lg:grid-cols-[1fr_auto_1fr_auto_1fr_auto_1fr_auto_1fr] gap-y-1.5 lg:gap-y-0 lg:gap-x-1.5 items-stretch">
          {PROGRAMMING_STEPS.map((step, idx) => (
            <React.Fragment key={step.title}>
              <SchemeNode title={step.title} sub={step.sub} tone="purple" />
              {idx < PROGRAMMING_STEPS.length - 1 && (
                <div
                  className="flex items-center justify-center py-0.5 lg:py-0 lg:px-0.5 text-purple-500"
                  aria-hidden="true"
                >
                  <ArrowRight size={15} strokeWidth={2.2} className="hidden lg:block shrink-0" />
                  <ArrowDown size={15} strokeWidth={2.2} className="block lg:hidden shrink-0" />
                </div>
              )}
            </React.Fragment>
          ))}
        </div>
      </div>

      {/* BOTTOM SPLIT: PROVING (Left 4/5) + TESTING (Right 1/5) */}
      <div className="grid grid-cols-1 lg:grid-cols-5">
        {/* PROVING REGION */}
        <div className="lg:col-span-4 bg-[#ecf6e8] border-b lg:border-b-0 lg:border-r border-[#d1e5c8] p-4 sm:p-5 flex flex-col justify-between gap-3">
          {/* 8-column subgrid: top 4 boxes span 2 cols each; bottom 3 boxes span 2 cols each */}
          <div className="grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-8 gap-3 items-stretch">
            {PROVING_TOP_ROW.map((title) => (
              <div key={title} className="lg:col-span-2">
                <SchemeNode title={title} tone="emerald" />
              </div>
            ))}

            {/* Bottom row: offset by 1 col on desktop so the first 2 sit centered under cols 1-3, and the 3rd sits directly under col 4 */}
            <div className="lg:col-start-2 lg:col-span-2">
              <SchemeNode
                title="Linear regression minimizes least squares error"
                tone="emerald"
              />
            </div>
            <div className="lg:col-start-4 lg:col-span-2">
              <SchemeNode
                title="Monotonic loss with iterations on ridge regression"
                tone="emerald"
              />
            </div>
            <div className="sm:col-span-2 lg:col-start-7 lg:col-span-2">
              <SchemeNode
                title="Soundness checks before ML training"
                tone="emerald"
              />
            </div>
          </div>

          <div className="flex items-center justify-between pt-1">
            <div className="inline-flex items-center gap-2">
              <span className="inline-flex items-center justify-center w-5 h-5 rounded-md bg-emerald-700/12 text-emerald-800 shrink-0">
                <ShieldCheck size={13} />
              </span>
              <span className="text-sm font-semibold tracking-tight text-slate-900">
                Proving
              </span>
            </div>
          </div>
        </div>

        {/* TESTING REGION */}
        <div className="lg:col-span-1 bg-[#e8f4fc] px-4 pt-2 pb-4 sm:px-4 sm:pt-2 sm:pb-5 flex flex-col justify-between gap-2">
          <div className="flex flex-col items-stretch gap-1.5">
            {/* Connector arrow down from "Predict properties" */}
            <div
              className="hidden lg:flex items-center justify-center text-sky-600 pb-0.5"
              aria-hidden="true"
            >
              <ArrowDown size={15} strokeWidth={2.2} />
            </div>

            <SchemeNode title={TESTING_STEPS[0]} tone="sky" />

            <div className="flex items-center justify-center py-0.5 text-sky-600" aria-hidden="true">
              <ArrowDown size={15} strokeWidth={2.2} />
            </div>

            <SchemeNode title={TESTING_STEPS[1]} tone="sky" />
          </div>

          <div className="flex items-center justify-between pt-1">
            <div className="inline-flex items-center gap-2">
              <span className="inline-flex items-center justify-center w-5 h-5 rounded-md bg-sky-700/12 text-sky-800 shrink-0">
                <FlaskConical size={13} />
              </span>
              <span className="text-sm font-semibold tracking-tight text-slate-900">
                Testing
              </span>
            </div>
          </div>
        </div>
      </div>
    </div>
  )
}
