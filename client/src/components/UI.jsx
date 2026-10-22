import React from 'react'
import { Terminal, CheckCircle2, AlertTriangle, XCircle } from 'lucide-react'

const LEAN_TOKEN_REGEX =
  /(--.*$)|("(?:\\.|[^"\\])*")|\b(public|section|open|import|def|theorem|lemma|abbrev|structure|inductive|where|match|with|let|in|fun|by|#eval)\b|\b(LeanSMILES|SMILES|Mol|Molecule|Depict|CSVparser|Finset|Vector|BondMatrix|SimpleGraph|Fin|String|Nat|Bool|Except)\b|(!|:=|↔|≃|→|≠|≤|≥|∆|∪|×|·)|([()[\]{}])|\b(\d+(?:\.\d+)?)\b/gm

export function highlightLeanTokens(code = '') {
  if (!code) return null
  const parts = []
  let lastIndex = 0
  const regex = new RegExp(LEAN_TOKEN_REGEX.source, 'gm')
  let match

  while ((match = regex.exec(code)) !== null) {
    if (match.index > lastIndex) {
      parts.push(
        <span key={`t-${lastIndex}`} className="text-slate-100">
          {code.slice(lastIndex, match.index)}
        </span>
      )
    }

    const [full, comment, str, kw, typeName, op, bracket, num] = match
    let cls = 'text-slate-100'
    if (comment) cls = 'text-slate-500 italic'
    else if (str) cls = 'text-emerald-300'
    else if (kw) cls = 'text-[#ff9e64] font-medium'
    else if (typeName) cls = 'text-sky-200'
    else if (op) cls = 'text-[#ff9e64]'
    else if (bracket) cls = 'text-amber-300'
    else if (num) cls = 'text-amber-200'

    parts.push(
      <span key={`m-${match.index}`} className={cls}>
        {full}
      </span>
    )
    lastIndex = regex.lastIndex
  }

  if (lastIndex < code.length) {
    parts.push(
      <span key={`e-${lastIndex}`} className="text-slate-100">
        {code.slice(lastIndex)}
      </span>
    )
  }

  return parts
}

export function Card({ title, subtitle, action, className = '', children }) {
  return (
    <div className={`glass rounded-2xl p-6 ${className}`}>
      {(title || action) && (
        <div className="flex items-center justify-between gap-4 mb-4">
          <div>
            {title && <h3 className="text-sm font-semibold text-slate-900">{title}</h3>}
            {subtitle && <p className="text-xs text-slate-500 mt-0.5">{subtitle}</p>}
          </div>
          {action}
        </div>
      )}
      {children}
    </div>
  )
}

export function Badge({ active = false, tone, children }) {
  let cls = 'bg-slate-100/80 text-slate-600 border border-slate-200/60'
  if (tone === 'rose') {
    cls = 'bg-rose-50 text-rose-700 border border-rose-200/80'
  } else if (tone === 'amber') {
    cls = 'bg-amber-50 text-amber-700 border border-amber-200/80'
  } else if (active || tone === 'teal') {
    cls = 'bg-teal-50 text-teal-700 border border-teal-200/80'
  }

  return (
    <span className={`inline-flex items-center px-2.5 py-0.5 rounded-full text-xs font-medium ${cls}`}>
      {children}
    </span>
  )
}

export function Button({ variant = 'primary', onClick, type = 'button', disabled = false, className = '', children }) {
  const styles =
    variant === 'primary'
      ? 'bg-slate-900 text-white hover:bg-slate-800 disabled:opacity-50'
      : 'bg-white/80 text-slate-600 border border-slate-200/80 hover:bg-white hover:text-slate-900 disabled:opacity-50'

  return (
    <button
      type={type}
      disabled={disabled}
      onClick={onClick}
      className={`px-4 py-2 rounded-xl text-xs font-medium transition cursor-pointer ${styles} ${className}`}
    >
      {children}
    </button>
  )
}

export function SectionHeader({ title, description, right }) {
  return (
    <div className="flex flex-col sm:flex-row sm:items-end justify-between gap-4 mb-8">
      <div>
        <h1 className="text-2xl font-semibold tracking-tight text-slate-900">{title}</h1>
        {description && <p className="text-sm text-slate-500 mt-1 max-w-xl">{description}</p>}
      </div>
      {right}
    </div>
  )
}

export function CodeBlock({ code }) {
  const lines = String(code || '').split('\n')
  return (
    <div className="rounded-xl bg-[#0d131a] border border-slate-800/90 py-3 text-xs font-mono overflow-x-auto leading-relaxed shadow-inner">
      {lines.map((line, idx) => {
        if (!line.trim()) {
          return <div key={idx} className="h-3.5" />
        }
        if (line.includes('-->')) {
          const [expr, res] = line.split('-->').map((s) => s.trim())
          const isErr = res.includes('Except.error')
          return (
            <div
              key={idx}
              className="px-4 py-1 bg-[#0c2331]/85 flex flex-wrap items-baseline justify-between gap-x-5 gap-y-1"
            >
              <span className="whitespace-pre">{highlightLeanTokens(expr)}</span>
              <span className={`font-medium ${isErr ? 'text-rose-400' : 'text-[#2ac3de]'}`}>
                {res}
              </span>
            </div>
          )
        }
        return (
          <div key={idx} className="px-4 py-0.5 whitespace-pre">
            {highlightLeanTokens(line)}
          </div>
        )
      })}
    </div>
  )
}

export function SpinnerPill({ label = 'Evaluating...' }) {
  return (
    <span className="inline-flex items-center gap-2 px-2.5 py-1 rounded-full bg-teal-50/90 border border-teal-200/70 text-teal-800 text-xs font-medium">
      <span className="w-3 h-3 rounded-full border-2 border-teal-200 border-t-teal-600 animate-spin shrink-0" />
      {label}
    </span>
  )
}

function parseLogLine(line) {
  const clean = line
    .replace(/^>\s*/, '')
    .replace(/^#eval\s+/, '')
    .trim()
  if (clean.includes('-->')) {
    const [cmd, res] = clean
      .split('-->')
      .map((s) => s.replace(/^#eval\s+/, '').trim())
    const isErr = res.includes('Except.error')
    return { cmd, res, isErr }
  }
  const isErr = clean.includes('Except.error') || clean.startsWith('message:')
  return { cmd: clean, res: '', isErr }
}

export function LogConsole({ logs = [], feedback, diagnostics, loading = false }) {
  if (!logs.length && !feedback && !diagnostics) return null

  return (
    <div
      className={`grid gap-6 transition-opacity duration-150 ${
        loading ? 'opacity-65' : 'opacity-100'
      } ${diagnostics ? 'md:grid-cols-12' : 'grid-cols-1'}`}
    >
      <Card
        className={diagnostics ? 'md:col-span-7' : ''}
        title="Lean 4 Infoview Logs"
        subtitle="Live evaluation trace from the LeanSMILES worker"
        action={
          loading ? (
            <SpinnerPill label="Evaluating..." />
          ) : (
            feedback && (
              <div className="flex items-center gap-1.5">
                <Terminal size={13} className="text-teal-600" />
                <Badge active>
                  {feedback.durationMs}ms · {feedback.cached ? 'cached' : 'live'}
                </Badge>
              </div>
            )
          )
        }
      >
        <div className="rounded-xl border border-slate-800/90 bg-[#0d131a] overflow-hidden max-h-72 overflow-y-auto py-2 font-mono text-xs shadow-inner">
          <div className="px-3.5 py-1 text-[11px] text-slate-500 border-b border-slate-800/70 mb-1 flex items-center justify-between">
            <span>{highlightLeanTokens('open LeanSMILES LeanSMILES.SMILES')}</span>
            <span className="text-[10px] text-slate-500">Lean 4.29.0</span>
          </div>
          <div className="divide-y divide-slate-800/40">
            {logs.map((line, i) => {
              const { cmd, res, isErr } = parseLogLine(line)
              return (
                <div
                  key={i}
                  className={`px-3.5 py-1.5 flex flex-col sm:flex-row sm:items-baseline justify-between gap-x-4 gap-y-1 transition ${
                    res ? 'bg-[#0c2331]/75 hover:bg-[#0c2331]' : 'hover:bg-slate-900/60'
                  }`}
                >
                  <div className="flex items-baseline gap-2.5 min-w-0">
                    <span className="text-[10px] text-slate-600 select-none w-4 shrink-0">
                      {String(i + 1).padStart(2, '0')}
                    </span>
                    <span className="truncate">{highlightLeanTokens(cmd)}</span>
                  </div>
                  {res && (
                    <span
                      className={`text-[11px] font-medium truncate max-w-full sm:max-w-xs shrink-0 ${
                        isErr ? 'text-rose-400' : 'text-[#2ac3de]'
                      }`}
                      title={res}
                    >
                      {res}
                    </span>
                  )}
                </div>
              )
            })}
          </div>
        </div>
      </Card>

      {diagnostics && (
        <Card
          className="md:col-span-5"
          title="Diagnostics & Checks"
          subtitle="Syntax, formal charge & Hückel checks"
          action={
            diagnostics.status === 'error' ? (
              <Badge tone="rose">Parse Error</Badge>
            ) : diagnostics.status === 'warn' ? (
              <Badge tone="amber">Warning</Badge>
            ) : (
              <Badge active>All Checks Passed</Badge>
            )
          }
        >
          <div className="space-y-2.5 text-xs">
            {diagnostics.items.map((item, idx) => (
              <div
                key={idx}
                className={`p-3 rounded-xl border flex items-start gap-2.5 ${
                  item.type === 'error'
                    ? 'bg-rose-50/60 border-rose-200/70 text-rose-900'
                    : item.type === 'warn'
                    ? 'bg-amber-50/60 border-amber-200/70 text-amber-900'
                    : 'bg-slate-50/70 border-slate-200/60 text-slate-700'
                }`}
              >
                <span className="mt-0.5 shrink-0">
                  {item.type === 'error' ? (
                    <XCircle size={14} className="text-rose-600" />
                  ) : item.type === 'warn' ? (
                    <AlertTriangle size={14} className="text-amber-600" />
                  ) : (
                    <CheckCircle2 size={14} className="text-teal-600" />
                  )}
                </span>
                <div className="min-w-0 flex-1">
                  <div className="flex items-center justify-between gap-2">
                    <span className="font-semibold">{item.label}</span>
                    {item.tag && (
                      <code className="text-[10px] opacity-75 font-mono">{item.tag}</code>
                    )}
                  </div>
                  <p className="mt-0.5 opacity-85 leading-relaxed break-words">{item.detail}</p>
                </div>
              </div>
            ))}
          </div>
        </Card>
      )}
    </div>
  )
}

export function DataTable({ columns, rows, maxHeight = 'max-h-96' }) {
  return (
    <div className={`overflow-auto rounded-xl border border-slate-200/60 bg-white/50 ${maxHeight}`}>
      <table className="w-full text-left text-xs">
        <thead className="sticky top-0 z-10 bg-white/95 backdrop-blur-xs text-slate-400 border-b border-slate-200/60">
          <tr>
            {columns.map((c) => (
              <th key={c.key} className="py-2.5 px-3.5 font-medium">
                {c.label}
              </th>
            ))}
          </tr>
        </thead>
        <tbody className="divide-y divide-slate-100">
          {rows.map((r, i) => (
            <tr key={i} className="hover:bg-slate-50/60 transition">
              {columns.map((c) => (
                <td key={c.key} className="py-2.5 px-3.5 text-slate-600">
                  {c.render ? c.render(r[c.key], r) : r[c.key]}
                </td>
              ))}
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  )
}
