import { spawn } from 'child_process'
import fs from 'fs'
import path from 'path'
import os from 'os'
import { fileURLToPath } from 'url'
import { leanTemplates } from '../templates/leanTemplates.js'

const __dirname = path.dirname(fileURLToPath(import.meta.url))
const REPO_ROOT = path.resolve(__dirname, '../..')
const CACHE_DIR = path.resolve(__dirname, '../.cache')
const WORKER_LEAN_FILE = path.join(CACHE_DIR, 'WorkerMain.lean')
const DISK_CACHE_FILE = path.join(CACHE_DIR, 'eval-cache.json')
const ELAN_BIN = path.join(os.homedir(), '.elan', 'bin')

fs.mkdirSync(CACHE_DIR, { recursive: true })
fs.writeFileSync(WORKER_LEAN_FILE, leanTemplates.workerDaemon(), 'utf8')

const cache = new Map()
if (fs.existsSync(DISK_CACHE_FILE)) {
  try {
    const raw = JSON.parse(fs.readFileSync(DISK_CACHE_FILE, 'utf8'))
    Object.entries(raw).forEach(([k, v]) => cache.set(k, v))
  } catch {}
}

function saveDiskCache() {
  try {
    fs.writeFileSync(DISK_CACHE_FILE, JSON.stringify(Object.fromEntries(cache)), 'utf8')
  } catch {}
}

let workerProc = null
let workerReady = false
let buffer = ''
const queue = []

function startWarmWorker() {
  if (workerProc) return
  const env = { ...process.env, PATH: `${ELAN_BIN}:${process.env.PATH || ''}` }

  workerProc = spawn('lake', ['env', 'lean', '--run', WORKER_LEAN_FILE], {
    cwd: REPO_ROOT,
    env,
  })

  workerProc.stdout.on('data', (chunk) => {
    buffer += chunk.toString()

    if (!workerReady && buffer.includes('__WORKER_READY__')) {
      workerReady = true
      buffer = buffer.split('__WORKER_READY__').slice(1).join('')
      flushQueue()
    }

    let match
    while ((match = buffer.match(/__JSON_START__([\s\S]*?)__JSON_END__/))) {
      const jsonStr = match[1]
      buffer = buffer.slice(match.index + match[0].length)
      const current = queue.shift()
      if (current) {
        const durationMs = Date.now() - current.startedAt
        try {
          const parsed = JSON.parse(jsonStr)
          const payload = {
            ...parsed,
            leanFeedback: {
              exitCode: 0,
              durationMs,
              cached: false,
              logs: 'Evaluated by warm Lean 4 worker',
            },
          }
          if (parsed.ok) {
            cache.set(current.cmd, payload)
            saveDiskCache()
          }
          current.resolve(payload)
        } catch (err) {
          current.reject(err)
        }
      }
      flushQueue()
    }
  })

  workerProc.on('close', () => {
    workerProc = null
    workerReady = false
  })
}

function flushQueue() {
  if (!workerReady || !workerProc || queue.length === 0) return
  const head = queue[0]
  if (!head.sent) {
    head.sent = true
    head.startedAt = Date.now()
    workerProc.stdin.write(head.cmd + '\n')
  }
}

startWarmWorker()

export function runLean(cmd) {
  if (cache.has(cmd)) {
    const hit = cache.get(cmd)
    return Promise.resolve({
      ...hit,
      leanFeedback: {
        ...hit.leanFeedback,
        durationMs: 0,
        cached: true,
      },
    })
  }

  startWarmWorker()

  return new Promise((resolve, reject) => {
    queue.push({ cmd, resolve, reject, sent: false, startedAt: Date.now() })
    flushQueue()
  })
}
