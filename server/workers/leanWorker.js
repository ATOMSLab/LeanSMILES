import { spawn } from 'child_process'
import fs from 'fs'
import path from 'path'
import os from 'os'
import { fileURLToPath } from 'url'

const __dirname = path.dirname(fileURLToPath(import.meta.url))
const REPO_ROOT = path.resolve(__dirname, '../..')
const CACHE_DIR = path.resolve(__dirname, '../.cache')
// The worker is Worker.lean at the repository root, compiled by `lake build worker`.
const WORKER_BIN = path.join(REPO_ROOT, '.lake', 'build', 'bin', process.platform === 'win32' ? 'worker.exe' : 'worker')
const DISK_CACHE_FILE = path.join(CACHE_DIR, 'eval-cache.json')
const ELAN_BIN = path.join(os.homedir(), '.elan', 'bin')
// One evaluation may run at most this long. Past it the worker is killed, the
// request fails with a clear message, and the next request gets a fresh worker.
const REQUEST_TIMEOUT_MS = Number(process.env.LEAN_REQUEST_TIMEOUT_MS) || 120000

fs.mkdirSync(CACHE_DIR, { recursive: true })

const cache = new Map()
if (fs.existsSync(DISK_CACHE_FILE)) {
  try {
    const raw = JSON.parse(fs.readFileSync(DISK_CACHE_FILE, 'utf8'))
    Object.entries(raw).forEach(([k, v]) => {
      if (k.startsWith('parse\t') && v?.aromatized?.ok && !Array.isArray(v?.aromatized?.atoms)) {
        return
      }
      cache.set(k, v)
    })
  } catch {}
}

function saveDiskCache() {
  try {
    fs.writeFileSync(DISK_CACHE_FILE, JSON.stringify(Object.fromEntries(cache)), 'utf8')
  } catch {}
}

// The warm worker is the `worker` executable: one request per stdin line, one
// `__JSON_START__ ... __JSON_END__` answer per request, in order. `queue[0]` is
// the request in flight once `sent` is set.
let workerProc = null
let workerReady = false
let buffer = ''
let restarts = 0
let building = null
const queue = []

const log = (msg) => console.log(`[lean worker] ${msg}`)

// The worker is spawned as its own process group and killed as a group, so a
// stop reaches it even if it ever runs through a wrapper such as `lake`.
function killWorker(proc) {
  if (!proc || proc.exitCode !== null || proc.signalCode !== null) return
  try {
    process.kill(-proc.pid, 'SIGKILL')
  } catch {
    try {
      proc.kill('SIGKILL')
    } catch {}
  }
}

// Without a binary, build it once (`lake build worker`, a few minutes the first
// time) and start the worker when that finishes; meanwhile requests queue.
function buildWorkerBinary() {
  if (building) return building
  log(`${WORKER_BIN} is missing; running \`lake build worker\``)
  const env = { ...process.env, PATH: `${ELAN_BIN}:${process.env.PATH || ''}` }
  building = new Promise((resolve) => {
    const proc = spawn('lake', ['build', 'worker'], { cwd: REPO_ROOT, env })
    proc.stdout.on('data', (chunk) => {
      const text = chunk.toString().trim()
      if (text) log(`lake build: ${text.split('\n').pop()}`)
    })
    proc.stderr.on('data', (chunk) => {
      const text = chunk.toString().trim()
      if (text) console.error(`[lake build worker] ${text}`)
    })
    proc.on('error', (err) => resolve(new Error(`lake build worker could not run: ${err.message}`)))
    proc.on('exit', (code) => resolve(code === 0 ? null : new Error(`lake build worker exited with code ${code}`)))
  }).then((err) => {
    building = null
    if (err) {
      log(err.message)
      while (queue.length > 0) {
        const q = queue.shift()
        clearTimeout(q.timer)
        q.reject(new Error(`The Lean worker is not built: ${err.message}`))
      }
    } else {
      log('built')
      startWarmWorker()
    }
  })
  return building
}

function startWarmWorker() {
  if (workerProc) return
  if (!fs.existsSync(WORKER_BIN)) {
    buildWorkerBinary()
    return
  }
  const env = { ...process.env, PATH: `${ELAN_BIN}:${process.env.PATH || ''}` }
  const proc = spawn(WORKER_BIN, [], {
    cwd: REPO_ROOT,
    env,
    detached: true,
  })
  workerProc = proc
  workerReady = false
  buffer = ''
  log(`starting (pid ${proc.pid})`)

  proc.stdout.on('data', (chunk) => {
    if (workerProc !== proc) return
    buffer += chunk.toString()

    if (!workerReady && buffer.includes('__WORKER_READY__')) {
      workerReady = true
      buffer = buffer.split('__WORKER_READY__').slice(1).join('')
      log('ready')
      flushQueue()
    }

    let match
    while ((match = buffer.match(/__JSON_START__([\s\S]*?)__JSON_END__/))) {
      const jsonStr = match[1]
      buffer = buffer.slice(match.index + match[0].length)
      const current = queue.shift()
      if (current) {
        clearTimeout(current.timer)
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

  proc.stderr.on('data', (chunk) => {
    const text = chunk.toString().trim()
    if (text) console.error(`[lean worker stderr] ${text}`)
  })

  proc.on('error', (err) => onWorkerGone(proc, `could not be started (${err.message})`))
  proc.on('exit', (code, signal) => onWorkerGone(proc, `exited (code ${code}, signal ${signal})`))
}

// The worker died or was killed. The request it was evaluating fails now
// instead of waiting forever; the rest of the queue gets a fresh worker. If it
// died before it was even ready, every queued request fails: the next request
// will try to start it again, and the reason is in the server log.
function onWorkerGone(proc, why) {
  if (workerProc !== proc) return
  const wasReady = workerReady
  workerProc = null
  workerReady = false
  buffer = ''
  killWorker(proc)

  if (!wasReady) {
    log(`${why} before it was ready; failing ${queue.length} queued request(s)`)
    while (queue.length > 0) {
      const q = queue.shift()
      clearTimeout(q.timer)
      q.reject(new Error(`Lean worker ${why} before it was ready; see the server log`))
    }
    return
  }

  const head = queue[0]
  if (head && head.sent) {
    queue.shift()
    clearTimeout(head.timer)
    const reason = head.timedOut
      ? `Lean evaluation exceeded ${Math.round(REQUEST_TIMEOUT_MS / 1000)} s and was stopped`
      : `Lean worker ${why} while evaluating this request`
    log(`${why}; failing the in-flight request`)
    head.reject(new Error(reason))
  } else {
    log(why)
  }

  if (queue.length > 0) {
    restarts += 1
    startWarmWorker()
  }
}

function flushQueue() {
  if (!workerReady || !workerProc || queue.length === 0) return
  const head = queue[0]
  if (!head.sent) {
    head.sent = true
    head.startedAt = Date.now()
    const proc = workerProc
    head.timer = setTimeout(() => {
      if (queue[0] !== head || workerProc !== proc) return
      head.timedOut = true
      log(`request exceeded ${REQUEST_TIMEOUT_MS} ms; killing the worker`)
      killWorker(proc)
    }, REQUEST_TIMEOUT_MS)
    proc.stdin.write(head.cmd + '\n')
  }
}

for (const sig of ['SIGINT', 'SIGTERM']) {
  process.on(sig, () => {
    killWorker(workerProc)
    process.exit(0)
  })
}
process.on('exit', () => killWorker(workerProc))

startWarmWorker()

export function leanWorkerStatus() {
  return {
    binary: fs.existsSync(WORKER_BIN),
    building: Boolean(building),
    running: Boolean(workerProc),
    ready: workerReady,
    queued: queue.length,
    restarts,
    cachedResults: cache.size,
    requestTimeoutMs: REQUEST_TIMEOUT_MS,
  }
}

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
    queue.push({ cmd, resolve, reject, sent: false, startedAt: Date.now(), timer: null, timedOut: false })
    flushQueue()
  })
}
