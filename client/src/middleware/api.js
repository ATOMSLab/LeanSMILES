const rawBaseUrl = (
  import.meta.env.VITE_API_URL || 'https://leansmiles-production.up.railway.app'
).replace(/\/+$/, '')
const BASE_URL = rawBaseUrl.endsWith('/api') ? rawBaseUrl : `${rawBaseUrl}/api`

export const PRESET_MOLECULES = [
  {
    name: 'Caffeine',
    smiles: 'CN1C=NC2=C1C(=O)N(C)C(=O)N2C',
  },
  {
    name: 'Nitrobenzene (cleanUp)',
    smiles: 'c1ccccc1N(=O)=O',
  },
  {
    name: 'L-Alanine (Stereo @)',
    smiles: 'C[C@H](N)C(=O)O',
  },
  {
    name: 'Cubane (3D Cage)',
    smiles: 'C12C3C4C1C5C2C3C45',
  },
  {
    name: 'cis-Alkene (F/C=C\\F)',
    smiles: 'F/C=C\\F',
  },
  {
    name: 'Kekulé Benzene',
    smiles: 'C1=CC=CC=C1',
  },
  {
    name: 'Charge Check ([C+123])',
    smiles: 'C[C+123]',
  },
  {
    name: 'Invalid: C(C)1CC1',
    smiles: 'C(C)1CC1',
  },
]

const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms))

// One evaluation the page can cancel: the server sees its id (X-Request-Id) and
// drops or stops the Lean job when the request is aborted or POST /cancel names it.
export function newRequestHandle() {
  const id = globalThis.crypto?.randomUUID?.() || `${Date.now()}-${Math.random().toString(36).slice(2)}`
  const controller = new AbortController()
  return {
    id,
    signal: controller.signal,
    cancel() {
      if (controller.signal.aborted) return
      controller.abort()
      fetch(`${BASE_URL}/cancel`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ requestId: id }),
        keepalive: true,
      }).catch(() => {})
    },
  }
}

async function request(endpoint, options = {}, minDelayMs = 200, handle = null) {
  const headers = { 'Content-Type': 'application/json', ...(options.headers || {}) }
  if (handle?.id) headers['X-Request-Id'] = handle.id
  let res
  try {
    ;[res] = await Promise.all([
      fetch(`${BASE_URL}${endpoint}`, { ...options, headers, signal: handle?.signal }),
      sleep(minDelayMs),
    ])
  } catch (e) {
    if (e?.name === 'AbortError' || handle?.signal?.aborted) {
      const err = new Error('Cancelled')
      err.cancelled = true
      throw err
    }
    throw e
  }

  const data = await res.json().catch(() => ({}))
  if (!res.ok) {
    const err = new Error(data.error || `API error (${res.status})`)
    err.status = res.status
    err.details = data
    throw err
  }
  return data
}

export const api = {
  analyzeSmiles(smiles, handle = null) {
    return request('/parse', { method: 'POST', body: JSON.stringify({ smiles }) }, 200, handle)
  },

  compareTanimoto(smilesA, smilesB, handle = null) {
    return request('/tanimoto', { method: 'POST', body: JSON.stringify({ smilesA, smilesB }) }, 200, handle)
  },

  getDatasets(datasetId = 'delaney', handle = null) {
    return request(`/datasets?id=${encodeURIComponent(datasetId)}`, {}, 200, handle)
  },

  fitPipeline(payload, handle = null) {
    return request('/pipeline/fit', { method: 'POST', body: JSON.stringify(payload) }, 200, handle)
  },
}

export default api
