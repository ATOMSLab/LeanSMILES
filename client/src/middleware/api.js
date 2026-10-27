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

async function request(endpoint, options = {}, minDelayMs = 200) {
  const [res] = await Promise.all([
    fetch(`${BASE_URL}${endpoint}`, {
      headers: { 'Content-Type': 'application/json', ...(options.headers || {}) },
      ...options,
    }),
    sleep(minDelayMs),
  ])

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
  analyzeSmiles(smiles) {
    return request('/parse', {
      method: 'POST',
      body: JSON.stringify({ smiles }),
    })
  },

  compareTanimoto(smilesA, smilesB) {
    return request('/tanimoto', {
      method: 'POST',
      body: JSON.stringify({ smilesA, smilesB }),
    })
  },

  getDatasets(datasetId = 'delaney') {
    return request(`/datasets?id=${encodeURIComponent(datasetId)}`)
  },

  fitPipeline(payload) {
    return request('/pipeline/fit', {
      method: 'POST',
      body: JSON.stringify(payload),
    })
  },
}

export default api
