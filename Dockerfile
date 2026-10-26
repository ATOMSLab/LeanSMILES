FROM node:20-bookworm-slim

# Install system dependencies required by elan, lake, and mathlib cache
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    git \
    ca-certificates \
    zstd \
    lz4 \
    xz-utils \
    tar \
    build-essential \
  && rm -rf /var/lib/apt/lists/*

# Install elan (Lean 4 version manager)
ENV ELAN_HOME="/root/.elan"
ENV PATH="/root/.elan/bin:${PATH}"
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
  | sh -s -- -y --default-toolchain none

WORKDIR /app

# 1. Fetch Lean toolchain & precompiled Mathlib .olean cache (cached layer)
COPY lean-toolchain lakefile.toml lake-manifest.json ./
RUN elan toolchain install "$(cat lean-toolchain)" \
  && lake exe cache get

# 2. Build LeanSMILES, LeanLearn, and Pipelines libraries
COPY LeanSMILES.lean LeanLearn.lean Pipelines.lean ./
COPY LeanSMILES ./LeanSMILES
COPY LeanLearn ./LeanLearn
COPY Pipelines ./Pipelines
COPY datasets ./datasets
RUN lake build LeanSMILES LeanLearn Pipelines

# 3. Install Express backend dependencies
COPY server/package.json server/package-lock.json ./server/
RUN cd server && npm ci --omit=dev

# 4. Copy backend source & pre-generate WorkerMain.lean
COPY server ./server
RUN node -e 'import("./server/templates/leanTemplates.js").then(m => import("fs").then(fs => { fs.mkdirSync("server/.cache", { recursive: true }); fs.writeFileSync("server/.cache/WorkerMain.lean", m.leanTemplates.workerDaemon()); }))'

ENV NODE_ENV=production
ENV PORT=8000
EXPOSE 8000

CMD ["node", "server/index.js"]
