#!/usr/bin/env bash
#
# l5_remote.sh — build an assigned range of L5 per-n corrected-law files on a
# remote host and rsync the results back.  The per-n files are independent, so a
# range [NSTART,NEND] can be split across many hosts (this is the whole point of
# the one-file-per-n layout).
#
# Usage:
#     scripts/l5_remote.sh HOST NSTART NEND [JOBS]
#
#   HOST    ssh target (e.g. kbld, user@1.2.3.4).  Must be reachable by ssh/rsync.
#   NSTART  first n to build (>= 4; n=2,3 live in FiniteLaw.lean itself)
#   NEND    last n to build
#   JOBS    lake -j concurrency on the remote (default 4).  Each heavy n can peak
#           ~7 GB RSS; size JOBS to remote RAM (>= 8 GB/job recommended).
#
# What it does on the remote:
#   1. installs elan + the pinned toolchain (lean-toolchain) if missing;
#   2. clones the repo from GitHub (or updates an existing checkout);
#   3. `lake exe cache get` (Mathlib olean cache — avoids recompiling Mathlib);
#   4. runs scripts/l5_gen.py NSTART NEND to emit the per-n .lean files
#      (exact-arithmetic witnesses computed on the remote);
#   5. `lake build` of the assigned FiniteLaw.N<n> modules with -j JOBS;
#   6. writes cbcert/scripts/l5_results_<NSTART>_<NEND>.log with timings + axioms.
#
# Back on this machine it rsyncs:
#   - the generated Cbcert/FiniteLaw/N*.lean sources, and
#   - the results log,
# into the local checkout, so you can `git add` the verified range.
#
# NOTE: point HOST at `kbld` once SSH credentials for it exist.  Until then this
# script is a no-op against kbld (it will simply fail to connect); do NOT assume
# kbld is reachable.  Everything below is host-agnostic and tested against
# localhost-style targets.

set -euo pipefail

HOST="${1:?usage: l5_remote.sh HOST NSTART NEND [JOBS]}"
NSTART="${2:?need NSTART}"
NEND="${3:?need NEND}"
JOBS="${4:-4}"

REPO_URL="https://github.com/rain-1/odd-zeta-values-autoformalization.git"
REMOTE_DIR="\$HOME/odd-zeta-values-autoformalization"     # expanded on remote
CBCERT="cbcert"
LOG="scripts/l5_results_${NSTART}_${NEND}.log"

echo "[l5_remote] host=$HOST range=[$NSTART,$NEND] jobs=$JOBS"

# ---------------------------------------------------------------------------
# Remote driver script (runs entirely on HOST).
# ---------------------------------------------------------------------------
read -r -d '' REMOTE_SCRIPT <<REMOTE || true
set -euo pipefail
export PATH="\$HOME/.elan/bin:\$PATH"

# 1. elan + toolchain -------------------------------------------------------
if ! command -v elan >/dev/null 2>&1; then
  echo "[remote] installing elan"
  curl -fsSL https://elan.lean-lang.org/elan-init.sh -o /tmp/elan-init.sh
  sh /tmp/elan-init.sh -y --default-toolchain none
  export PATH="\$HOME/.elan/bin:\$PATH"
fi

# 2. clone / update ---------------------------------------------------------
if [ ! -d "$REMOTE_DIR/.git" ]; then
  echo "[remote] cloning $REPO_URL"
  git clone "$REPO_URL" "$REMOTE_DIR"
else
  echo "[remote] updating existing checkout"
  git -C "$REMOTE_DIR" fetch --all --quiet
  git -C "$REMOTE_DIR" checkout main --quiet
  git -C "$REMOTE_DIR" pull --ff-only --quiet || true
fi
cd "$REMOTE_DIR/$CBCERT"

# toolchain pin is read from lean-toolchain by elan automatically
elan toolchain install "\$(cat lean-toolchain | sed 's#.*/##')" || true

# 3. Mathlib cache ----------------------------------------------------------
echo "[remote] lake exe cache get"
lake exe cache get || true

# 4. generate the assigned per-n files -------------------------------------
echo "[remote] generating N$NSTART..N$NEND"
python3 scripts/l5_gen.py "$NSTART" "$NEND"

# 5. build ------------------------------------------------------------------
: > "$LOG"
echo "# L5 remote build  host=\$(hostname)  range=[$NSTART,$NEND]  jobs=$JOBS" >> "$LOG"
echo "# started \$(date -u +%FT%TZ)" >> "$LOG"
for n in \$(seq "$NSTART" "$NEND"); do
  echo "[remote] building Cbcert.FiniteLaw.N\$n"
  start=\$(date +%s)
  if lake build "Cbcert.FiniteLaw.N\$n" >>"$LOG" 2>&1; then st=ok; else st=FAIL; fi
  end=\$(date +%s)
  echo "n=\$n  status=\$st  seconds=\$((end-start))" | tee -a "$LOG"
done
echo "# finished \$(date -u +%FT%TZ)" >> "$LOG"

# axiom spot-check on the top of the range
echo "[remote] axiom check law_$NEND"
echo "import Cbcert.FiniteLaw.N$NEND open Cbcert.FiniteLaw in #print axioms law_$NEND" \
  > /tmp/l5axiom.lean
lake env lean /tmp/l5axiom.lean >>"$LOG" 2>&1 || true
REMOTE

# ---------------------------------------------------------------------------
# Run remotely, then pull results back.
# ---------------------------------------------------------------------------
ssh "$HOST" "bash -s" <<<"$REMOTE_SCRIPT"

LOCAL_ROOT="$(cd "$(dirname "$0")/.." && pwd)"     # .../cbcert
echo "[l5_remote] rsyncing generated files + log back to $LOCAL_ROOT"
rsync -avz "$HOST:$REMOTE_DIR/$CBCERT/Cbcert/FiniteLaw/N*.lean" \
      "$LOCAL_ROOT/Cbcert/FiniteLaw/" || true
rsync -avz "$HOST:$REMOTE_DIR/$CBCERT/$LOG" \
      "$LOCAL_ROOT/$LOG" || true

echo "[l5_remote] done.  Review $LOG, then wire the new n into Cbcert/FiniteLaw.lean"
echo "            (add imports + extend law_upto) and 'git add' the verified range."
