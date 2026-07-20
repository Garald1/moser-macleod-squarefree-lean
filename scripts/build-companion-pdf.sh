#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"

pandoc "$root/MOSER_MACLEOD_LEAN_COMPANION.md" \
  --from=gfm \
  --standalone \
  --lua-filter="$root/scripts/companion-pdf.lua" \
  --metadata title='The Moser--MacLeod Squarefree Error Estimate' \
  --metadata subtitle='Human proof and Lean correspondence' \
  --variable mainfont='DejaVu Serif' \
  --variable sansfont='DejaVu Sans' \
  --variable monofont='DejaVu Sans Mono' \
  --variable geometry:margin=0.85in \
  --variable colorlinks=true \
  --variable linkcolor=blue \
  --variable urlcolor=blue \
  --toc \
  --pdf-engine=xelatex \
  --output="$root/MOSER_MACLEOD_LEAN_COMPANION.pdf"
