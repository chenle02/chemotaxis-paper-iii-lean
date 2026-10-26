#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build Chen-Ruau-Shen-JMB.tex
if rg -i 'undefined references|undefined citations|LaTeX Error|Citation.*undefined|Reference.*undefined' build/Chen-Ruau-Shen-JMB.log; then
  echo 'Build has unresolved references or citations' >&2
  exit 1
fi
