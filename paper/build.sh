#!/bin/sh
# Build the anonymous review PDF from the supplied sources.
set -eu
cd "$(dirname "$0")"
export SOURCE_DATE_EPOCH=1788739200
export FORCE_SOURCE_DATE=1
if command -v bibtex >/dev/null 2>&1; then
    BIBTEX=bibtex
elif command -v bibtex.original >/dev/null 2>&1; then
    BIBTEX=bibtex.original
else
    echo 'BibTeX is required (normally supplied with TeX Live or MiKTeX).' >&2
    exit 1
fi
pdflatex -interaction=nonstopmode -halt-on-error main.tex > build_pass1.log 2>&1
"$BIBTEX" main > build_bib.log 2>&1
pdflatex -interaction=nonstopmode -halt-on-error main.tex > build_pass2.log 2>&1
pdflatex -interaction=nonstopmode -halt-on-error main.tex > build_pass3.log 2>&1
if grep -E 'undefined references|undefined citations|Overfull \\hbox' build_pass3.log; then
    echo 'Inspect the reported typesetting diagnostics.' >&2
    exit 1
fi
printf 'Built main.pdf\n'
