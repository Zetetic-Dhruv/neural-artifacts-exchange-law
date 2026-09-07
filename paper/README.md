# Model Inference from Neural Artifacts
## An Exchange Law for Structure and Memory

Anonymous full-paper manuscript for the NeurIPS 2026 Workshop on Neural Network
Artifacts as a New Data Modality.

The supplied PDF contains 9 pages of main text, 1 page of references, and 10 pages
of appendices. The source uses the NeurIPS 2026 review layout. The author field
is explicitly anonymous; the style's `nonanonymous` switch merely suppresses
its placeholder affiliation, address, and email lines.

## Build the paper

A standard TeX Live installation with pdfLaTeX, BibTeX, PGF/TikZ, pgfplots,
natbib, microtype, and cleveref is sufficient.

```sh
sh build.sh
```

This produces `main.pdf` directly from `main.tex`, `appendix.tex`,
`references.bib`, and the included style file. The included `main.bbl` is the
BibTeX-generated bibliography, not a separately reconstructed source. PDF dates
and trailer identifiers are suppressed for reproducible builds. An identical
TeX environment is required for byte-identical rendering.

The style file was retrieved from the NeurIPS2026 directory of the public
`yenslife/conference-latex-templates` mirror. Its layout parameters are retained.

## Reproduce the checks

Tested with Python 3.13.5 and NumPy 2.3.5.

```sh
python -m pip install -r requirements.txt
python checks/verify.py
```

The command reruns all assertions and writes `checks/results.json`. The four
modules implement independent quotient checks, exhaustive monoid and congruence
enumeration, neural transition extraction, recursive forest execution, and
literal shared-block transformer execution. The verifier raises an exception on
failure. Do not run Python with `-O`, which disables assertions.

Integer transition and algebraic checks are exact. Softmax and transformer
checks use NumPy float64. These are exhaustive checks of explicitly compiled
finite constructions, not training or generalization experiments. The paper's
mathematical proofs do not depend on the enumeration.

## Contents

- `main.tex`: main text and document setup.
- `appendix.tex`: complete supplementary proofs and construction details.
- `references.bib`, `main.bbl`: bibliography database and generated bibliography.
- `neurips_2026.sty`: conference formatting.
- `build.sh`: reproducible PDF build.
- `requirements.txt`: Python dependency.
- `checks/`: executable verification and recorded results.
- `main.pdf`: PDF built from these exact sources.
- `SHA256SUMS`: integrity manifest for the package contents.

The new results are supplied as mathematical proofs. No new Lean compilation
or machine-checked proof claim is made in this package.
