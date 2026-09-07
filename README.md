# Model Inference from Neural Artifacts: An Exchange Law for Structure and Memory

Source, computational checks, and Lean 4 formalization for the paper.

## Paper

`paper/` contains the LaTeX source, bibliography, style file, and the exhaustive
finite checks. `sh paper/build.sh` produces `main.pdf`; `python paper/checks/verify.py`
reruns every reported enumeration (Python 3.13, NumPy 2.3).

## Formalization

`lean/` is a Lean 4 project over Mathlib. Most results in the paper are proved there
at full generality: the canonical inference state, the exchange law under independent
pooling with its exact chain region, the coupled-width separation, the exact chain and
Boolean residual laws, finite-state extraction and recovery of the meet, the
attention--ReLU compiler with its semantic round trip, finite-symbol hardening and its
perturbation certificates, query certificates, intervention preservation for finite
structural causal models, the table and permutation memory bounds, and measurability of
the hardened events. Real quantifier elimination enters as an explicit interface.

```sh
cd lean
lake exe cache get
lake build
```

Toolchain: Lean 4.31.0; Mathlib pinned in `lakefile.toml`. The development uses no
axioms beyond `propext`, `Classical.choice`, and `Quot.sound`, and no incomplete proofs.
