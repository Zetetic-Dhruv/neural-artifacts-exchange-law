# Model Inference from Neural Artifacts: An Exchange Law for Structure and Memory

Source, computational checks, and Lean 4 formalization for the paper.

## Paper

`paper/` contains the LaTeX source, bibliography, style file, and the exhaustive
finite checks. `sh paper/build.sh` produces `main.pdf`; `python paper/checks/verify.py`
reruns every reported enumeration (Python 3.13, NumPy 2.3).

## Formalization

`lean/` is a Lean 4 project over Mathlib. All results in the paper are proved there
at full generality: the canonical inference state, the exchange law under independent
pooling with its exact chain region, the coupled-width separation, the exact chain and
Boolean residual laws, finite-state extraction and recovery of the meet, the
attention--ReLU compiler with its semantic round trip, finite-symbol hardening and its
perturbation certificates, query certificates, intervention preservation for finite
structural causal models, the table and permutation memory bounds, measurability of the
hardened events, the width law for an arbitrary inference state, the adaptive-experiment
bound on a pooled memory, and the mind-change bound. Real quantifier elimination enters as an explicit interface.

```sh
cd lean
lake exe cache get
lake build
```

Toolchain: Lean 4.31.0; Mathlib pinned in `lakefile.toml`. The development uses no
axioms beyond `propext`, `Classical.choice`, and `Quot.sound`, and no incomplete proofs.

## The certified-compiler chain (branch `exchange-law`)

`lean/NeuralArtifacts/CertifiedChain/` bridges three developments that were proved
separately: the cascade fiber (trace agreement, on which a routed network collapses to a
single affine map), the presentation lattice (admissible words, the read axis, darkness and
its cure), and the extraction theory in this repository.

| module | content |
|---|---|
| `TraceWord` | a cascade trace is a labeled word; prefix agreement is darkness at the trace presentation |
| `FiberPartition` | the affine collapse at general carrier dimension; successor determinacy and readout constancy discharge the finite-abstraction template, giving agreement on all histories |
| `TraceExtraction` | the reachable version space of trace atoms is the fiber they cut, so the minimal machine at the trace presentation is the canonical inference state |
| `TraceCapacity` | trace count as a dimension, bounded by depth with the carrier dimension absent |
| `HardeningRead` | hardening is a proper presentation restriction on the read axis; the wrong-mass, perturbation and score-margin criteria each imply it creates no darkness between separated states |
| `Repair` | where hardening collapses a distinction, the cure is exhibited: a threshold word at the differing coordinate |

98 declarations, no incomplete proofs, axioms within `propext`, `Classical.choice` and
`Quot.sound`. No metric, Lipschitz constant or covering number enters the routing line.

These modules import the presentation lattice and the cascade development, which live in a
larger library and are not vendored here, so they are **not** part of this repository's build
targets and `lake build` ignores them. They compile inside that library, where all three
build with zero errors and zero warnings. The 30 modules on `main` remain self-contained and
build on their own.
