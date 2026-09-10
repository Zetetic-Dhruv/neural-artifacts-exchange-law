/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import NeuralArtifacts.CertifiedChain.TraceWord
import NeuralArtifacts.CertifiedChain.FiberPartition
import NeuralArtifacts.CertifiedChain.TraceExtraction
import NeuralArtifacts.CertifiedChain.TraceCapacity
import NeuralArtifacts.CertifiedChain.HardeningRead
import NeuralArtifacts.CertifiedChain.Repair

/-!
# The certified-compiler chain: the bridges

Three developments with no Lean connection to each other — the affine-mux cascades of
`TLT_Proofs`, the presentation lattice of `PRLT`, and the exchange-law inference theory of
`NeuralArtifacts` — are wired together here. This library is a sink: it imports all three and
none of them imports it.

* `TraceWord` — **B1**. The active-branch trace is a word; TLT's partial-fiber predicate
  `MuxCascade.PFiber` is agreement of word prefixes and, equivalently, darkness at the
  depth-`m` trace presentation. The fiber predicate IS a presentation condition.
* `FiberPartition` — **B2**. The trace-word fibers discharge the four hypotheses of the
  continuous-state extraction template: cover, disjointness, successor determinacy, readout
  constancy. On a fiber the run collapses to a single affine map, exactly.
* `TraceExtraction` — **B3**. The minimal machine of a cascade read at its trace
  presentation is the canonical inference state.
* `TraceCapacity` — **B4**. PRLT's capacity identity at the cascade trace class, with the
  dimension bounded by the depth, meeting TLT's alternation bound on the trace word.
* `HardeningRead` — **B5**. Hardening is the inclusion of the hard presentation into the
  soft one; the read-axis law turns it into a quotient coarsening, and the wrong-mass
  condition (exact, perturbed, and score-margin forms) implies that the restriction creates
  no darkness between states the machine separates.
* `Repair` — **B6**. Where hardening does collapse a distinction, the enlargement cure names
  the word that restores it, and the explicit word is a score threshold.

The localization is by exact fibers throughout. Metric balls, Lipschitz constants and
covering numbers belong to the capacity side of `TLT_Proofs` and appear nowhere in this
library.
-/
