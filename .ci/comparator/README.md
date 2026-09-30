# Statement and definition preservation with Comparator

The [Comparator workflow](../../.github/workflows/comparator.yml) uses
[leanprover/comparator](https://github.com/leanprover/comparator) to compare the
candidate against twelve short, self-contained problem specifications:

| Challenge | Physical lines | Configuration | Comparison roots |
| --- | --- | --- | --- |
| [ReverseSimplexChallenge.lean](ReverseSimplexChallenge.lean) | 72 | [reverse_simplex.json](reverse_simplex.json) | 6 theorems |
| [SimplicialSetChallenge.lean](SimplicialSetChallenge.lean) | 96 | [simplicial_set.json](simplicial_set.json) | 10 theorems and 3 definition roots |
| [WordObstructionChallenge.lean](WordObstructionChallenge.lean) | 22 | [word_obstruction.json](word_obstruction.json) | 5 theorems |
| [PresheafChallenge.lean](PresheafChallenge.lean) | 92 | [presheaf.json](presheaf.json) | 6 theorems: equivalence, limits/colimits, presentability, free adjunction |
| [NormalCofibrationChallenge.lean](NormalCofibrationChallenge.lean) | 88 | [normal_cofibration.json](normal_cofibration.json) | 2 theorems |
| [UnitaryObstructionChallenge.lean](UnitaryObstructionChallenge.lean) | 44 | [unitary_obstruction.json](unitary_obstruction.json) | 2 theorems |
| [FreeCofibrationChallenge.lean](FreeCofibrationChallenge.lean) | 91 | [free_cofibration.json](free_cofibration.json) | 13 theorems: monicity, saturation closure, preservation and reflection |
| [VerticesChallenge.lean](VerticesChallenge.lean) | 28 | [vertices.json](vertices.json) | 3 theorems identifying the common vertices with the zero-skeleton |
| [FreeDaggerPushoutChallenge.lean](FreeDaggerPushoutChallenge.lean) | 88 | [free_dagger_pushout.json](free_dagger_pushout.json) | 2 theorems: pushout, unit and swap, including the literal zero-skeleton span |
| [RelativeSkeletonChallenge.lean](RelativeSkeletonChallenge.lean) | 55 | [relative_skeleton.json](relative_skeleton.json) | 3 theorems: stable skeleta and actual filtration with inclusions and colimit |
| [FreeDaggerCofibrationChallenge.lean](FreeDaggerCofibrationChallenge.lean) | 82 | [free_dagger_cofibration.json](free_dagger_cofibration.json) | 5 theorems: free monos, genuine boundary generators, saturation inclusion and lifting |
| [RelativeCellBoundaryChallenge.lean](RelativeCellBoundaryChallenge.lean) | 29 | [relative_cell_boundary.json](relative_cell_boundary.json) | 4 theorems: epi membership, exact boundary preimage, complement and normal-form uniqueness |

Each file directly imports only pinned Mathlib modules, with its own definitions
visible. None imports `DaggerModels`, a local reference module, or a snapshot of
the implementation. The twelve Challenges are compiled in separate environments
under the logical module name `Challenge`. Their **787 lines in total**, including
comments and blank lines, are the review surface;
reviewing one file does not review the others.

The checker retains the original **21 named library theorems** and adds 40
selected results toward the main theorems, including their statement
dependencies. Three additional reflexive statements make `FreeCofibration`,
`nonDegenerateEquiv`, and `forget` roots of the recursive definition comparison.
These statements are inline in the simplicial-set Challenge; `Contracts.lean`
adds matching roots to the solution environment. They are audit markers, not new
mathematical results, and are not imported by `DaggerModels.lean`.
No definition holes are enabled. [targets.json](targets.json) records the full
64-root coverage set; it is a registry, not an executable Comparator config.

The new existential statements require actual categories, equivalences,
adjunctions, and counterexamples. They let the implementation choose the proof
and witnesses without duplicating those constructions in the problem file.
The integer-groupoid and initial-to-point witnesses are implemented in the
library; the Challenges protect the stated existence conclusions and their
definitions, not a unique choice of witness. All earlier roots remain intact.

The free-completion targets apply to **any actual adjunction** `F ⊣ forget`.
They require its unit to be the first coprojection, a natural second
coprojection, the genuine pushout universal property, and both dagger-swap
equations with the standard double-reversal isomorphism. The second target
uses the actual zero-skeleton subcomplex, with its canonical inclusion
preserved. Together with the separate vertices specification, this protects
the paper's precise gluing formula, not merely an arbitrary isomorphic object
or the existence of an unspecified left adjoint.

The relative-filtration target retains actual transfinite-composition data,
including the source map and colimit, and identifies each stage with the exact
image-plus-skeleton subobject while preserving its inclusion in the target.
The free-boundary target defines its generators as actual images of ordinary
boundary inclusions. Its saturation assertion has only the proved direction
from generated maps to free cofibrations; the converse is still open. The
ordinary cell specification fixes both the exact boundary preimage and the
unique nondegenerate ancestor/epi map. These new obligations add 18 roots to
the preceding 46, all of which are retained. Tool and dependency pins and both
negative-control definitions are unchanged.

The result statements in a Challenge have intentional `sorry` placeholders:
they specify obligations, not proved results. The data definitions remain
explicit. Necessary structural proof fields in category/functor constructions
are also visible: this Comparator version compares full elaborated definitions,
including embedded proof terms. The library's proofs and axioms are checked
separately, and Challenge placeholders are never counted as library proofs.

The candidate module imports the proposed `DaggerModels` sources. Comparator
checks statement equality, the relevant transitive
definitions, permitted axioms, and replays the exported proof dependencies in
its Lean kernel. Changing a theorem's type to `True`, or changing
`FreeCofibration` to the vacuous condition `f = f`, is required to fail with a
specific comparison diagnostic. A compilation error alone is not accepted as
evidence that either negative control worked.

## Trust boundary

This checks agreement with the chosen Lean specifications. It does **not**
establish that they faithfully translate the informal manuscript. The Challenges
were produced with AI assistance and are recorded as agent-reviewed, not
independently human-reviewed, in `formalization.yaml`.

On pull requests, `pull_request_target` executes the **base branch's** control
files and uses its Challenges. The candidate checkout is treated as data: only its Lean library sources
are copied into an isolated project. Its Lake configuration, dependency pins,
shell/Python scripts, workflows, and prebuilt artifacts are not executed or
reused. All checkouts disable credential persistence and the workflow has only
read permission. Every case receives a fresh independent copy of the trusted
dependency cache immediately before its sandboxed build. That writable copy is
discarded after the comparison, keeping disk usage bounded as coverage grows.
Only source files and logs are retained; candidate artifacts are never reused
by a later case or loaded outside the sandbox.

Comparator builds and exports the candidate with the actual Linux Landrun
sandbox. The upstream-recommended systemd restriction on AF_UNIX sockets is
also applied, and comparison runs as the unprivileged runner user. There is no
fake-landrun fallback. Candidate artifacts are never subsequently loaded outside
the sandbox. The ordinary build/axiom/metadata job runs on a separate runner.

The Challenge files, comparison target list, contracts, trusted preparer, tool
pins, and workflow are trusted inputs. Changes to these files need explicit
review: a maintainer who changes both the target and its checker can still
change what is being checked. Repository administration and branch protection
are not established by this workflow. Newly added mathematical results must be
registered explicitly; the current target list is not a claim of coverage for
future declarations. The source-hygiene check enforces at most 100 physical
lines per Challenge (including blank lines and comments), plain direct Mathlib
imports, standard permitted axioms, no definition holes, and exact registration
of all 64 roots. This check is not a Lean parser or an adversarial security
boundary; it does not replace review of trusted source files.

## Pinned tools

| Component | Revision |
| --- | --- |
| Comparator | `fd5d5bcf14177b187f66d4502071268d877887c3` |
| Exporter for Lean 4.27.0 | `590dec59d93ab6becdf16fdd8aee5abbb99cb856` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

Comparator is built with the toolchain in its own pinned repository. The
exporter and both proof projects use the companion's original Lean 4.27.0
toolchain. See the workflow for executable setup and the two deliberate
negative controls. This Linux check is separate from the macOS-compatible
`lake build`, axiom audit, and metadata validation commands.

The immutable v0.1.0 commit `dce8401a23588ba65b8aa4ca41de26cb0203d444`
still supplies the trusted Lake configuration, toolchain, dependency manifest,
and implementations mutated by the two negative controls. It no longer supplies
the Challenge mathematics. The twelve positive comparisons use current candidate
source. Every comparison has independent writable dependency artifacts, staged
and discarded sequentially by `run_comparator.py`.

## Updating the mathematical specification

First review the proposed statements, definitions, hypotheses, and manuscript
correspondence. Explain any mathematical change, then update the trusted
Challenges, target registry/configurations, and `formalization.yaml`, and rerun
both positive and negative checks. Do not automatically replace a Challenge with
the candidate when Comparator reports a mismatch. Dependency or Lean upgrades
also require explicit review, because Comparator checks the elaborated
statements and their definitions, not merely displayed source text.
