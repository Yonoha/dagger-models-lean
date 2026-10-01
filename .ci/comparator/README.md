# Statement and definition preservation with Comparator

The [Comparator workflow](../../.github/workflows/comparator.yml) uses
[leanprover/comparator](https://github.com/leanprover/comparator) to compare the
candidate against seventeen self-contained problem specifications:

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
| [FreeDaggerCofibrationChallenge.lean](FreeDaggerCofibrationChallenge.lean) | 93 | [free_dagger_cofibration.json](free_dagger_cofibration.json) | 7 theorems: free monos, genuine boundary generators, relative cell presentation, saturation equality and lifting |
| [RelativeCellBoundaryChallenge.lean](RelativeCellBoundaryChallenge.lean) | 29 | [relative_cell_boundary.json](relative_cell_boundary.json) | 4 theorems: epi membership, exact boundary preimage, complement and normal-form uniqueness |
| [DaggerSimplicialCategoryChallenge.lean](DaggerSimplicialCategoryChallenge.lean) | 73 | [dagger_simplicial_category.json](dagger_simplicial_category.json) | 6 theorems: full mapping-space dagger and inverse enriched opposite functors |
| [FreeSimplicialPathsChallenge.lean](FreeSimplicialPathsChallenge.lean) | 100 | [free_simplicial_paths.json](free_simplicial_paths.json) | 11 theorems: actual finite words, edgewise simplicial operators, reverse and empty/singleton dagger laws |
| [FreeDaggerUniversalChallenge.lean](FreeDaggerUniversalChallenge.lean) | 83 | [free_dagger_universal.json](free_dagger_universal.json) | 1 theorem: existence of a free dagger simplicial category with bijective restriction for every target |
| [DaggerMonadicityChallenge.lean](DaggerMonadicityChallenge.lean) | 160 | [dagger_monadicity.json](dagger_monadicity.json) | 3 theorems: literal isomorphism reflection, monadicity and finitarity of a free/forgetful composite for the actual graph forgetful functor |
| [DaggerGraphPresentableChallenge.lean](DaggerGraphPresentableChallenge.lean) | 74 | [dagger_graph_presentable.json](dagger_graph_presentable.json) | 5 theorems: actual small-index presheaf equivalence, limits/colimits, and graph LFP/LP |

Each file directly imports only pinned Mathlib modules, with its own definitions
visible. None imports `DaggerModels`, a local reference module, or a snapshot of
the implementation. The seventeen Challenges are compiled in separate environments
under the logical module name `Challenge`. Their **1,288 lines in total**, including
comments and blank lines, are the review surface;
reviewing one file does not review the others.

The checker retains the original **21 named library theorems** and adds 68
selected results toward the main theorems, including their statement
dependencies. Three additional reflexive statements make `FreeCofibration`,
`nonDegenerateEquiv`, and `forget` roots of the recursive definition comparison.
These statements are inline in the simplicial-set Challenge; `Contracts.lean`
adds matching roots to the solution environment. They are audit markers, not new
mathematical results, and are not imported by `DaggerModels.lean`.
No definition holes are enabled. [targets.json](targets.json) records the full
92-root coverage set; it is a registry, not an executable Comparator config.

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
boundary inclusions. Its two new conclusions require an actual relative cell
complex for every map satisfying the original `FreeCofibration` condition,
and equality of the stated saturation with that class. No chosen orbit
representatives or cellularity assumption are provided as input. The ordinary
cell specification fixes both the exact boundary preimage and the unique
nondegenerate ancestor/epi map. These two obligations extend the preceding 64
roots to 66; all earlier roots are retained. Tool and dependency pins and both
negative-control definitions are unchanged.

Eighteen further roots protect the new dagger simplicial-category development.
The core specification uses actual SSet-enriched mapping spaces and enriched
opposite functors; dagger commutes with the same simplex operator. It has
independent object and hom universes. The word specification fixes actual
`Quiver.Path` data, edgewise simplicial maps, singleton inclusion, empty-path
identity, and reversal by the original graph dagger. The universal specification
visibly defines both raw bundles and their morphisms, and requires restriction
along a single graph map to be bijective for every target dagger simplicial
category. It quantifies over all object maps and all enriched dagger functors.
It leaves the free witness free; the library supplies the concrete word witness
and an actual adjunction with its unit. This split keeps each problem below
100 lines without importing implementation data or reducing the universal
property. It does not assert monadicity or presentability.

The monadicity specification adds the literal `ReflectsIsomorphisms` and
`Nonempty (MonadicRightAdjoint forgetGraph)` conclusions. Both actual category
structures, their full enriched dagger functors/graph maps, and the original
forgetful functor are visible. Mathlib's monadicity class includes a comparison
equivalence with monad algebras. Its 160 physical lines are covered by a
reviewed, file-specific 160-line budget: this is the only exception to the
100-line budget. It keeps required definitions visible instead of importing
candidate files or weakening the monadicity statement. All preceding 84 roots
remain intact, and the tool/dependency pins and negative controls are unchanged.

This specification also requires a left adjoint to the same `forgetGraph`
whose free/forgetful composite is `ℵ₀`-accessible. The concrete library witness
is the original finite-path adjunction. Its word decomposition uses exact
endpoint pullbacks, and the proof identifies both objects and arbitrary graph
maps with the original free functor. Choosing a left adjoint existentially
preserves the assertion: left adjoints to a fixed functor are naturally
isomorphic, and accessibility is invariant under natural isomorphism.
The seven added physical lines leave every preceding definition and target
unchanged. The registry retains its preceding 91 entries and appends this target.

The graph presentability specification adds five targets with the complete
original graph category visible. It asks for an actual equivalence with
presheaves on some small category and for all small limits/colimits and LFP/LP
at the original value universe. The indexing witness is not fixed by the
Challenge; the library constructs the explicit vertex/edge index and proves
the full equivalence, including natural unit/counit and the triangle law.
This 74-line file extends the preceding 86 roots to 91 without altering them.
It does not conclude LFP for dagger simplicial categories.

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
future declarations. The source-hygiene check enforces the 100-line budget for
the sixteen ordinary Challenges and the explicit 160-line monadicity exception
(including blank lines and comments), plain direct Mathlib imports, standard
permitted axioms, no definition holes, and exact registration of all 92 roots.
This check is not a Lean parser or an adversarial security
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
the Challenge mathematics. The seventeen positive comparisons use current candidate
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
