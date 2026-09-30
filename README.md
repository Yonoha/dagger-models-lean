# Dagger models in Lean

[![Lean verification](https://github.com/Yonoha/dagger-models-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/Yonoha/dagger-models-lean/actions/workflows/lean.yml)
[![Comparator](https://github.com/Yonoha/dagger-models-lean/actions/workflows/comparator.yml/badge.svg)](https://github.com/Yonoha/dagger-models-lean/actions/workflows/comparator.yml)

A **partial formalization** accompanying Keima Akasaka's *Models for dagger
$(\infty,1)$-categories I: Dagger simplicial sets and unitary cores*.

The first release formalizes foundational definitions and elementary lemmas.
**The main theorems A–D of the paper are not yet formalized.** In particular,
this repository does not yet prove the dagger Bergner or dagger Joyal model
structures, the rigidification Quillen equivalence, the intrinsic recognition
theorem, or the comparison with anti-involutive simplicial sets.

## What is checked

| Paper construction or argument | Lean content | Scope |
| --- | --- | --- |
| The reversal simplex category before `prop.sSetdag_is_equivalent_to_Fun` | [`ReverseSimplex`](DaggerModels/ReverseSimplex.lean) | Category of actual monotone or antitone functions, reversal involution, inclusion of the simplex category, reversal relation, and the ambiguity only on constant functions |
| `def.dagger_simplicial_sets` and the following simplicial identities | [`DaggerSSet`](DaggerModels/SimplicialSet.lean) | Definition, dagger morphisms and their category, faithful forgetful functor, and reversal identities for face and degeneracy maps |
| The opening nondegeneracy argument of `dj.lem.free-cof` | `dagger_mem_nonDegenerate_iff`, `nonDegenerateEquiv` | Dagger preserves and reflects nondegeneracy |
| `dj.def.free-cof` | `FreeCofibration` | The definition only; no cellular characterization |
| The last obstruction in the proof of `dj.prop.counterexample` | [`WordObstruction`](DaggerModels/WordObstruction.lean) | The algebraic vertex-level argument: no self-adjoint word of length one, hence no dagger-preserving section of the length map |

[CORRESPONDENCE.md](CORRESPONDENCE.md) explains the translation and what remains
outside the verified statements. Labels refer to the Part I manuscript inspected
on 2026-10-01; they are used instead of potentially changing theorem numbers.

## Reproduce the verification

Install Lean using the [Lean community instructions](https://leanprover-community.github.io/install/project.html).
The repository selects its own toolchain; no manual Lean version choice is needed.

```sh
git clone https://github.com/Yonoha/dagger-models-lean.git
cd dagger-models-lean
git checkout v0.1.0
lake exe cache get Mathlib.AlgebraicTopology.SimplicialSet.Op Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
lake build
lake env lean Audit.lean
python3 scripts/check_audit.py
```

The pinned versions are Lean **4.27.0** and mathlib commit
[`a3a10db0e9d66acbebf76c5e6a135066525ac900`](https://github.com/leanprover-community/mathlib4/tree/a3a10db0e9d66acbebf76c5e6a135066525ac900).
`lake-manifest.json` also fixes the transitive dependency revisions.
Downloading the mathlib cache speeds up the build; the proof source is in the
three files imported by `DaggerModels.lean`.

The [GitHub workflow](.github/workflows/lean.yml), using the official
[Lean action](https://github.com/leanprover/lean-action), runs the same build and
audit on pushes and pull requests. Python is needed only for the audit's
negative controls, not to check the mathematical proofs.

## What the audit guarantees

[`Audit.lean`](Audit.lean) traverses the transitive axiom dependencies of every
loaded declaration in the `DaggerModels` namespace, including definitions and
generated declarations. It permits only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. In particular, `sorryAx` and additional
unproved axioms are rejected. The library also treats warnings as errors.

[`scripts/check_audit.py`](scripts/check_audit.py) checks that the audit actually
rejects both a deliberately incomplete proof and a new axiom in temporary files.
These files are not part of the library. A successful build checks the encoded
statements, with the usual trust in Lean and the pinned dependency artifacts;
matching those statements to the paper remains a mathematical review task.

## Preserving the intended statements

The current development branch additionally runs
[leanprover/comparator](https://github.com/leanprover/comparator) in a separate
Linux GitHub Actions job. It compares all 21 named library theorems against the
independently fetched, immutable v0.1.0 commit. Three audit-only roots also
protect the definitions of `FreeCofibration`, `nonDegenerateEquiv`, and `forget`.
It checks the statement dependencies, permitted axioms, and exported kernel
proofs. Deliberately weakened statements and changed definitions must be
rejected. See [.ci/comparator/README.md](.ci/comparator/README.md) for the exact
scope, trusted inputs, sandbox, and reference-update procedure.

[`formalization.yaml`](formalization.yaml) follows the
[mathlib-initiative reporting standard](https://github.com/mathlib-initiative/formalization.yaml).
It records the source, partial scope, AI assistance, proof status, axioms, and
source-to-Lean correspondence. Review status is **agent-reviewed**; no independent
human review is claimed. CI checks it against the vendored upstream v0.4 schema
and compares its reported axioms with the dependencies collected from Lean.

To run the metadata check on this development version after `lake build`:

```sh
python3 -m venv build/metadata-venv
build/metadata-venv/bin/python -m pip install -r .ci/requirements.txt
lake env lean scripts/ReportAxioms.lean > build/axioms.json
build/metadata-venv/bin/python scripts/check_metadata.py --axioms build/axioms.json
```

These additional checks were introduced after the immutable v0.1.0 release.
Comparator preserves the chosen Lean baseline; mathematical review is still
needed to establish that the baseline expresses the manuscript correctly.

## Citing this version

Use the [v0.1.0 release](https://github.com/Yonoha/dagger-models-lean/releases/tag/v0.1.0)
and its tagged source when citing the first version. GitHub citation metadata is
provided in [CITATION.cff](CITATION.cff). For an immutable reference, record the
full commit hash shown in the release notes as well.

Suggested wording:

> A partial Lean 4 formalization of the foundational constructions is available
> in the companion repository, version 0.1.0. Its verified scope and the
> correspondence with the manuscript are documented there.

## Development

The next mathematical milestones are the presheaf equivalence in
`prop.sSetdag_is_equivalent_to_Fun`, the free dagger completion, and the cellular
description in `dj.lem.free-cof`. These are planned work, not axioms or incomplete
theorems in this release. Extending to the main model-categorical theorems will
also require substantial ordinary simplicial and homotopical infrastructure.

This companion was developed with AI assistance. The source, precise scope, and
verification workflow are public so that its mathematical content can be reviewed.
Original project code and documentation are distributed under Apache-2.0; see
[LICENSE](LICENSE). Dependencies retain their own licenses. The license does not
apply to the separately maintained manuscript.

日本語: この初版で検証済みなのは基礎的な定義・補題と反例の一部分です。
論文の主定理全体を Lean で証明したという意味ではありません。
対応する箇所と未実装の範囲は [CORRESPONDENCE.md](CORRESPONDENCE.md) に記載しています。
