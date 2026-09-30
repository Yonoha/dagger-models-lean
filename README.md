# Dagger models in Lean

[![Lean verification](https://github.com/Yonoha/dagger-models-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/Yonoha/dagger-models-lean/actions/workflows/lean.yml)
[![Comparator](https://github.com/Yonoha/dagger-models-lean/actions/workflows/comparator.yml/badge.svg)](https://github.com/Yonoha/dagger-models-lean/actions/workflows/comparator.yml)

A **partial formalization** accompanying Keima Akasaka's *Models for dagger
$(\infty,1)$-categories I: Dagger simplicial sets and unitary cores*.

The current development proves the presheaf equivalence and presentability,
constructs the free–forgetful adjunction with its explicit zero-skeleton pushout,
unit and swap dagger, and proves the closure of free cofibrations under
composition, coproducts, pushouts, transfinite composition, and retracts.
The full cellular characterization `dj.lem.free-cof` is proved: every free
cofibration has an actual relative presentation by free boundary cells, and
their saturation equals the original free-cofibration class. The construction
attaches individual new vertices in degree zero and free dagger orbits in
positive degrees, at every value universe. Two concrete comparison obstructions
and the first release's elementary foundations are retained.
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
| `dj.def.free-cof` and closure arguments of `dj.lem.free-cof` | [`FreeCofibration`](DaggerModels/FreeCofibration.lean), [`FreeCofibrationClosure`](DaggerModels/FreeCofibrationClosure.lean) | Original definition, underlying monicity comparison, identities, composition, coproducts, pushouts, continuous transfinite composition, and retracts |
| `dj.cor.Fdag-free` and the closure direction of `dj.lem.free-cof` | [`FreeDaggerCofibration`](DaggerModels/FreeDaggerCofibration.lean), [`FreeBoundary`](DaggerModels/FreeBoundary.lean) | Every simplicial mono becomes free; actual boundary-generator saturation is contained in free cofibrations; exact underlying boundary lifting condition |
| `dj.lem.free-cof` (both conclusions) | [`RelativeCellPresentation`](DaggerModels/RelativeCellPresentation.lean) | Every free cofibration is an actual relative free-boundary-cell complex; the saturation of the free boundary generators equals free cofibrations |
| Skeletal construction in `dj.lem.free-cof` | [`RelativeSkeleton`](DaggerModels/RelativeSkeleton.lean), [`RelativeCellBoundary`](DaggerModels/RelativeCellBoundary.lean) | Actual dagger-stable relative stages, source and colimit identifications, boundary preimage, and unique nondegenerate ancestor/degeneracy map, used in the attachment pushouts |
| The last obstruction in the proof of `dj.prop.counterexample` | [`WordObstruction`](DaggerModels/WordObstruction.lean) | The algebraic vertex-level argument: no self-adjoint word of length one, hence no dagger-preserving section of the length map |
| `prop.sSetdag_is_equivalent_to_Fun` | [`Presheaf`](DaggerModels/Presheaf.lean), [`Presentable`](DaggerModels/Presentable.lean) | Actual category equivalence, all small limits and colimits, and local finite presentability, at every value universe |
| Free–forgetful adjunction in `dj.not.adjunctions` | [`FreeDagger`](DaggerModels/FreeDagger.lean), [`FreeDaggerPushout`](DaggerModels/FreeDaggerPushout.lean), [`FreeDaggerSkeleton`](DaggerModels/FreeDaggerSkeleton.lean) | Actual left adjoint, naturally identified with the explicit zero-skeleton pushout; unit, swap and all small limits/colimits preservation by forget proved |
| The common zero-skeleton in `dj.not.adjunctions` | [`Vertices`](DaggerModels/Vertices.lean) | Constant vertices identify with the actual zero-skeleton, preserving its inclusion; mathlib uses `skeleton 1` for the paper's `sk₀` |
| Cofibration obstruction in `pointset.cor.cofibrant-obstruction` | [`NormalCofibrationObstruction`](DaggerModels/NormalCofibrationObstruction.lean) | Initial-to-point map is free but its anti-involutive image is not normal; model structures and Quillen claims are not assumed |
| Parts (1)–(2) of `pointset.prop.weak-counterexample` | [`UnitaryObstruction`](DaggerModels/UnitaryObstruction.lean) | The actual integer dagger groupoid inclusion is an ordinary equivalence but is not unitarily essentially surjective |

[CORRESPONDENCE.md](CORRESPONDENCE.md) explains the translation and what remains
outside the verified statements. Labels refer to the Part I manuscript inspected
on 2026-10-01; they are used instead of potentially changing theorem numbers.
[MAIN_THEOREMS.md](MAIN_THEOREMS.md) records the complete A–D objective, its
remaining proof dependencies, and a malformed source statement found during
formalization. These remaining results are not postulated as axioms.

## Reproduce the verification

Install Lean using the [Lean community instructions](https://leanprover-community.github.io/install/project.html).
The repository selects its own toolchain; no manual Lean version choice is needed.

```sh
git clone https://github.com/Yonoha/dagger-models-lean.git
cd dagger-models-lean
git checkout codex/part1-foundations
lake exe cache get \
  Mathlib.AlgebraicTopology.SimplicialSet.Op \
  Mathlib.AlgebraicTopology.SimplicialSet.Degenerate \
  Mathlib.CategoryTheory.Groupoid Mathlib.Data.Int.Basic \
  Mathlib.Data.Quot \
  Mathlib.CategoryTheory.Presentable.Presheaf \
  Mathlib.CategoryTheory.Presentable.Type \
  Mathlib.CategoryTheory.Presentable.Adjunction \
  Mathlib.CategoryTheory.Functor.KanExtension.Adjunction \
  Mathlib.CategoryTheory.Limits.Types.Colimits \
  Mathlib.AlgebraicTopology.SimplicialSet.Skeleton \
  Mathlib.CategoryTheory.Adjunction.Unique \
  Mathlib.CategoryTheory.Limits.Types.Pushouts \
  Mathlib.CategoryTheory.MorphismProperty.Retract \
  Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory \
  Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition \
  Mathlib.CategoryTheory.MorphismProperty.FunctorCategory \
  Mathlib.CategoryTheory.Types.Monomorphisms \
  Mathlib.AlgebraicTopology.SimplicialSet.Boundary \
  Mathlib.AlgebraicTopology.RelativeCellComplex.Basic \
  Mathlib.CategoryTheory.LiftingProperties.Adjunction \
  Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
lake build
lake env lean Audit.lean
python3 scripts/check_audit.py
```

The pinned versions are Lean **4.27.0** and mathlib commit
[`a3a10db0e9d66acbebf76c5e6a135066525ac900`](https://github.com/leanprover-community/mathlib4/tree/a3a10db0e9d66acbebf76c5e6a135066525ac900).
`lake-manifest.json` also fixes the transitive dependency revisions.
Downloading the mathlib cache speeds up the build; the proof source is in the
modules imported by `DaggerModels.lean`. Record the checked commit hash for an
immutable reference; the development branch can advance.

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
Linux GitHub Actions job. It compares 63 selected library theorems against twelve
short, self-contained problem specifications:

- [Reversal simplex category](.ci/comparator/ReverseSimplexChallenge.lean): 72 lines
- [Dagger simplicial sets](.ci/comparator/SimplicialSetChallenge.lean): 96 lines
- [Word obstruction](.ci/comparator/WordObstructionChallenge.lean): 22 lines
- [Presheaf equivalence, presentability, and free adjunction](.ci/comparator/PresheafChallenge.lean): 92 lines
- [Free versus normal cofibration obstruction](.ci/comparator/NormalCofibrationChallenge.lean): 88 lines
- [Ordinary versus unitary equivalence obstruction](.ci/comparator/UnitaryObstructionChallenge.lean): 44 lines
- [Free-cofibration closure and the forgetful functor](.ci/comparator/FreeCofibrationChallenge.lean): 91 lines
- [Vertices and the actual zero-skeleton](.ci/comparator/VerticesChallenge.lean): 28 lines
- [Explicit free-completion pushout, unit and swap](.ci/comparator/FreeDaggerPushoutChallenge.lean): 88 lines
- [Actual relative skeletal filtration](.ci/comparator/RelativeSkeletonChallenge.lean): 55 lines
- [Free monomorphisms, cellular characterization and lifting](.ci/comparator/FreeDaggerCofibrationChallenge.lean): 93 lines
- [Boundary preimages and relative-cell normal forms](.ci/comparator/RelativeCellBoundaryChallenge.lean): 29 lines

Each Challenge directly imports only pinned Mathlib modules and contains the
definitions and theorem statements to review. It does not import this library
or a copy of the implementation. Three audit-only roots also protect the
definitions of `FreeCofibration`, `nonDegenerateEquiv`, and `forget`.
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

The intentional `sorry` placeholders in the trusted Challenges mean "prove this
statement"; they are excluded from the library and are not claimed as proofs.
The actual library must remain free of proof holes and extra axioms.
CI checks each Challenge's 100-line budget, direct Mathlib imports, and coverage
of all 66 registered roots. The 798 lines across all twelve files are the review
surface; checking one file is not a review of the entire formalization.

These additional checks were introduced after the immutable v0.1.0 release.
Comparator verifies agreement with the Challenges; mathematical review must
still establish that those Challenges express the manuscript correctly.
The new existential goals fix the actual mathematical assertions while leaving
the proof's choice of witness free. For example, the integer-groupoid Challenge
requires actual groupoids and a dagger functor with the stated categorical
properties; it does not require duplicating the integer construction in the
problem statement. Auxiliary implementation lemmas are not all separate
Comparator roots, but the library audit includes every loaded declaration.
The explicit free-completion targets retain the actual adjunction unit,
natural right coprojection, pushout universal property, and both swap equations.
They apply to every free–forgetful adjunction, including the original Kan
construction. The zero-skeleton target also pins its canonical inclusion.

## Citing this version

Use the [v0.1.0 release](https://github.com/Yonoha/dagger-models-lean/releases/tag/v0.1.0)
and its tagged source when citing the first version. GitHub citation metadata is
provided in [CITATION.cff](CITATION.cff). For an immutable reference, record the
full commit hash shown in the release notes as well.
The presheaf, free-adjunction, cellular, and comparison-obstruction developments
described above are newer than v0.1.0; cite the corresponding development commit
when referring to them.

Suggested wording:

> A partial Lean 4 formalization of the foundational constructions is available
> in the companion repository, version 0.1.0. Its verified scope and the
> correspondence with the manuscript are documented there.

## Development

[`AGENTS.md`](AGENTS.md) records the development policy: use GPT-6.1-Sol with
`xhigh` effort for implementation from detailed proofs and for a separate
statement review; reserve `ultra` for a concrete difficult obstacle, and
distinguish that obstacle from missing mathematics that may call for Astra.
These are task roles, not a claim that the main chat's model changes itself.

The [lean4 skill](https://github.com/cameronfreer/lean4-skills) supplies
statement-preservation, mathlib-search, and proof-review guidance. Its core skill
and references were installed and read during the Challenge redesign; optional
helper scripts, lifecycle hooks, and Lean LSP integration are not part of that
installation. The repository's Lean/Lake build and audits are the verification
commands. See `AGENTS.md` for the pinned skill revision and usage instructions.

The cellular characterization is complete. The next stage toward A–D requires
actual dagger simplicial categories, ordinary rigidification and coherent
nerve, their lifted adjunction, and the model structures themselves. These
requirements are recorded in [MAIN_THEOREMS.md](MAIN_THEOREMS.md); they are not
assumed as axioms in the current proofs.

This companion was developed with AI assistance. The source, precise scope, and
verification workflow are public so that its mathematical content can be reviewed.
Original project code and documentation are distributed under Apache-2.0; see
[LICENSE](LICENSE). Dependencies retain their own licenses. The license does not
apply to the separately maintained manuscript.

日本語: 現在の開発版では、基礎的な定義・補題に加え、前層の圏同値と局所可呈示性、
自由・忘却随伴とその零次骨格に沿う pushout 表示、自由 cofibration の coproduct・
pushout・超限合成・レトラクト等による閉性を検証しています。
さらに `dj.lem.free-cof` の両方の結論を証明しました。
全ての自由 cofibration に対して実際の相対境界セル複体を構成し、
自由境界生成射の飽和閉包と自由 cofibration 全体の一致を示しています。
次数 0 では新しい頂点ごと、正次数では dagger 軌道ごとにセルを貼り付けます。
論文の主定理全体を Lean で証明したという意味ではありません。
対応する箇所と未実装の範囲は [CORRESPONDENCE.md](CORRESPONDENCE.md) に記載しています。
