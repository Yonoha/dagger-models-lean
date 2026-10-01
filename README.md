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
positive degrees, at every value universe. It also constructs genuine dagger
simplicial categories and graphs, their concrete finite-path free category,
and the free–forgetful adjunction with singleton-edge unit. The graph forgetful
functor is proved monadic by constructing its split coequalizers and applying
Beck's theorem. The graph category is equivalent to presheaves on a concrete
small index and is locally finitely presentable, with all small limits and
colimits. The actual finite-word monad is finitary. Monadicity then supplies
all small limits and creates filtered colimits over graphs, with no remaining
finitarity premise. Actual hom quotients of free categories on graph colimits
give all small colimits. A small strong generator of finitely presentable
objects then proves local finite presentability of dagger simplicial categories,
completing `bg.lem.presentable` at every common universe. The ordinary
simplicial-category forgetful functor also creates all small limits and colimits
(`bg.lem.creation`), with independent object, hom, and diagram universes.
The actual two-object free dagger cells have the full universal property
`bg.eq.A-univ` and are finitely presentable for finite simplicial sets. The
underlying free cell is a pushout of its two ordinary one-edge copies. A concrete
right adjoint also proves colimit preservation by ordinary forgetting.
Ordinary simplicial-category colimits are now constructed, completing the
successive-attachment comparison in `bg.lem.reduction`. The actual generator
family `I†` detects object surjectivity and boundary lifting on every hom space.
Ordinary boundary RLP now implies the actual Mathlib Kan fibration property.
Every ordinary simplicial mono has an actual relative boundary-cell presentation;
the boundary-cell closure equals all monos, and their right lifting classes agree.
Boundary RLP also gives one section and one cylinder homotopy satisfying both
endpoint laws and the equation over the original target. The actual local horn
family `J†loc` detects local Kan fibrations. The actual `I†` admits the small
object argument and functorial factorization in `I†.rlp.llp` and `I†.rlp`.
The weak homotopy equivalence comparison, trivial Kan characterization, and
unitary-interval part of `J†` remain unproved. Two concrete comparison obstructions
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
| `bg.def.dagger-scat` | [`DaggerSimplicialCategory`](DaggerModels/DaggerSimplicialCategory.lean) | Full simplicial mapping spaces, the identity-on-objects dagger and its inverse enriched opposite functor, and the category of dagger enriched functors |
| `bg.def.dagger-graph` and the word construction in `bg.lem.presentable` | [`DaggerSimplicialGraph`](DaggerModels/DaggerSimplicialGraph.lean), [`FreeSimplicialPaths`](DaggerModels/FreeSimplicialPaths.lean) | Actual finite paths, including empty and singleton paths; edgewise simplicial operators and reversal with edge dagger |
| Free universal property at the start of `bg.lem.presentable` | [`FreeDaggerSimplicialCategory`](DaggerModels/FreeDaggerSimplicialCategory.lean) | Actual free–forgetful adjunction, singleton-edge unit, and bijective restriction for every target |
| Monadicity in `bg.lem.presentable` | [`DaggerSimplicialMonadicity`](DaggerModels/DaggerSimplicialMonadicity.lean) | Actual graph forgetful functor is monadic, using constructed graph-split coequalizers and isomorphism reflection |
| Graph presentability in the proof of `bg.lem.presentable` | [`DaggerGraphPresheaf`](DaggerModels/DaggerGraphPresheaf.lean), [`DaggerGraphPresentable`](DaggerModels/DaggerGraphPresentable.lean) | Actual small-index presheaf equivalence, all small limits/colimits, and local finite presentability at every common value universe |
| Word finitarity in the proof of `bg.lem.presentable` | [`FreeWordFinitary`](DaggerModels/FreeWordFinitary.lean) | The original free/forgetful endofunctor preserves all small filtered colimits; fixed-length endpoint fibers identify naturally with actual paths |
| Consequences of monadicity and word finitarity | [`DaggerSimplicialLimits`](DaggerModels/DaggerSimplicialLimits.lean), [`DaggerSimplicialFilteredColimits`](DaggerModels/DaggerSimplicialFilteredColimits.lean) | All small limits and filtered colimits exist; the graph forgetful functor creates them. The different ordinary-category forgetful functor is treated separately below |
| Final assertion of `bg.lem.presentable` | [`DaggerSemanticColimit`](DaggerModels/DaggerSemanticColimit.lean), [`DaggerFiniteGenerators`](DaggerModels/DaggerFiniteGenerators.lean), [`DaggerSimplicialPresentable`](DaggerModels/DaggerSimplicialPresentable.lean) | Actual small colimits and a small strong generator of finitely presentable objects give unconditional local finite presentability of the full dagger simplicial category at every common universe |
| `bg.lem.creation` | [`DaggerOrdinaryCreation`](DaggerModels/DaggerOrdinaryCreation.lean) | The actual ordinary simplicial-category forgetful functor creates all small limits and colimits, with no existence premise or restriction on object maps |
| `bg.not.cells`, `bg.eq.A-univ` and its finite compactness assertion | [`TwoObjectDaggerCell`](DaggerModels/TwoObjectDaggerCell.lean), [`TwoObjectCellPresentability`](DaggerModels/TwoObjectCellPresentability.lean) | Actual free two-object cell, unrestricted universal property and finite presentability when the simplicial set has finitely many nondegenerate simplices |
| Ordinary colimits used in `bg.lem.reduction` | [`SimplicialColimits`](DaggerModels/SimplicialColimits.lean) | Actual colimits of all small ordinary simplicial-category diagrams, with arbitrary object maps and no existence premise |
| `bg.lem.reduction` | [`TwoObjectCellReductionResolved`](DaggerModels/TwoObjectCellReductionResolved.lean) | Actual dagger attachment is isomorphic to two successive ordinary attachments along the given edge and its dagger, with both pushouts and all three comparison legs |
| `bg.not.cells`, `bg.def.IJ` and generator lifting in `bg.lem.I-inj` | [`DaggerDiscreteObjects`](DaggerModels/DaggerDiscreteObjects.lean), [`TwoObjectCellLifting`](DaggerModels/TwoObjectCellLifting.lean), [`DaggerGeneratingCofibrations`](DaggerModels/DaggerGeneratingCofibrations.lean) | Actual initial-to-point generator and full boundary family detect object surjectivity plus boundary RLP on every hom; the trivial Kan comparison remains unproved |
| Ordinary inputs to `bg.lem.I-inj` | [`SSetBoundaryFibration`](DaggerModels/SSetBoundaryFibration.lean), [`SSetBoundaryCells`](DaggerModels/SSetBoundaryCells.lean) | Boundary RLP implies actual Mathlib Kan fibrations; every mono is a genuine relative boundary-cell complex; boundary-cell closure equals monos and `I.rlp = monomorphisms.rlp` |
| Section and homotopy input to `bg.lem.I-inj` | [`SSetMonoRLPRetraction`](DaggerModels/SSetMonoRLPRetraction.lean), [`SSetBoundaryRetraction`](DaggerModels/SSetBoundaryRetraction.lean) | The same section and cylinder homotopy satisfy all four equations for mono-RLP or boundary-RLP, with no Kan-object premise or weak-equivalence conclusion |
| Local lifting in `bg.def.IJ` and `bg.lem.Iinj-in-Jinj` | [`DaggerLocalFibrations`](DaggerModels/DaggerLocalFibrations.lean) | Actual `J†loc` RLP is all-hom Mathlib Kan fibrations; actual `I†` RLP implies object surjectivity and this local condition; interval lifting remains open |
| Small-object input to `bg.thm.main` | [`SmallObjectFiniteDomains`](DaggerModels/SmallObjectFiniteDomains.lean), [`DaggerSmallObject`](DaggerModels/DaggerSmallObject.lean) | General finite-domain bridge with explicit smallness/colimit premises; unconditional actual `I†` application and functorial factorization data; no model structure asserted |

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
  Mathlib.AlgebraicTopology.SimplicialSet.Presentable \
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
  Mathlib.CategoryTheory.MorphismProperty.LiftingProperty \
  Mathlib.AlgebraicTopology.SimplicialSet.Monoidal \
  Mathlib.CategoryTheory.Enriched.Opposite \
  Mathlib.CategoryTheory.PathCategory.Basic \
  Mathlib.Combinatorics.Quiver.Symmetric \
  Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer \
  Mathlib.CategoryTheory.Monad.Monadicity \
  Mathlib.CategoryTheory.Monad.Limits \
  Mathlib.CategoryTheory.Presentable.Limits \
  Mathlib.CategoryTheory.Limits.Types.Pullbacks \
  Mathlib.CategoryTheory.Limits.Types.Coproducts \
  Mathlib.CategoryTheory.Quotient \
  Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations \
  Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits \
  Mathlib.CategoryTheory.LiftingProperties.Limits \
  Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting \
  Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms \
  Mathlib.CategoryTheory.SmallObject.Basic
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
Linux GitHub Actions job. It compares 106 selected mathematical results against
twenty-seven self-contained problem specifications:

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
- [Dagger simplicial categories and their opposite functors](.ci/comparator/DaggerSimplicialCategoryChallenge.lean): 73 lines
- [Concrete free paths and their simplicial dagger](.ci/comparator/FreeSimplicialPathsChallenge.lean): 100 lines
- [Free dagger simplicial category universal property](.ci/comparator/FreeDaggerUniversalChallenge.lean): 83 lines
- [Graph forgetful functor: reflection, monadicity and word finitarity](.ci/comparator/DaggerMonadicityChallenge.lean): 160 lines
- [Graph presheaf equivalence and presentability](.ci/comparator/DaggerGraphPresentableChallenge.lean): 74 lines
- [Dagger simplicial category limits, colimits and presentability](.ci/comparator/DaggerSimplicialPresentableChallenge.lean): 93 lines
- [Creation over ordinary simplicial categories](.ci/comparator/DaggerOrdinaryCreationChallenge.lean): 116 lines
- [Two-object dagger cell universal property](.ci/comparator/TwoObjectDaggerCellChallenge.lean): 57 lines
- [Finite presentability of the same universal cell](.ci/comparator/FiniteTwoObjectCellChallenge.lean): 95 lines
- [Ordinary simplicial-category colimits](.ci/comparator/SimplicialColimitsChallenge.lean): 40 lines
- [Initial-to-point object generator](.ci/comparator/DaggerObjectGeneratorChallenge.lean): 91 lines
- [Boundary lifting implies actual Kan fibrations](.ci/comparator/SSetBoundaryFibrationChallenge.lean): 15 lines
- [Ordinary relative boundary cells and lifting-class equality](.ci/comparator/SSetBoundaryCellsChallenge.lean): 27 lines
- [Section and cylinder homotopy from lifting](.ci/comparator/SSetBoundaryRetractionChallenge.lean): 27 lines
- [Small object argument from finitely presentable domains](.ci/comparator/SmallObjectFiniteDomainsChallenge.lean): 21 lines

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
CI checks direct Mathlib imports and coverage of all 109 registered roots
(106 mathematical results and three definition markers). Twenty-five Challenges
have 100-line budgets. The monadicity and ordinary-creation
Challenges have reviewed 160-line and 116-line budgets respectively. Both need
the two full category structures and actual forgetful functor visible, including
structural proofs. The ordinary-creation file still has 101 nonblank lines; its
116-line format preserves readability. The 1,870 lines across all twenty-seven
files are the review surface; checking one file is not a review of the entire
formalization.

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
The new simplicial-category specifications separately protect full mapping-space
dagger, the concrete word operations, and free universality for all graph maps
and all target categories. The last specification fixes the bijective restriction
property, not the implementation's choice of its free object. The library also
constructs the actual adjunction and identifies its unit with singleton inclusion.
The monadicity Challenge directly asks for Mathlib's `MonadicRightAdjoint` for
the original graph forgetful functor. This includes a comparison equivalence
with a category of monad algebras, not just the existence of a left adjoint.
It also requires an actual left adjoint to this same functor whose composite
with it is finitely accessible. The library supplies the original finite-path
adjunction and proves that composite's finitarity. This added statement keeps
all previous definitions and targets and uses the existing 160-line budget.
The graph presentability Challenge asks for an actual equivalence with some
small-index presheaf category and directly states limits, colimits and LFP/LP
for the complete original graph category. It leaves the indexing witness free;
the library constructs its index, both functors, unit/counit and triangle.
The dagger simplicial presentability Challenge includes the original category
and all enriched dagger functors, with the full category structure visible.
Its four targets state small limits, small colimits, LFP and LP directly,
without premises assuming cocompleteness or a strong generator. It adds 93
physical lines and four roots while retaining all preceding 92 targets.
The ordinary-creation Challenge then adds two roots for the actual forgetful
functor to ordinary simplicial categories. It directly requires Mathlib
`CreatesLimitsOfSize` and `CreatesColimitsOfSize` for arbitrary diagram sizes,
with independent object and hom universes. `Nonempty` expresses existence of
the full creation data, including lifting and reflection. All 96 preceding
roots and eighteen Challenges remain unchanged.
The two-object cell Challenges add two further roots, retaining all preceding
98 roots and nineteen specifications. The 57-line statement asks for the actual
classification of all dagger functors by a pair of target objects and an edge
map. The 95-line statement requires the same representing cell to be finitely
presentable when `K.Finite`; this means finitely many nondegenerate simplices,
not merely finite sets in each degree. Both specify full definitions directly
using Mathlib imports. Their witnesses are the actual free cells constructed in
the library. The ordinary-cell pushout and cofree constructions are supporting
proof modules covered by the library audit, not additional Comparator roots.
The ordinary-colimits and object-generator Challenges add 40 and 91 lines,
retaining all preceding 100 roots and twenty-one specifications unchanged.
The former requires actual small colimits of the full ordinary enriched category.
The latter requires one initial object, one terminal object, and the same arrow
between them to detect object surjectivity for every target functor. The library
witnesses are the concrete empty and identity-only one-object categories.
The complete attachment reduction and boundary-RLP characterization are audited
and separately reviewed supporting results, not separate Comparator roots.
That stage had 23 Challenges and 102 roots. The four ordinary-lifting and
small-object Challenges add 90 lines and seven roots while retaining those
23 specifications, their 23 configurations, and all 102 ordered roots unchanged.
Four new roots protect the ordinary Kan consequence, actual relative cells,
cell-closure equality and `I.rlp` equality. Two protect the same section and
homotopy with all four laws. The last protects the general finite-domain small
object theorem, with its explicit assumptions. The actual `J†loc` equivalence
and unconditional actual `I†` factorization are separately reviewed and audited
applications, not additional Comparator roots. The new tranche has passed local
fresh compilation, exact root-header comparison and a 2,544-declaration audit;
these checks do not substitute for its exact-commit Linux run.

## Citing this version

Use the [v0.1.0 release](https://github.com/Yonoha/dagger-models-lean/releases/tag/v0.1.0)
and its tagged source when citing the first version. GitHub citation metadata is
provided in [CITATION.cff](CITATION.cff). For an immutable reference, record the
full commit hash shown in the release notes as well.
The presheaf, free-adjunction, cellular, dagger simplicial-category, ordinary-lifting,
small-object and comparison-obstruction developments described above are newer than
v0.1.0; cite the corresponding development commit when referring to them.

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

The cellular characterization, free dagger simplicial-category adjunction and
monadicity over dagger graphs, and graph presheaf equivalence/presentability
are complete. The original word monad is finitary, and dagger simplicial categories
have all small limits and colimits and are locally finitely presentable.
The ordinary-category forgetful assertion in `bg.lem.creation` is also proved.
The actual two-object free cells, their finite presentability, the underlying
free-cell pushout, ordinary colimit existence, and full successive-attachment
comparison are proved. The actual `I†` lifting condition is characterized by
object surjectivity and ordinary boundary lifting on all hom spaces. Boundary
lifting now gives actual local Kan fibrations and a section/cylinder homotopy;
all ordinary monos have actual relative boundary-cell presentations. The actual
`I†` has functorial factorization from the small object argument. The missing
ordinary input is the comparison with actual weak homotopy equivalences and
trivial Kan fibrations. The next stages toward A–D also include unitary interval
lifting, the rest of the ordinary Kan–Quillen comparison,
rigidification and coherent nerve, their lifted adjunction, and the model structures. These
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
また、dagger simplicial category と graph、具体的な有限の道による自由圏、
および自由・忘却随伴と singleton-edge unit を構成しました。
さらに、実際の分裂余等化子を構成し、graph への忘却関手の monadicity を証明しました。
graph の圏についても、実際の前層圏との圏同値、全ての小極限・小余極限、
および局所有限可呈示性を証明しました。
元の有限の道による word monad の finitarity も証明し、dagger simplicial category の
全ての小極限と filtered colimit の存在、および graph への忘却関手による生成を示しました。
さらに、自由圏の hom の商として一般の小余極限を構成し、有限可呈示な対象からなる
小さい強生成系と合わせて、dagger simplicial category の局所有限可呈示性を証明しました。
これにより `bg.lem.presentable` の結論全体を証明しました。
通常の simplicial category への忘却関手が全ての小極限・小余極限を創出する
`bg.lem.creation` も証明しました。対象・hom・図式の universe は独立で、
対象写像を固定する条件や極限・余極限の存在を仮定する条件は追加していません。
二対象自由 dagger セルの普遍性 `bg.eq.A-univ` と、有限 simplicial set に対する
同じセルの有限可呈示性も証明しました。それぞれ 57 行・95 行の Challenge で照合します。
underlying 自由セルの二つの通常セルによる pushout 分解と、忘却関手の具体的な右随伴も
構成しています。通常の simplicial category の小余極限を実際に構成することで、
セル付加の還元補題 `bg.lem.reduction` 全体も証明しました。
また、実際の生成射族 `I†` に対する右持ち上げ条件が、対象上の全射性と全ての hom の
境界持ち上げ条件に同値であることを証明しました。trivial Kan fibration との比較は未完了です。
さらに通常の境界 RLP から実際の Mathlib Kan fibration を導き、任意の通常の mono の
実相対境界セル表示、境界セル閉包と mono 全体の一致、および右持ち上げ類の一致を証明しました。
同じ section と cylinder homotopy が、両端と元の target 上の四式を満たすことも証明しました。
実 `J†loc` の RLP は全ての hom が Kan fibration であることに同値です。
実 `I†` の small object argument と、`I†.rlp.llp`・`I†.rlp` による関手的分解も証明しました。
今回の４ Challenges は 15・27・27・21 行で、既存23本と102 rootsをそのまま保持します。
全体は27本・1,870行・109 roots（数学106、定義marker3）です。
弱ホモトピー同値・trivial Kan fibration との同定と `J†` の interval 部分は未完了で、
論文の主定理 A–D 全体を Lean で証明したという意味ではありません。
対応する箇所と未実装の範囲は [CORRESPONDENCE.md](CORRESPONDENCE.md) に記載しています。
