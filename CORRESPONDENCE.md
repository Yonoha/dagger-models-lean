# Correspondence with Part I

Scope of the current development, based on the manuscript inspected on 2026-10-01.
Version 0.1.0 remains the immutable initial foundations release.
Names below are in the `DaggerModels` namespace. A definition being implemented
does not mean that every subsequent theorem about it has been proved.

The current branch supplies twelve self-contained Comparator Challenges for
reviewing its mathematical scope. Each imports only Mathlib; definitions
are visible in the Challenge rather than imported from this implementation.
The intentional theorem-proof placeholders are specification markers, not
unproved library results. A reviewer must inspect all twelve files to review the
whole checked scope. Comparator checks correspondence between their Lean
statements and the implementation, not the translation from the manuscript.

## The reversal simplex category

File: [DaggerModels/ReverseSimplex.lean](DaggerModels/ReverseSimplex.lean).
Problem specification: [ReverseSimplexChallenge.lean](.ci/comparator/ReverseSimplexChallenge.lean).

`ReverseSimplex` has an object for each natural number `n`, representing `[n]`.
Its morphisms are functions `Fin (m + 1) → Fin (n + 1)` together with the
**proposition** that the function is monotone or antitone. The orientation is
not a separate tag. `Hom.ext` identifies morphisms with equal underlying
functions; in particular, a constant function is one morphism, even though it
has both properties.

The category laws, reversal involution (`reversal_comp_reversal`), triviality
of reversal at `[0]` (`reversal_zero`), the inclusion from the ordinary simplex
category, and the reversal commutation relation (`reversal_naturality`) are
proved. `monotone_antitone_iff_constant` identifies the overlap of the two
orientation properties. This implements the index category in the definition
immediately preceding `prop.sSetdag_is_equivalent_to_Fun`.

The presheaf equivalence and presentability are proved in the modules below.
Comparison with the appendix's tagged index category remains to implement.

## Dagger simplicial sets

File: [DaggerModels/SimplicialSet.lean](DaggerModels/SimplicialSet.lean).
Problem specification: [SimplicialSetChallenge.lean](.ci/comparator/SimplicialSetChallenge.lean).

`DaggerSSet` implements `def.dagger_simplicial_sets` using mathlib's `SSet` and
`SSet.op`. It contains a natural transformation to the opposite simplicial set,
the degreewise involution equation, and the equation fixing **all vertices**.
The componentwise involution equation uses `SSet.opObjEquiv` to identify the
underlying sets in a fixed degree; it is the componentwise formulation of the
paper's equation that applying the opposite dagger after dagger is the identity.

`DaggerSSet.Hom` implements the commuting square for dagger morphisms. The
category laws and the faithful forgetful functor are proved. The lemmas
`dagger_map`, `dagger_δ`, and `dagger_σ` give the simplicial reversal relations
following the definition. `selfConjugate_edge_endpoints` proves that a
self-conjugate edge has equal endpoints, as used in the discussion of the
self-adjoint generator.

The proof of `dj.lem.free-cof` begins by asserting that reversal preserves and
reflects nondegeneracy. This is formalized as
`dagger_mem_nonDegenerate_iff`; `nonDegenerateEquiv` restricts dagger to a
bijection on nondegenerate simplices in each degree. The proof uses mathlib's
definition of degenerate simplices and dagger naturality.

`FreeCofibration f` implements `dj.def.free-cof`: it requires `Mono f` in the
category of dagger simplicial sets, and every positive-dimensional
nondegenerate simplex outside the degreewise range of `f` must differ from its
dagger. It does not assume a model structure. The full equivalence with the
boundary-generated class is proved in the cellular construction below.

**Not yet proved:** the model structures, rigidification, or results about
fibrant objects. The free adjunction, closure properties, and cellular
characterization are described below.

## Elementary free-cofibration properties

Files: [FreeCofibration.lean](DaggerModels/FreeCofibration.lean),
[FreeCofibrationPushout.lean](DaggerModels/FreeCofibrationPushout.lean),
[FreeCofibrationCoproduct.lean](DaggerModels/FreeCofibrationCoproduct.lean),
[FreeCofibrationTransfinite.lean](DaggerModels/FreeCofibrationTransfinite.lean),
[FreeCofibrationClosure.lean](DaggerModels/FreeCofibrationClosure.lean).
Problem specification: [FreeCofibrationChallenge.lean](.ci/comparator/FreeCofibrationChallenge.lean).

`mono_iff_mono_hom` proves that the original categorical monicity condition in
`FreeCofibration` agrees with underlying simplicial monicity. The proof uses
the actual free–forgetful adjunction and faithfulness of the forgetful functor;
the definition has not been replaced. Identities and composites are free.
`FreeCofibration.of_retract` implements the final retract argument of
`dj.lem.free-cof`: the section preserves nondegeneracy, the retraction detects
whether a simplex lies in the original image, and dagger compatibility
transports a hypothetical fixed point to a contradiction.

`FreeCofibration.of_isPushout` proves closure under any actual dagger-category
pushout square, as in the pushout paragraph of `dj.lem.free-cof`. The forgetful
functor and evaluation give genuine pushouts of types. A pushout identifies no
distinct elements outside the attaching image, proved directly from its
universal property. A hypothetical new fixed nondegenerate simplex therefore
lifts to one violating the original freeness hypothesis. The other attaching
map is arbitrary; it is not assumed monic.

`FreeCofibration.of_coproduct` uses actual specified coproduct cocones, whose
degreewise images are disjoint unions. `of_transfiniteCompositionOfShape`
uses a genuine well-order-continuous diagram and colimit. Transition maps and
colimit inclusions are proved monic; successor/limit induction forces a fixed
positive nondegenerate simplex to come from the bottom stage. Its index type
is `J : Type u`, matching the arbitrary simplex universe. `freeCofibrations_saturated`
packages the proved closure under coproducts, pushouts, transfinite composition,
and retracts. This closure result is one ingredient in the equality with the
boundary-generated class proved below.

`forget_preservesLimits` and `forget_preservesColimits` in `FreeDagger.lean`
prove that the original forgetful functor preserves all `u`-small limits and
colimits. Colimits are preserved because the functor is presheaf restriction
after the actual presheaf equivalence; no new adjoint or presentability
hypothesis is assumed. These are infrastructure for the cellular argument.
`ForgetfulReflection.lean` proves that an inverse underlying simplicial map
is dagger-compatible and hence that the forgetful functor reflects isomorphisms.
Together with existence and preservation, this proves reflection of colimits.

## Free boundary generators and the relative filtration

Files: [FreeDaggerCofibration.lean](DaggerModels/FreeDaggerCofibration.lean),
[FreeBoundary.lean](DaggerModels/FreeBoundary.lean),
[RelativeSkeleton.lean](DaggerModels/RelativeSkeleton.lean),
[RelativeCellBoundary.lean](DaggerModels/RelativeCellBoundary.lean).
Specifications: [FreeDaggerCofibrationChallenge.lean](.ci/comparator/FreeDaggerCofibrationChallenge.lean),
[RelativeSkeletonChallenge.lean](.ci/comparator/RelativeSkeletonChallenge.lean),
[RelativeCellBoundaryChallenge.lean](.ci/comparator/RelativeCellBoundaryChallenge.lean).

`freeDagger_map_freeCofibration` proves `dj.cor.Fdag-free` for any actual
adjunction `F ⊣ forget`, with the original canonical free functor as a proved
specialization. The degreewise two-copy pushout proves mono preservation;
its mixed-copy equality reflects the common totally degenerate vertices.
Every positive nondegenerate simplex in a free object has nonfixed dagger.
No freeness hypothesis on the input simplicial set is added.

`freeBoundaryGenerators F` consists of the actual maps `F.map (boundary n).ι`.
Their saturation is contained in `FreeCofibration`. An actual relative cell
complex built from them is therefore free. These results supply one direction
of the full characterization constructed below. `freeBoundary_rlp_iff`
identifies lifting against these generators with underlying lifting against
all ordinary boundaries. It does not assume or construct a Kan model structure.

`relativeSkeleton` is literally the dagger restriction to
`range i.hom ⊔ Y.toSSet.skeleton n`. Stage zero is identified with the given
source while preserving `i`, and the target is the genuine colimit. The
Challenge permits a choice of diagram data but fixes every stage's subobject
and inclusion, as well as the original map and colimit universal property.
Since the inclusions are monic, their dagger and transition maps are forced.
The indexing is exact: mathlib stage `n + 1` is the paper's `B_{≤n}`.

The ordinary characteristic map of a new nondegenerate `n`-simplex has inverse
image of the preceding stage exactly `boundary n`, including `n = 0`.
It is not assumed monic: a nondegenerate simplex can have identified vertices.
The stage complement is exactly the set of degeneracies of new nondegenerate
`n`-simplices, with unique ancestor and epi degeneracy map, using the genuine
Eilenberg–Zilber results.

## The full cellular characterization

Main file: [RelativeCellPresentation.lean](DaggerModels/RelativeCellPresentation.lean).
Problem specification: [FreeDaggerCofibrationChallenge.lean](.ci/comparator/FreeDaggerCofibrationChallenge.lean).

`exists_relativeFreeBoundaryCellComplex` proves the relative-cell assertion of
`dj.lem.free-cof`. Its only hypothesis on the original map is `FreeCofibration`;
neither orbit representatives nor cellularity are added as assumptions.
The proof constructs actual `AttachCells` data at every successor stage of
the original relative skeleton, retaining its source identification, original
map, and target colimit.

[FreeInvolution.lean](DaggerModels/FreeInvolution.lean) and
[RelativeCellOrbits.lean](DaggerModels/RelativeCellOrbits.lean) construct the
orbit quotient and select representatives using `Quotient.out`. In positive
degrees, the original freeness condition makes each orbit a free pair.
Degree zero is treated separately: the cells are indexed by individual new
vertices, and no nonfixedness is asserted there.

[FreeDaggerCell.lean](DaggerModels/FreeDaggerCell.lean) identifies the interiors
of the actual free cells. A positive cell has two copies of epi simplex maps;
the two copies of a zero-cell coincide. On the right copy, the characteristic
map has value `map (rev α) (dagger σ)`, with the reversal retained.
[RelativeCellMaps.lean](DaggerModels/RelativeCellMaps.lean) constructs the
characteristic and boundary maps by the actual free adjunction. Characteristic
maps are never assumed monic.

[RelativeCellIntersection.lean](DaggerModels/RelativeCellIntersection.lean),
[RelativeCellCoverage.lean](DaggerModels/RelativeCellCoverage.lean), and
[RelativeCellSeparation.lean](DaggerModels/RelativeCellSeparation.lean) prove
the exact boundary intersection, coverage of the next stage, and uniqueness
outside the boundaries. These imply actual degreewise pushouts and hence
dagger-category pushouts, using
[DegreewisePushout.lean](DaggerModels/DegreewisePushout.lean) and
[CoproductAttachment.lean](DaggerModels/CoproductAttachment.lean).

[BoundaryCellTransport.lean](DaggerModels/BoundaryCellTransport.lean)
transports the cells from the explicit free functor to any actual left adjoint
of the original forgetful functor. It also transports the countable stage
order from `ℕ` to `ULift.{u} ℕ`, so the transfinite-composition universe remains
the arbitrary value universe `u`.

`freeBoundarySaturation_eq` proves the exact equality of the original
free-cofibration class with coproducts of free boundaries followed by pushouts,
transfinite compositions, and retracts. `canonical_freeBoundarySaturation_eq`
specializes this to the original canonical free functor. Thus **both conclusions
of `dj.lem.free-cof` are proved**. This does not yet construct a model structure
or establish main theorems A–D.

## Presheaf equivalence and presentability

Files: [Presheaf.lean](DaggerModels/Presheaf.lean),
[Presentable.lean](DaggerModels/Presentable.lean).
Problem specification: [PresheafChallenge.lean](.ci/comparator/PresheafChallenge.lean).

`daggerSSetEquivalencePresheaf` constructs an actual
`DaggerSSet.{u} ≌ (ReverseSimplexᵒᵖ ⥤ Type u)` for arbitrary `u`.
It extends simplicial pullbacks to antitone maps by reversing the target and
using dagger. When a function is both monotone and antitone, it is constant;
factorization through `[0]` and fixed vertices prove agreement of the formulas.
All four composition cases, extension on natural transformations, restriction
with dagger given by reversal, the natural unit and counit, and the triangle
identity are proved. This establishes the equivalence clause of
`prop.sSetdag_is_equivalent_to_Fun`, not just a bijection of objects.

`Presentable.lean` proves all small limits and colimits and local finite
presentability, hence the proposition's local presentability assertion.
The cardinal and diagram universe is the value universe `u`. A singleton strong
generator of `Type u` gives a `u`-small family of free representables; no
presentability hypothesis or restriction to `u = 0` is introduced.

## Free–forgetful adjunction

Files: [FreeDagger.lean](DaggerModels/FreeDagger.lean),
[Vertices.lean](DaggerModels/Vertices.lean),
[FreeDaggerPushout.lean](DaggerModels/FreeDaggerPushout.lean),
[FreeDaggerSkeleton.lean](DaggerModels/FreeDaggerSkeleton.lean).
Problem specifications: [PresheafChallenge.lean](.ci/comparator/PresheafChallenge.lean),
[VerticesChallenge.lean](.ci/comparator/VerticesChallenge.lean),
[FreeDaggerPushoutChallenge.lean](.ci/comparator/FreeDaggerPushoutChallenge.lean).

`freeDaggerAdjunction` is an actual adjunction to the original
`DaggerSSet.forget`. It uses the left Kan extension along the opposite simplex
inclusion, transported through the proved presheaf equivalence. The natural
identification of the resulting right adjoint with `forget` is proved.
This establishes existence of the free–forgetful adjunction in
`dj.not.adjunctions`.

The displayed formula `A ⨿_{sk₀ A} Aᵒᵖ` is also proved. `SSetVertices.obj A`
is the constant simplicial set on `A₀`, with both inclusions given by total
degeneracies of the same vertex. Its canonical monic inclusion has range
`A.skeleton 1`, and `skeletonIso` identifies it with that actual subcomplex
while preserving inclusion. Mathlib's skeleton uses nondegenerate dimensions
strictly below its index; thus `skeleton 1` is exactly the paper's `sk₀`.

`FreeDaggerPushout.functor` constructs the genuine pushout with its swap dagger.
The involution and fixed-vertex equations, action on maps, Hom equivalence,
adjunction, and natural isomorphism to the original `freeDagger` are proved.
The first coprojection is the adjunction unit. `freeDagger_pushout` establishes
this pushout presentation for **any** adjunction to the original forgetful
functor, with a natural second coprojection and both swap equations. The
double reversal in the first equation uses the standard `SSet` isomorphism.
`freeDagger_skeleton_pushout` transports the same presentation to the literal
zero-skeleton subcomplex, retaining the unit and swap.

The cellular presentation by boundary maps is proved separately above.
The model structures remain unproved; the explicit free formula alone does
not establish them.

## The fixed-vertex cofibration obstruction

File: [NormalCofibrationObstruction.lean](DaggerModels/NormalCofibrationObstruction.lean).
Problem specification: [NormalCofibrationChallenge.lean](.ci/comparator/NormalCofibrationChallenge.lean).

`AntiInvolutiveSSet` has the same simplicial anti-involution data but omits the
fixed-vertex condition. Its `NormalMono` predicate requires an underlying
monomorphism and freeness on new nondegenerate simplices in **every** degree.
`toAntiInvolutive` retains the actual underlying simplicial set, dagger, and map.
Every missing vertex therefore prevents normality.

`emptyToPoint` satisfies `FreeCofibration`: all positive-dimensional simplices
of the point are degenerate. Its anti-involutive image is not normal because
the vertex is fixed. The constructions have actual `IsInitial` and `IsTerminal`
proofs. This is the explicit predicate obstruction used in
`pointset.cor.cofibrant-obstruction` and the second half of Theorem D.
The identification of the point with `F†(Δ⁰)`, the relevant model cofibrations,
and the comparison Kan-extension adjunctions remain unproved.

## Ordinary equivalence need not be unitary equivalence

Files: [DaggerCategory.lean](DaggerModels/DaggerCategory.lean),
[UnitaryObstruction.lean](DaggerModels/UnitaryObstruction.lean).
Problem specification: [UnitaryObstructionChallenge.lean](.ci/comparator/UnitaryObstructionChallenge.lean).

The ordinary dagger category class fixes objects and reverses composition.
`IsUnitary f` means that `dagger f` is a two-sided inverse; it constructs a
categorical isomorphism, and dagger functors preserve it.

The example in `pointset.prop.weak-counterexample` is implemented with two
objects (`Bool`), all Hom types equal to `ℤ`, composition by addition, inverse
by negation, and dagger `a ↦ a + tᵢ - tⱼ`. The full subgroupoid on `false`
has a fully faithful dagger inclusion that is an actual categorical equivalence.
The unitary equation is `2a = tⱼ - tᵢ`, so no unitary arrow reaches `true` from
that subgroupoid. This proves precisely parts (1)–(2) of the source example.
Part (3), involving dagger nerves and the two notions of weak equivalence,
and its use in the first Quillen obstruction of D remain unproved.

The new existential Challenge goals fix the actual categories and mathematical
properties, not the chosen implementation of each witness. The library proves
the equivalence and adjunction by constructions and supplies the exact concrete
counterexamples above. This does not require including those construction
proofs in the problem specification.

## The vertex-level word obstruction

File: [DaggerModels/WordObstruction.lean](DaggerModels/WordObstruction.lean).
Problem specification: [WordObstructionChallenge.lean](.ci/comparator/WordObstructionChallenge.lean).

This file uses only Lean's standard library. In the proof of
`dj.prop.counterexample`, the two vertices `a` and `b` of the indiscrete groupoid
are represented by `false` and `true`. Vertices of its free monoid are finite
lists of these two letters. `dagger` reverses a list and switches every letter.

`dagger_length`, `dagger_involutive`, and `dagger_append` verify the elementary
dagger laws. `no_selfAdjoint_length_one` states that a word of length one cannot
be fixed by dagger. Consequently `no_dagger_preserving_section` rules out a
function from the natural numbers to words that is both a section of length
and dagger preserving, where dagger on the natural numbers is the identity.

This supplies the algebraic obstruction in the last paragraph of the paper's
argument. **It is not a formal proof of the whole proposition.** The nerve,
contractible Kan fibers, free simplicial monoid, local trivial fibration,
Bergner cofibration, and identification of rigidification with the self-adjoint
monoid are not constructed in this release.

## Main-result status

| Manuscript label | Result | Status |
| --- | --- | --- |
| `bg.thm.main`, `bg.thm.left-proper` | Dagger Bergner model structure and left properness; Theorem A | Not formalized |
| `dj.thm.main`, `dj.thm.equivalence` | Dagger Joyal model structure and rigidification Quillen equivalence; Theorem B | Not formalized |
| `dj.thm.intrinsic-equivalence` | Intrinsic recognition using unitary cores; Theorem C | Not formalized |
| `pointset.cor.no-naive-quillen` | Comparison obstruction with the DCH model; Theorem D | Not formalized |
| `prop.sSetdag_is_equivalent_to_Fun` | Presheaf equivalence and presentability | Proved, with arbitrary value universe |
| `dj.not.adjunctions` (simplicial sets) | Free–forgetful adjunction | Actual adjunction, zero-skeleton pushout, unit and swap proved |
| `dj.lem.free-cof` | Cellular characterization of free cofibrations | Both conclusions proved: an actual relative free-boundary-cell complex for every free cofibration, and equality with the stated saturation, at arbitrary value universe |
| `dj.prop.counterexample` | Rigidification need not preserve all monomorphisms as cofibrations | Vertex-level obstruction proved; proposition not proved |

These results are not inserted as assumptions to make the project build.
The full A–D objective and remaining dependencies are in
[MAIN_THEOREMS.md](MAIN_THEOREMS.md). It also records a malformed hypothesis in
`dj.prop.strict-borel-presentation`; no manuscript change has been made here.
The correspondence above is an explicit mathematical interpretation of the
formal statements, not a machine-checked translation of the manuscript's prose.
