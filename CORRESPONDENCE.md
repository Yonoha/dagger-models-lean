# Correspondence with Part I

Scope of the current development, based on the manuscript inspected on 2026-10-01.
Version 0.1.0 remains the immutable initial foundations release.
Names below are in the `DaggerModels` namespace. A definition being implemented
does not mean that every subsequent theorem about it has been proved.

The current branch supplies twenty-seven self-contained Comparator Challenges for
reviewing its mathematical scope. Each imports only Mathlib; definitions
are visible in the Challenge rather than imported from this implementation.
The intentional theorem-proof placeholders are specification markers, not
unproved library results. A reviewer must inspect all twenty-seven files to review the
whole checked scope. Comparator checks correspondence between their Lean
statements and the implementation, not the translation from the manuscript.
The current total is 1,870 physical lines and 109 roots: 106 mathematical results
and three definition markers. Twenty-five files have the standard 100-line
budget; the existing 160-line and 116-line exceptions are unchanged. Smaller
counts below describe earlier milestones, not the current coverage.

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

## Dagger simplicial categories and their free construction

Files: [DaggerSimplicialCategory.lean](DaggerModels/DaggerSimplicialCategory.lean),
[DaggerSimplicialGraph.lean](DaggerModels/DaggerSimplicialGraph.lean),
[FreeSimplicialPaths.lean](DaggerModels/FreeSimplicialPaths.lean),
[FreeSimplicialLift.lean](DaggerModels/FreeSimplicialLift.lean), and
[FreeDaggerSimplicialCategory.lean](DaggerModels/FreeDaggerSimplicialCategory.lean).
The three new problem specifications are
[DaggerSimplicialCategoryChallenge.lean](.ci/comparator/DaggerSimplicialCategoryChallenge.lean),
[FreeSimplicialPathsChallenge.lean](.ci/comparator/FreeSimplicialPathsChallenge.lean), and
[FreeDaggerUniversalChallenge.lean](.ci/comparator/FreeDaggerUniversalChallenge.lean).

`DaggerSimplicialStructure` implements the hom-level formulation in the remark
after `bg.def.dagger-scat`. Each dagger is an ordinary SSet morphism between
the reversed mapping spaces, preserves enriched identity, reverses composition
using the canonical Cartesian braiding, and squares to identity. The actual
enriched functor to the opposite and its typed inverse are constructed, and
both composites are proved equal to identity. Objects and mapping spaces have
independent universes. There is no reversal of the simplex operator and no
condition fixing every vertex of a mapping space. The bundled category uses
actual enriched dagger-preserving functors. The ordinary dagger category on
underlying generalized elements is also constructed.

`DaggerSimplicialGraph` implements `bg.def.dagger-graph` at every common universe
`u`, with arbitrary vertex maps and natural edge maps commuting with dagger.
`DaggerSimplicialCat.forgetGraph` retains the original objects, mapping spaces,
dagger, and functor components. `FreeSimplicialPaths` implements the opening
construction in the proof of `bg.lem.presentable`: its objects are the original
vertices and its degreewise morphisms are actual Mathlib `Quiver.Path` values.
Empty words give identities, singleton words insert edges, and concatenation
gives composition. Simplicial operators act on every edge; dagger reverses the
word and applies graph dagger to every letter. There is no cancellation or
quotient by inverse relations. The free enrichment is used locally in the
construction; it cannot override the enrichment of an arbitrary target category.

`FreeSimplicialExtension.extend` composes assigned edges and proves naturality
in the simplicial degree, restriction on singleton edges, and uniqueness for
every enriched functor. Dagger compatibility then gives `homEquiv`, an actual
bijection between all dagger simplicial functors out of the free category and
all graph maps into the target. Its target naturality constructs the actual
free functor and `adjunction`; `adjunction_unit` identifies the unit with
singleton insertion. `exists_freeDaggerSimplicialCategory` exposes the full
universal property through the raw `restrictGraph` operation so that the
problem statement fits in 83 lines. This specification quantifies over all
targets and all object maps. It protects universality without prescribing the
choice of free witness; the separate word specification protects the concrete
path operations. The actual adjunction and its unit are included in the library
axiom audit, but are not additional roots of this short universal specification.

This completes the free construction and adjunction used at the start of
`bg.lem.presentable`. Its monadicity assertion is proved in the next section.
The local finite presentability conclusion is proved below. Creation of limits
and colimits in `bg.lem.creation` are proved in the final construction below.
The model-categorical conclusions of A–D
do not follow from the currently proved results alone. The implementation and
Challenge correspondence received separate GPT-6.1-Sol/xhigh agent reviews;
this is not independent human review. No manuscript statement was edited.

## Monadicity over dagger simplicial graphs

Files: [DaggerGraphReflection.lean](DaggerModels/DaggerGraphReflection.lean),
[DaggerSplitCoequalizer.lean](DaggerModels/DaggerSplitCoequalizer.lean),
[DaggerGraphDescent.lean](DaggerModels/DaggerGraphDescent.lean),
[DaggerGraphCoequalizer.lean](DaggerModels/DaggerGraphCoequalizer.lean), and
[DaggerSimplicialMonadicity.lean](DaggerModels/DaggerSimplicialMonadicity.lean).
Problem specification: [DaggerMonadicityChallenge.lean](.ci/comparator/DaggerMonadicityChallenge.lean).

`forgetGraph_reflectsIsomorphisms` proves the reflection sentence in the second
paragraph of `bg.lem.presentable`. Given an actual inverse graph map, its unit
and composition laws follow by cancellation along the original functor's hom
maps. Their monicity is derived from that inverse. All endpoint transports are
explicit; no restriction to identity object maps is introduced.

For a graph-split diagram, `GraphSplitData` contains exactly the six fields of
Mathlib's `IsSplitCoequalizer`. The adapter `GraphSplitData.ofMathlib` copies
those fields unchanged. The quotient graph is only a graph at this point.
`quotientId` and `quotientComp` lift through the graph section, use the actual
operations in the source, and return through the quotient map with explicit
endpoint transports. The split equations and the two original functors' laws
prove preservation by the quotient map. Lifting complete composable tuples
then gives unit and associativity laws. The given graph dagger supplies the
involution and, using the actual graph-map compatibility, the unit and
anti-composition laws. `quotientCategory` and `quotientFunctor` retain the
original quotient graph and map definitionally. A graph section is never
assumed to preserve composition or identity.

`GraphDescent.lift` proves that graph factorization through this quotient is an
enriched dagger functor. `GraphCoequalizer.isColimit` proves existence and
uniqueness of the factorization for every target. Its split graph cofork is
also a colimit, giving preservation by `forgetGraph`. Together with the actual
free adjunction and reflection of isomorphisms, Mathlib's Beck theorem yields
`forgetGraph_monadic : Nonempty (MonadicRightAdjoint forgetGraph)`. This is the
full first assertion of `bg.lem.presentable`, at every common universe `u`.
The graph presentability, word-finitarity and dagger-category local finite
presentability assertions are proved below.

The Challenge directly protects the literal reflection and monadicity types.
It shows the full category structures and the original forgetful functor, and
imports only Mathlib. With the word-finitarity target below it has 160 physical
lines, within its reviewed 160-line budget;
the other Challenges keep their 100-line budgets. This explicit
exception avoids hiding definitions or replacing monadicity by an easier
existence statement. All prior comparison roots remain registered.

## Dagger graph presheaves and presentability

Files: [DaggerGraphIndex.lean](DaggerModels/DaggerGraphIndex.lean),
[DaggerGraphTotalSpace.lean](DaggerModels/DaggerGraphTotalSpace.lean),
[DaggerGraphPresheaf.lean](DaggerModels/DaggerGraphPresheaf.lean), and
[DaggerGraphPresentable.lean](DaggerModels/DaggerGraphPresentable.lean).
Problem specification:
[DaggerGraphPresentableChallenge.lean](.ci/comparator/DaggerGraphPresentableChallenge.lean).

This proves the graph-LFP ingredient in the last paragraph of
`bg.lem.presentable`, with the graph category of `bg.def.dagger-graph` unchanged.
The concrete small index has one vertex object and an edge object for each
simplex. Its two endpoint maps are exchanged by an involution. The involution
commutes with ordinary simplex maps; it does not reverse their order.

The forward functor uses the original vertex set and the total edge spaces
`Σ x, Σ y, (G.Hom x y).obj n`. A graph map acts on both endpoints and the edge
simplex. The inverse functor takes the exact fibers of both endpoint maps,
with the index involution supplying dagger. Arbitrary presheaf natural
transformations induce the full graph maps, including their vertex functions.
The unit reinserts endpoint labels; its inverse uses their equalities to
recover the original typed edge. The counit forgets redundant fiber labels,
with inverse supplied by the actual source and target of an edge. Naturality,
both inverse laws, and the equivalence triangle are proved.

Presheaves on this index are locally finitely presentable in every value
universe `u`: free representables on the singleton type form a small strong
generator of finitely presentable objects. The actual equivalence transports
this assertion and all `u`-small limits and colimits to the original graph
category. There is no restriction to a fixed vertex set or to degree-zero
graphs, and no finitary-monad premise is needed for this graph result.

The 74-line Challenge displays the complete original graph category and asks
for an actual equivalence with presheaves on some small category, as well as
`HasLimits`, `HasColimits`, `IsLocallyFinitelyPresentable`, and
`IsLocallyPresentable`. It does not fix the proof's choice of indexing category
or duplicate the intermediate equivalence. Comparator replays their proof
dependencies, and the namespace-wide axiom audit includes those constructions.
The five graph targets and all preceding 86 roots remain registered. Word
finitarity, dagger-category presentability, ordinary creation, two-object cells,
ordinary colimits and object generation below brought that stage to 23 Challenges,
102 roots and 1,780 physical lines. The ordinary-lifting and small-object stage
below extends this to the current 27 Challenges, 109 roots and 1,870 lines.
Tool pins, permitted axioms
and negative controls are unchanged. Local finite presentability of dagger
simplicial categories requires the further constructions below; the main
theorems A–D remain unproved.

## Finitary words and limits over dagger graphs

Files: [DaggerGraphFiniteWords.lean](DaggerModels/DaggerGraphFiniteWords.lean),
[FreeSimplicialMap.lean](DaggerModels/FreeSimplicialMap.lean),
[FreeWordFinitary.lean](DaggerModels/FreeWordFinitary.lean),
[DaggerSimplicialLimits.lean](DaggerModels/DaggerSimplicialLimits.lean), and
[DaggerSimplicialFilteredColimits.lean](DaggerModels/DaggerSimplicialFilteredColimits.lean).
Problem specification:
[DaggerMonadicityChallenge.lean](.ci/comparator/DaggerMonadicityChallenge.lean).

This proves the assertion that the word monad is finitary in the last paragraph
of `bg.lem.presentable`. At each simplex degree, length zero consists of the
original vertices. Each successor length is the fiber product of the prefix's
target and the next total edge's source. The resulting type is proved equivalent
to the original finite paths of that exact length, preserving both endpoints.
The equivalence is natural under arbitrary vertex functions and edge maps,
including ordinary simplex operators. No fixed-object or injectivity premise
is introduced.

The actual vertex and total-edge functors preserve small colimits by the
proved graph presheaf equivalence. Each fixed word length is finitely accessible
because filtered colimits of types commute with finite limits. The library
constructs the literal pullback functor and its limiting cone before applying
Mathlib's accessibility theorem. It also constructs the literal disjoint-sum
functor and identifies it with the categorical coproduct, proving accessibility
of the sum over all finite lengths.

`wordsIso` identifies this sum with the actual total edges of
`FreeDaggerSimplicialCategory.functor ⋙ forgetGraph`. Its naturality uses the
proved equality between that original free functor's maps and edgewise path
extension. All vertex maps are retained. The graph evaluations jointly detect
accessibility through the actual presheaf equivalence, so the conclusion is
finitarity of the original word endofunctor at every common universe `u`.

The new Challenge statement requires an actual left adjoint `F` to the original
graph forgetful functor and finite accessibility of `F ⋙ forgetGraph`.
The implementation witnesses this with its original free adjunction. A fixed
right adjoint determines its left adjoint up to natural isomorphism, and finite
accessibility is invariant under that isomorphism; leaving the witness free
does not weaken the mathematical assertion. The seven-line addition retains
the previous complete definitions, category structures and two targets.

Monadicity now proves that the graph forgetful functor creates all small limits
and all small filtered colimits. Graph limits/colimits supply their existence
in dagger simplicial categories, and the graph forgetful functor itself is
finitely accessible. The finitarity premise in the filtered argument is
discharged by the new theorem. These consequences are checked by Lean and
the full namespace axiom audit; they are not additional Comparator roots.
They do not assert the different claim in `bg.lem.creation`, whose forgetful
functor goes to ordinary simplicial categories. General colimits and local
finite presentability are proved next. The main theorems A–D remain unproved.

## Dagger simplicial category colimits and local finite presentability

Files: [DaggerHomKernel.lean](DaggerModels/DaggerHomKernel.lean),
[DaggerHomQuotient.lean](DaggerModels/DaggerHomQuotient.lean),
[DaggerColimitKernel.lean](DaggerModels/DaggerColimitKernel.lean),
[DaggerSemanticColimit.lean](DaggerModels/DaggerSemanticColimit.lean),
[StrongGeneratorAdjunction.lean](DaggerModels/StrongGeneratorAdjunction.lean),
[DaggerFiniteGenerators.lean](DaggerModels/DaggerFiniteGenerators.lean), and
[DaggerSimplicialPresentable.lean](DaggerModels/DaggerSimplicialPresentable.lean).
Problem specification:
[DaggerSimplicialPresentableChallenge.lean](.ci/comparator/DaggerSimplicialPresentableChallenge.lean).

This proves the final assertion of `bg.lem.presentable` for the complete original
category, at every common universe `u`. The proof builds the needed colimits and
finite generators instead of postulating the cited general finitary-monad theorem.

`HomQuotient` closes a relation on each mapping-space degree under composition
using Mathlib's actual category quotient. Ordinary simplex operators and dagger
descend, giving an actual enriched dagger category on the original object type.
The quotient functor and factorization bijection allow arbitrary object maps.
In particular, uniqueness uses equality of dependent hom maps with the required
endpoint transports; it does not restrict to functors fixing objects.

For a small diagram `K`, `ColimitKernel.graph K` is its colimit after forgetting
to dagger graphs. The original free adjunction forms a dagger category on this
graph, including paths newly composable after vertex identifications. Every
existing dagger-category cocone gives a free extension from that category.
Their joint kernel defines a relation on hom simplices. Although the family of
all cocones lives in `Type (u+1)`, the relation is in `Prop`, so its hom quotients
remain in `Type u`. No dagger-category colimit or prospective quotient is
assumed in defining the relation.

The images of each original diagram identity and composite are related because
every actual cocone preserves them. Thus the graph legs become enriched dagger
functors into the quotient. The quotient and free-adjunction universal properties,
followed by the graph-colimit universal property, prove existence and uniqueness
of factorization for every target cocone. This constructs all `u`-small colimits
of the actual category, including arbitrary vertex identifications.

Free images of a small strong generator in the graph category form a strong
generator because the actual right adjoint is faithful and reflects isomorphisms.
No fullness hypothesis is used. Accessibility of that right adjoint makes the
free images finitely presentable. Since their isomorphism-closed image is only
essentially small, `DaggerFiniteGenerators` chooses a genuinely small set of
representatives and proves it remains a strong generator. Mathlib's generator
criterion, with the constructed colimits supplying its cocompleteness premise,
then gives unconditional local finite presentability.

The 93-line Challenge contains the complete original category and all enriched
dagger functors. Its four targets directly state `HasLimits`, `HasColimits`,
`IsLocallyFinitelyPresentable` and `IsLocallyPresentable` at universe `u`.
None assumes colimits, a strong generator, finitarity, or a restricted object
class. All imports are Mathlib; the full structure and its proof fields are
visible. The preceding 92 targets and their specifications are unchanged, and
these four targets bring the total to 96. The proof and statement correspondence
received separate agent reviews; this is not independent human review.

Together with the preceding monadicity proof, this completes `bg.lem.presentable`.
Creation by the distinct forgetful functor to ordinary simplicial categories
in `bg.lem.creation` is proved next. The main theorems A–D remain unproved.

## Creation over ordinary simplicial categories

Files: [SimplicialOpposite.lean](DaggerModels/SimplicialOpposite.lean),
[SimplicialObjectAdjunctions.lean](DaggerModels/SimplicialObjectAdjunctions.lean),
[DaggerStructureFromOpposite.lean](DaggerModels/DaggerStructureFromOpposite.lean),
[DaggerOppositeHom.lean](DaggerModels/DaggerOppositeHom.lean),
[DaggerLimitOpposite.lean](DaggerModels/DaggerLimitOpposite.lean),
[DaggerColimitOpposite.lean](DaggerModels/DaggerColimitOpposite.lean),
[DaggerOrdinaryLimitCreation.lean](DaggerModels/DaggerOrdinaryLimitCreation.lean),
[DaggerOrdinaryColimitCreation.lean](DaggerModels/DaggerOrdinaryColimitCreation.lean), and
[DaggerOrdinaryCreation.lean](DaggerModels/DaggerOrdinaryCreation.lean).
Problem specification:
[DaggerOrdinaryCreationChallenge.lean](.ci/comparator/DaggerOrdinaryCreationChallenge.lean).

This proves `bg.lem.creation` for the original `DaggerSimplicialCat.forget`
into ordinary `SimplicialCat`. It is a different functor from `forgetGraph`.
The result has no `HasLimits`, `HasColimits`, fullness, or fixed-object premise.
Object universe `o`, mapping-space universe `v`, and diagram object/hom
universes `w, w'` remain independent.

The ordinary opposite functor is an actual autoequivalence, with canonical
double-opposite unit/counit and triangle identity. Discrete and codiscrete
simplicial categories give left and right adjoints to the actual object functor.
It therefore preserves limits and colimits of any size that exist.
The discrete enrichment uses constant simplicial sets on lifted equality proofs;
this does not force the object and mapping-space universes to coincide.

Given any ordinary limit cone or colimit cocone of the forgotten diagram, its
universal property induces a functor from the apex to its ordinary opposite.
The diagram equations and double-opposite naturality prove involutivity.
Preservation by the object functor proves that this induced functor fixes
objects. `ofOppositeFunctor` then supplies exactly the original mapping-space
dagger, whose enriched opposite functor is proved equal to the induced functor.
The original apex and entire cone/cocone are retained after forgetting.

An enriched functor commuting with these daggers lifts to the actual dagger
Hom type. Isomorphism reflection is proved by lifting the ordinary inverse,
without assuming fullness. The ordinary universal map commutes with dagger by
the same limit/colimit equations, so it lifts with its full universal property.
These constructions supply Mathlib's actual `LiftsToLimit` / `LiftsToColimit`
and `CreatesLimitsOfSize` / `CreatesColimitsOfSize` data, including reflection.

The two public conclusions are `Nonempty (CreatesLimitsOfSize ... forget)` and
`Nonempty (CreatesColimitsOfSize ... forget)`. These classes are Type-valued;
`Nonempty` states existence of their complete data without prescribing a witness.
It does not reduce creation to preservation or conditional existence.

The Mathlib-only Challenge visibly includes both complete category structures,
all enriched dagger functors, and this exact ordinary forgetful functor.
Its 116 physical lines form an explicit reviewed budget exception; even without
blank lines it has 101 lines. Readability is retained rather than hiding local
definitions or compressing proof fields. Its two root types and all 92 local
constants were compared directly in separate Lean environments, with only the
two root proof bodies omitted. The existing 18 Challenges/configurations and
96 roots were retained at this stage, giving 19 Challenges and 98 roots before
the two-object cell specifications below.
The implementation and statement correspondence received separate agent reviews;
no independent human review is claimed. The main theorems A–D remain unproved.

## Two-object cells and finite compactness

Files: [TwoObjectDaggerGraph](DaggerModels/TwoObjectDaggerGraph.lean),
[TwoObjectDaggerCell](DaggerModels/TwoObjectDaggerCell.lean),
[TwoObjectDaggerCellUniversal](DaggerModels/TwoObjectDaggerCellUniversal.lean),
[TwoObjectGraphPresentability](DaggerModels/TwoObjectGraphPresentability.lean), and
[TwoObjectCellPresentability](DaggerModels/TwoObjectCellPresentability.lean).

The actual graph in `bg.not.cells` has two vertices `ULift Bool`, empty diagonal
edge spaces, and off-diagonal copies of K exchanged by dagger. Its full graph
Hom equivalence classifies a morphism by an arbitrary pair of target vertices
and one simplicial edge map. The target vertices may coincide, and K may be
empty or disconnected. Applying the original finite-path free adjunction gives
the actual cell `F(G_K)` and the complete equivalence in `bg.eq.A-univ`, with
restriction literally given by the singleton generator followed by the target
functor's hom map. Both source and target naturality are proved.

Finite presentability requires retaining the endpoint pair even when K is
empty or disconnected. The graph Hom functor is naturally the pullback of
`Hom(K, totalEdges(G))` and the vertex-pair set over
`Hom(K, const(vertices(G) times vertices(G)))`. The inverse uses the actual
endpoint fiber in every simplicial degree. Evaluation colimit preservation,
finite products and pullbacks, and finite presentability of K prove that this
Hom functor preserves filtered colimits. This is not an assumption that the
two-object graph functor is left adjoint to the total-edge functor.

The original free adjunction and the already proved filtered-colimit
accessibility of graph forgetting transfer finite presentability to `F(G_K)`.
Pinned Mathlib proves finite simplicial sets are finitely presentable. Here
`K.Finite` means finitely many nondegenerate simplices in total, not degreewise
finiteness. The conclusion uses the same actual cell for both its universal
property and finite presentability, completing the compactness assertion
following `bg.eq.A-univ` at every common universe `u`.

The 57-line and 95-line Mathlib-only Challenges protect these two conclusions.
They show the original dagger structures, all enriched dagger functors and the
actual generator-restriction classifier. The latter also shows the complete
category structure needed for `IsFinitelyPresentable`. Their closed existential
statements leave the representing witness free while fixing the full required
property. Raw comparison in separate Lean environments compares 71 and 84
constants, including all definition values and structural proofs, with only
the target theorem's proof body omitted. All preceding 19 Challenges/configs
and 98 roots are retained. This two-object-cell stage had 21 Challenges, 100 roots
and 1,649 physical lines, with no new line-budget exception. The further
ordinary-colimits and object-generator registrations are described below.

## Ordinary cells and two ingredients of cell-attachment reduction

Files: [OrdinaryTwoObjectCell](DaggerModels/OrdinaryTwoObjectCell.lean),
[UnderlyingTwoObjectCell](DaggerModels/UnderlyingTwoObjectCell.lean),
[TwoObjectCellPushout](DaggerModels/TwoObjectCellPushout.lean), and
[DaggerSimplicialCofree](DaggerModels/DaggerSimplicialCofree.lean).

The ordinary cell of `bg.not.cells` has terminal diagonal homs, forward hom K,
and empty reverse hom. Its enriched identities and composition are explicitly
constructed, with its unrestricted universal property and both naturalities.
Ordinary enriched functors from `U(F(G_K))` to any ordinary simplicial category
are classified by two independent directed edge maps with their endpoints.
No dagger compatibility is imposed on those target functors.

This gives the actual pushout decomposition of the underlying free dagger cell
used in `bg.lem.reduction`. Its base is the discrete two-object category. One
span leg fixes the object labels and the other swaps them, so the second copy
of the ordinary cell represents the paper's reverse-labelled cell. The apex
is literally `forget.obj (TwoObjectDaggerCell.cell K)`, and its legs are the
forward and reverse singleton inclusions. Full factorization and uniqueness
for every compatible pair of ordinary functors prove `IsColimit` and `IsPushout`.
There is no restriction on K, the target endpoints, or target object maps.

Ordinary forgetting also has an actual right adjoint. It sends C to the dagger
category with the same objects and hom `C(x,y) times C(y,x)`. Composition is
forward composition paired with reverse composition in the opposite order;
dagger swaps the two factors at the same simplex degree. Pairing an ordinary
functor F with its value on the source dagger gives a full natural Hom
equivalence, and the actual adjunction proves colimit preservation. Object,
hom and diagram universes remain independent. This does not assume or prove
existence of arbitrary ordinary simplicial-category colimits.

These four supporting modules are included in the namespace-wide axiom audit,
but they are not separate Comparator roots. The complete attachment reduction
is now proved using the ordinary colimit construction below. The constructions
and their Challenges received separate agent reviews, not independent human review.

## Ordinary colimits and complete attachment reduction

`SimplicialColimitsFree.lean` constructs ordinary simplicial graphs and genuine
finite paths, with ordinary edgewise simplex operators and the full free
universal property for arbitrary object functions. `SimplicialHomQuotient.lean`
constructs degreewise hom quotients by a relation stable under simplex operators,
retaining the original objects and proving full enriched-functor descent.
For an arbitrary diagram, `SimplicialColimitKernel.lean` first takes the actual
Type-colimit of objects. Its edge generators keep the original diagram object,
both endpoints, and simplex. The quotient relation is the intersection of
kernels of all original cocone extensions. This quantification does not assume
a colimit cocone; the relation lives in Prop, so the quotient stays in the
original universe. `SimplicialColimits.lean` constructs the actual enriched legs,
proves their identities, composition and naturality with both endpoint
transports, and proves the complete colimit universal property.

`DaggerModels.simplicialCatHasColimits` is an unconditional theorem at every
common universe. Its 40-line Mathlib-only Challenge exposes the full ordinary
category and all enriched functors. No prospective model structure, cocompleteness
premise, dagger, or restriction on object maps appears in the statement.

`TwoCopyPushoutReduction.lean` proves the general two-copy pasting lemma in an
arbitrary category. The three `TwoObjectCellReduction` modules instantiate it
with the actual ordinary and dagger cells. The ordinary pushouts now exist by
the preceding colimit construction; the dagger pushout exists by proved dagger
cocompleteness, and its underlying square is a pushout by the cofree adjunction.
`TwoObjectCellReductionResolved.lean` supplies
`DaggerModels.TwoObjectCellReduction.reductionIso`, with no remaining `HasPushout`
or `HasColimits` premises. Its `exists_reduction` theorem uses the same two
pushouts and comparison isomorphism throughout. The second attaching map is
literally the original edge followed by dagger, at the reversed endpoint pair,
and then by the first attachment inclusion. All three comparison-leg equations
are proved. This proves the full `bg.lem.reduction`, and in fact requires no
monicity of the simplicial map, distinct endpoints, or nonempty edge space.
These reduction proofs are audited and separately reviewed auxiliary results;
the ordinary-colimits theorem is their new registered Comparator root.

## The actual object generator and boundary lifting

`DaggerDiscreteObjects.lean` equips the existing discrete enrichment on V,
with hom the constant simplicial set `ULift (PLift (x = y))`, with equality
reversal as dagger. Its full Hom equivalence classifies arbitrary dagger functors
by object functions. Objects and hom universes remain independent. Empty and
one-object identity-only instances give actual initial and terminal objects,
with the unique arrow between them. Lifting against that arrow is proved
equivalent to surjectivity of the actual object function.

`exists_daggerObjectGenerator` has a 91-line Mathlib-only Challenge exposing the
full dagger category. It requires one initial object, one terminal object and
one arrow, outside the quantification over every target functor. These universal
properties determine the concrete empty-to-point arrow up to arrow isomorphism,
under which lifting is invariant. The conclusion is actual surjectivity, not
essential surjectivity. The library uses the same concrete witnesses throughout.

`TwoObjectCellLifting.lean` uses the full two-object-cell Hom equivalence to prove
that lifting against the actual image of any simplicial map is equivalent to
lifting on every full hom space. Both endpoint equalities are transported
before comparing dependent hom maps. Arbitrary object functions, equal endpoints
and empty simplicial sets are all retained. `DaggerGeneratingCofibrations.lean`
defines `I†` as the literal union of all actual free boundary inclusions (all
natural-number dimensions, including zero) and the empty-to-point generator.
Its RLP is exactly object surjectivity and boundary RLP for every hom map.
These are audited and separately reviewed auxiliary results, not additional
Comparator roots. The comparison of boundary RLP with a Kan fibration that is
a weak homotopy equivalence, and therefore full `bg.lem.I-inj`, remains unproved.
No weak-equivalence or model-category structure is supplied as an extra premise.

At the ordinary-colimit/object-generator stage, the two Challenges retained all
preceding 100 roots and twenty-one specifications/configurations unchanged.
That stage had 102 roots (99 mathematical and three definition markers),
twenty-three Challenges and 1,780 physical lines. Both remain unchanged in the
new ordinary-lifting/small-object tranche below.

## Ordinary boundary cells, local Kan fibrations and the small object argument

These are inputs to `bg.lem.I-inj`, the local part of `bg.lem.Iinj-in-Jinj`, and
smallness/factorization in the proof of `bg.thm.main`. They do not complete
`bg.lem.I-inj`, the interval part of `J†`, or the model-structure theorem.
The nine new modules have the following roles.

| File | Mathematical construction |
| --- | --- |
| [SSetBoundaryFibration.lean](DaggerModels/SSetBoundaryFibration.lean) | Actual horn-to-boundary pushout and boundary RLP implying the existing Mathlib Kan fibration property |
| [SSetBoundaryCellsCore.lean](DaggerModels/SSetBoundaryCellsCore.lean) | Actual disjoint-union coproducts, relative skeleton, characteristic/boundary lifts, original source isomorphism and target colimit |
| [SSetBoundaryCellsAttachment.lean](DaggerModels/SSetBoundaryCellsAttachment.lean) | Boundary intersection, coverage and interior uniqueness imply actual attachment pushouts |
| [SSetBoundaryCells.lean](DaggerModels/SSetBoundaryCells.lean) | Every mono is an actual relative boundary-cell complex; closure and right lifting-class equalities |
| [SSetMonoRLPRetraction.lean](DaggerModels/SSetMonoRLPRetraction.lean) | Mono-RLP gives a section and literal cylinder homotopy over the original target |
| [SSetBoundaryRetraction.lean](DaggerModels/SSetBoundaryRetraction.lean) | The same simultaneous conclusion for actual boundary RLP |
| [DaggerLocalFibrations.lean](DaggerModels/DaggerLocalFibrations.lean) | Actual positive horn family `J†loc` and its all-hom Kan lifting equivalence |
| [SmallObjectFiniteDomains.lean](DaggerModels/SmallObjectFiniteDomains.lean) | General finite-domain bridge to Mathlib's `HasSmallObjectArgument` at the regular cardinal ℵ₀ |
| [DaggerSmallObject.lean](DaggerModels/DaggerSmallObject.lean) | Unconditional small object argument and actual functorial factorization data for the original `I†` |

For ordinary simplicial sets, `I` and `J` are the existing
`SSet.modelCategoryQuillen.I` and `.J`, not new predicates. Filling the missing
face of a horn is an actual pushout of the lower boundary inclusion; composing
with the upper boundary proves `I.rlp ≤ fibrations SSet`. This is Mathlib's Kan
fibration class, defined by ordinary horn lifting, for arbitrary source/target
and every value universe `u`. There is no source- or target-Kan assumption.

For any original `i : X ⟶ Y` with `[Mono i]`, the stage at `n` is literally
`(SSet.skeletonOfMono i n).toSSet`. The cells are all new nondegenerate
`n`-simplices of `Y` outside the degreewise image of `i`, individually indexed,
including every new vertex when `n = 0`. The actual characteristic map of each
cell lifts to stage `n + 1`; its boundary lifts to stage `n`. The checked ordinary
boundary-preimage and unique Eilenberg–Zilber normal-form lemmas prove exact
intersection, coverage and uniqueness of interiors. They give a pointwise
pushout, reflected by evaluation to an actual simplicial pushout. Characteristic
maps need not be monic. The zeroth stage is isomorphic to the original source,
and the colimit is the original target with the original map. Thus
`exists_relativeCellComplex` requires only `[Mono i]` and concludes
`Nonempty (RelativeCellComplex.{u} (fun (_ : ℕ) n ↦ (SSet.boundary.{u} n).ι) i)`.
There is no cellularity premise. Reindexing ℕ by `ULift.{u} ℕ` keeps the
transfinite closure in the full value universe, yielding
`transfiniteCompositions.{u} (coproducts.{u} I).pushouts = monomorphisms SSet.{u}`
and `I.rlp = (monomorphisms SSet.{u}).rlp`.

For arbitrary `p : X ⟶ Y`, mono-RLP, and hence actual boundary-RLP, gives one
`s : Y ⟶ X` and one `H : X ⊗ Δ[1] ⟶ X` satisfying all four equations:

```lean
s ≫ p = 𝟙 Y
SSet.ι₀ ≫ H = p ≫ s
SSet.ι₁ ≫ H = 𝟙 X
H ≫ p = CartesianMonoidalCategory.fst X Δ[1] ≫ p
```

The initial lifting square constructs the section. The actual coproduct of the
two endpoints is monic: its two constant interval coordinates are disjoint in
every degree. Its lifting square gives the same `H` in both endpoint laws and
the equation over `p`. No stationarity on the section image is claimed.
No weak-homotopy-equivalence predicate is defined or identified by this result.

`DaggerLocalFibrations.localGenerators` is the actual family of
`TwoObjectDaggerCell.functor.map (SSet.horn (n + 1) k).ι`, for every `n : ℕ` and
`k : Fin (n + 2)`. Its RLP is equivalent to `∀ x y, Fibration (p.map x y)`.
The original `I†` RLP implies object surjectivity and this local Kan condition.
All target object maps, equal endpoints and the original full hom spaces are
retained, at every common universe `u`. These are the local portion only of
`bg.def.IJ` and `bg.lem.Iinj-in-Jinj`; no unitary interval lifting is proved.

The general `SmallObjectFiniteDomains.hasSmallObjectArgument` theorem retains
independent category, hom and auxiliary universes `u`, `v`, `w`. Its assumptions
are `[Category.{v} C]`, `[LocallySmall.{w} C]`,
`[HasColimitsOfSize.{w,w} C]`, `[MorphismProperty.IsSmall.{w} I]`, and finite
presentability at `w` of every actual `I`-domain. Choosing ℵ₀ proves the actual
relative-cell colimit condition and `HasSmallObjectArgument.{w} I`.
For the original `I†`, literal union smallness, finite presentability of the
boundary-cell domains, initiality of the empty domain, and the already proved
dagger-category colimits discharge these assumptions. Consequently
`DaggerSmallObject.generators_hasSmallObjectArgument` has no remaining premise,
and the actual functorial factorization data has left class `I†.rlp.llp` and
right class `I†.rlp`, for every common `u`. These classes are not identified
with model cofibrations or trivial fibrations. The full `J†` family and its
interval-domain smallness/factorization are not constructed here.

Four Mathlib-only Challenges add 15, 27, 27 and 21 physical lines and seven roots.
Four roots protect the ordinary Kan consequence, relative presentation, cell
closure equality and lifting-class equality; two protect the section/homotopy
conclusions; one protects the general finite-domain bridge with its explicit
hypotheses. The actual local horn equivalence and unconditional `I†`
factorization are audited, separately agent-reviewed auxiliary applications,
not separate Comparator roots. All 23 prior Challenges and their 23 configs
(46 files), and all 102 ordered roots, remain unchanged. The current total is
27 Challenges, 1,870 lines and 109 roots (106 mathematical and three markers).
The nine-module tranche passed local fresh compilation, seven exact root-header
comparisons and a transitive audit of all 2,544 loaded `DaggerModels`
declarations, including generated declarations; only `propext`,
`Classical.choice` and `Quot.sound` occur. Separate agent reviews are recorded,
without a claim of independent human review. Exact-commit Linux checks remain
separate from these local results. Weak homotopy equivalences, trivial Kan
fibrations, full `bg.lem.I-inj`, interval lifting in `J†`, and A–D remain unproved.

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
| `bg.def.dagger-scat`, `bg.def.dagger-graph` | Dagger simplicial categories and graphs | Full definitions, functor categories, and enriched dagger laws implemented |
| Opening construction in `bg.lem.presentable` | Free dagger simplicial category | Concrete word model, actual adjunction, singleton unit and universal property proved |
| First assertion of `bg.lem.presentable` | Graph forgetful functor is monadic | Proved by actual split coequalizers and Beck |
| Graph ingredient in the proof of `bg.lem.presentable` | Dagger graphs are locally finitely presentable | Actual presheaf equivalence, all small limits/colimits, and LFP proved at every common value universe |
| Word ingredient in the proof of `bg.lem.presentable` | The original word monad is finitary | Proved by exact finite endpoint pullbacks, disjoint sums and their natural identification with the actual free functor |
| Consequences over dagger graphs | All small limits and filtered colimits | Existence and creation by the graph forgetful functor proved; ordinary-category forgetting is treated separately |
| Final assertion of `bg.lem.presentable` | Dagger simplicial categories are locally finitely presentable | Proved using constructed small colimits and a small strong generator of finitely presentable objects, at every common universe |
| `bg.lem.creation` | Ordinary simplicial-category forgetting creates all small limits and colimits | Full Mathlib creation data proved, with independent object, hom, and diagram universes and arbitrary object maps |
| `bg.not.cells`, `bg.eq.A-univ` and the following compactness assertion | Two-object free cells and finite presentability | Actual cells, unrestricted universal property and finite presentability for finite simplicial sets proved |
| `bg.lem.reduction` | Successive ordinary attachments compute the forgotten dagger attachment | Full comparison isomorphism and three leg equations proved, with both ordinary pushouts constructed and no existence premise |
| `bg.not.cells`, `bg.def.IJ`, generator lifting in `bg.lem.I-inj` | Actual object and boundary generators | Exact object-surjectivity plus all-hom boundary-RLP characterization proved; comparison with trivial Kan fibrations remains unproved |
| Ordinary inputs to `bg.lem.I-inj` | Boundary RLP, actual cells and homotopy | Boundary RLP implies actual Kan fibrations; every mono has an actual relative boundary-cell complex; cell and lifting-class equalities and the same section/cylinder four laws proved; weak-equivalence comparison remains unproved |
| `bg.def.IJ`, local portion of `bg.lem.Iinj-in-Jinj` | Actual `J†loc` lifting | All-hom Kan equivalence and the local consequence of `I†` RLP proved; interval lifting remains unproved |
| Small-object input to `bg.thm.main` | Actual `I†` smallness and factorization | Generic finite-domain theorem and unconditional actual `I†` small object argument/functorial data proved, with classes `I†.rlp.llp` and `I†.rlp`; no full model structure or `J†` factorization claimed |
| `dj.prop.counterexample` | Rigidification need not preserve all monomorphisms as cofibrations | Vertex-level obstruction proved; proposition not proved |

These results are not inserted as assumptions to make the project build.
The full A–D objective and remaining dependencies are in
[MAIN_THEOREMS.md](MAIN_THEOREMS.md). It also records a malformed hypothesis in
`dj.prop.strict-borel-presentation`; no manuscript change has been made here.
The correspondence above is an explicit mathematical interpretation of the
formal statements, not a machine-checked translation of the manuscript's prose.
