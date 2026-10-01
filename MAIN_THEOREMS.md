# Part I main-theorem formalization

The active objective is the full statements of **A–D**, not merely the
foundational lemmas below. This development does not yet prove any of A–D.
A successful build or Comparator run establishes only the registered Lean
results. Main-theorem completion requires the actual categories, weak
equivalences, adjunctions, and hypotheses in the manuscript.

The labels below refer to the author's Part I working manuscript inspected on
2026-10-01. Source line numbers are navigation aids, not stable identifiers.
This roadmap records implementation dependencies, not assumptions added to the
Lean library. Unfinished results are not declared as axioms or `sorry` proofs.

## Verified steps toward the main results

- `prop.sSetdag_is_equivalent_to_Fun`: `Presheaf.lean` constructs
  `DaggerSSet.{u} ≌ (ReverseSimplexᵒᵖ ⥤ Type u)` for every universe `u`.
  Both functors, their action on morphisms, the natural unit and counit, and
  the triangle identity are proved. Constant monotone/antitone maps are one
  morphism, and agreement of the two pullback formulas uses fixed vertices.
  `Presentable.lean` proves existence of all small limits and colimits and
  local presentability in the value universe `u`, completing the proposition's
  presentability assertion as well.
- The free–forgetful adjunction in `dj.not.adjunctions`: `FreeDagger.lean`
  constructs a left Kan extension and an actual adjunction to the original
  `DaggerSSet.forget` at every universe. `FreeDaggerPushout.lean` constructs the
  explicit pushout with swap dagger, proves its adjunction, and identifies it
  naturally with the original free functor, preserving the unit. `Vertices.lean`
  and `FreeDaggerSkeleton.lean` identify the common vertices with the actual
  zero-skeleton and prove the literal displayed pushout formula. The general
  result pins the unit, natural right coprojection, and both swap equations.
- The elementary closure arguments for `dj.def.free-cof` and `dj.lem.free-cof`:
  `FreeCofibration.lean` proves the equivalence of categorical and underlying
  monicity, identity and composition closure, and the actual arrow-retract
  closure. `FreeCofibrationPushout.lean` proves closure under any genuine
  pushout square. `FreeCofibrationCoproduct.lean` and
  `FreeCofibrationTransfinite.lean` prove coproduct and continuous transfinite
  closure. `FreeCofibrationClosure.lean` packages the full saturation operations
  for the original class. Its positive-degree restriction is unchanged.
  Forgetting dagger preserves all small limits/colimits and reflects colimits
  and isomorphisms (`FreeDagger.lean`, `ForgetfulReflection.lean`).
- `dj.cor.Fdag-free`: `FreeDaggerCofibration.lean` proves that the actual free
  functor, and indeed any adjoint to the original forgetful functor, sends
  simplicial monomorphisms to free cofibrations. `FreeBoundary.lean` defines
  the genuine free boundary generators, proves their saturation is contained
  in free cofibrations, and gives the exact underlying boundary lifting
  condition by the adjunction. The reverse inclusion is proved below.
- Both conclusions of `dj.lem.free-cof`: `RelativeSkeleton.lean` constructs the
  actual dagger-stable image-plus-skeleton stages, the original source at
  stage zero, and the actual target colimit. `RelativeCellBoundary.lean`
  proves the ordinary characteristic-map boundary preimage and the exact
  unique nondegenerate/epi normal forms for each stage difference.
  `RelativeCellOrbits.lean` selects individual new vertices in degree zero
  and genuine dagger-orbit representatives in positive degrees.
  `RelativeCellPresentation.lean` combines the boundary intersection, coverage,
  and interior uniqueness into actual attachment pushouts at every stage.
  It constructs a `RelativeCellComplex` for every free cofibration, then proves
  equality with the stated saturation of free boundary inclusions. The result
  applies to every actual free adjunction and every value universe `u`.
- The underlying cofibration obstruction in `pointset.cor.cofibrant-obstruction`:
  `NormalCofibrationObstruction.lean` proves that the initial-to-point dagger
  map satisfies `FreeCofibration` but its anti-involutive image is not normal.
  The actual initial and terminal universal properties are proved as well.
  This does not yet identify either predicate with a model structure's
  cofibrations or construct the comparison adjunctions.
- Parts (1)–(2) of `pointset.prop.weak-counterexample`:
  `UnitaryObstruction.lean` constructs the two-object integer dagger groupoid
  and its full subgroupoid on `0`. The inclusion is a fully faithful dagger
  functor and an ordinary equivalence, but is not unitarily essentially
  surjective. The nerve and weak-equivalence assertions in part (3) remain open.
- `bg.def.dagger-scat`, `bg.def.dagger-graph`, and the free construction at the
  start of `bg.lem.presentable`: `DaggerSimplicialCategory.lean` constructs the
  actual enriched dagger and opposite functors, with independent object and
  mapping-space universes. `DaggerSimplicialGraph.lean` and
  `FreeSimplicialPaths.lean` construct graphs and genuine finite-path mapping
  spaces with ordinary edgewise simplicial operators. `FreeSimplicialLift.lean`
  proves extension and uniqueness. `FreeDaggerSimplicialCategory.lean` builds
  the actual free–forgetful adjunction, identifies its unit with singleton
  inclusion, and proves the full bijective restriction property, at every
  common universe `u`. No cancellation quotient is used.
- The monadicity assertion of `bg.lem.presentable`:
  `DaggerGraphReflection.lean` lifts actual graph inverses and proves reflection
  of isomorphisms. `DaggerSplitCoequalizer.lean` constructs identity, composition
  and dagger on each graph-split quotient, with arbitrary object maps.
  `DaggerGraphDescent.lean` and `DaggerGraphCoequalizer.lean` prove the full
  coequalizer universal property and preservation. `DaggerSimplicialMonadicity.lean`
  then applies Mathlib's Beck theorem to the actual free adjunction. Thus the
  original graph forgetful functor is monadic, at every common universe `u`.
  The word finitarity and local finite presentability assertions are proved
  below as well.
- The graph presentability ingredient in the proof of `bg.lem.presentable`:
  `DaggerGraphIndex.lean` gives a small index with a vertex object, simplex
  edge objects, endpoint maps, and an involution commuting with ordinary
  simplex maps. `DaggerGraphPresheaf.lean` constructs an actual equivalence
  between dagger simplicial graphs and presheaves on this index, including
  arbitrary graph maps, natural unit/counit isomorphisms and the triangle law.
  `DaggerGraphPresentable.lean` transports all small limits and colimits and
  proves local finite presentability at the graph's value universe `u`.
  This graph result supplies the evaluations used in the word proof below.
- The word-finitarity ingredient in the proof of `bg.lem.presentable`:
  `DaggerGraphFiniteWords.lean` identifies recursive endpoint pullbacks with
  actual finite paths of each length, including arbitrary graph maps.
  `FreeSimplicialMap.lean` identifies the original left adjoint's map action
  with edgewise path extension. `FreeWordFinitary.lean` proves accessibility
  for each finite length, then their disjoint sum, and uses the actual graph
  evaluations to prove finitarity of the original free/forgetful composite.
  `DaggerSimplicialFilteredColimits.lean` derives creation of every small
  filtered colimit by the graph forgetful functor, existence of these colimits,
  and finite accessibility of that functor, without any remaining premise.
  `DaggerSimplicialLimits.lean` derives creation and existence of all small
  limits from monadicity. These results concern the graph forgetful functor;
  the different ordinary-category forgetful assertion in `bg.lem.creation`
  is proved separately below. General colimits are constructed next.
- The final local finite presentability assertion of `bg.lem.presentable`:
  `DaggerHomQuotient.lean` constructs actual enriched hom quotients, retaining
  ordinary simplicial maps, dagger, arbitrary object maps, and the full
  factorization universal property. `DaggerSemanticColimit.lean` applies this
  to the original free category on the graph colimit. Its relation is the
  intersection of the kernels of all existing cocone extensions; the relation
  lives in `Prop`, so homs stay in the original universe. The original diagram
  legs preserve identity and composition in this quotient, and the quotient,
  free-adjunction and graph-colimit universal properties give the actual
  colimit. No dagger-category colimit is assumed in this construction.
  `DaggerFiniteGenerators.lean` transports graph generators through the
  actual free adjunction, selects a small set of representatives, and proves
  finite presentability using the already proved accessibility of the graph
  forgetful functor. `DaggerSimplicialPresentable.lean` combines this small
  strong generator with the constructed colimits to prove unconditional local
  finite presentability at every common universe `u`. The complete conclusion
  of `bg.lem.presentable` is now proved, without postulating the manuscript's
  cited general finitary-monad theorem.
- `bg.lem.creation`: `SimplicialOpposite.lean` constructs the actual ordinary
  opposite equivalence, and `SimplicialObjectAdjunctions.lean` proves both
  adjoints to the object functor, hence its preservation of limits and colimits.
  The opposite constructions induce an involutive functor on any given ordinary
  limit or colimit apex; object-functor preservation proves it fixes objects.
  `DaggerOrdinaryLimitCreation.lean` and `DaggerOrdinaryColimitCreation.lean`
  retain the original apex and cone/cocone, lift the actual universal maps,
  and construct full Mathlib creation data using proved isomorphism reflection.
  `DaggerOrdinaryCreation.lean` states both conclusions without existence
  premises, for independent object, hom, and diagram universes.
- `bg.not.cells`, `bg.eq.A-univ`, and the following finite compactness assertion:
  `TwoObjectDaggerGraph.lean` constructs the literal graph with empty diagonal
  edges and off-diagonal copies of K. The original free category on that graph
  represents arbitrary target object pairs and one simplicial edge map.
  `TwoObjectGraphPresentability.lean` retains those endpoints in an actual
  pullback, including for empty or disconnected K, and proves finite
  presentability. `TwoObjectCellPresentability.lean` uses the original free
  adjunction and proved graph-forgetting accessibility to show that the same
  universal cell is finitely presentable for a finite simplicial set. The two
  closed conclusions have separate 57-line and 95-line Mathlib-only Challenges.
- `bg.lem.reduction`: `OrdinaryTwoObjectCell.lean` constructs
  the actual ordinary one-edge cell and its full universal property.
  `UnderlyingTwoObjectCell.lean` classifies ordinary functors out of the actual
  free dagger cell by two independent edge maps. `TwoObjectCellPushout.lean`
  proves its actual pushout decomposition into the two one-edge copies over
  the discrete two-object category; the reverse copy uses swapped labels.
  `DaggerSimplicialCofree.lean` constructs the actual right adjoint to ordinary
  forgetting, with hom C(x,y) times C(y,x), and proves colimit preservation.
  `SimplicialColimitsFree.lean`, `SimplicialHomQuotient.lean`,
  `SimplicialColimitKernel.lean` and `SimplicialColimits.lean` construct actual
  ordinary colimits from free paths and their semantic hom quotients, retaining
  arbitrary object maps and the original common universe. Ordinary attachment
  existence is therefore proved. `TwoCopyPushoutReduction.lean` proves the
  two-copy pasting result, and `TwoObjectCellReductionResolved.lean` applies it
  to the actual cells and their dagger attachment. The resulting isomorphism
  respects all three comparison legs and uses exactly the attachments along
  the given edge and its dagger. No pushout-existence premise remains. Thus
  the full reduction lemma is proved; ordinary colimits have a 40-line Challenge.
- Generator lifting in `bg.lem.I-inj`: `DaggerDiscreteObjects.lean` constructs
  discrete dagger categories with constant lifted equality homs, their full
  Hom/object-function equivalence, the actual initial empty category and
  terminal identity-only point, and proves that the empty-to-point map detects
  object surjectivity. A 91-line Challenge protects the same initial/terminal
  witnesses and lifting equivalence for all target functors.
  `TwoObjectCellLifting.lean` proves that actual free-cell lifting is equivalent
  to lifting on every full hom space, without endpoint restrictions.
  `DaggerGeneratingCofibrations.lean` defines the actual `I†` as all free boundary
  maps, including dimension zero, together with the object generator. Its RLP
  is exactly object surjectivity plus boundary RLP on every hom. Identifying the
  latter with a Kan fibration that is a weak homotopy equivalence remains open.
  The full model-categorical `bg.lem.I-inj` assertion is not yet claimed.

`formalization.yaml` and `CORRESPONDENCE.md` specify the exact checked scope.

## A — dagger Bergner model structure

Targets: `bg.thm.main` (line 1119), `bg.thm.left-proper` (line 1143).

Required chain:

1. Dagger simplicial categories (`bg.def.dagger-scat`), dagger graphs,
   free categories, limits/colimits, and local presentability.
   The categories, graphs, concrete free construction and adjunction are now
   implemented, monadicity over dagger graphs is proved, and the graph category
   is locally finitely presentable by an actual presheaf equivalence. The word
   monad is finitary. All small limits and colimits and local finite
   presentability of dagger simplicial categories are now proved, completing
   `bg.lem.presentable`. Creation of limits and colimits by the different
   ordinary-category forgetful functor (`bg.lem.creation`) is now also proved.
   Two-object free cells and their finite presentability (`bg.not.cells`,
   `bg.eq.A-univ`) are proved, including the full unrestricted universal property.
   Actual ordinary colimits and the complete successive-attachment comparison
   in `bg.lem.reduction` are proved, with all required pushouts constructed.
2. Fixed-object model structures (`gb.cor.sGph-model`, `bg.thm.fixed-object`).
3. Natural unitary intervals, their extraction and realization, and coherent
   unitary equivalences (`bg.def.interval`, `bg.prop.cu-groupoid`).
4. The exact classes `W†`, `I†`, `J†` (`bg.def.W`, `bg.def.IJ`), two-out-of-three,
   cell and lifting results, and the recognition theorem's hypotheses.
   The actual `I†` is defined and its full boundary-RLP characterization is proved.
   The comparison with trivial Kan fibrations still requires ordinary SSet theory.
5. The actual model structure, specified generating sets, characterization of
   trivial fibrations, combinatoriality, and left properness.

Pinned mathlib supplies enriched categories/functors, a general `ModelCategory`
class, weak factorization systems, and small object machinery. It does not
supply the ordinary Bergner model structure needed here. Its
`SimplicialSet.CategoryWithFibrations` defines Kan fibrations by horn lifting,
but describes the SSet Quillen model structure as TODO. In particular, it does
not supply the required boundary-RLP/trivial-fibration comparison with actual
weak homotopy equivalences. A degree-zero dagger category does not replace a
dagger simplicial category. The external Kan–Quillen source recorded below is
a candidate dependency to port and audit, not an assumed theorem.

## B — dagger Joyal structure and rigidification equivalence

Targets: `dj.thm.main` (line 1810), `dj.thm.equivalence` (line 1848).

Required chain:

1. The presheaf equivalence, local presentability, and free–forgetful adjunction,
   including the explicit pushout description (`dj.not.adjunctions`), are
   implemented above.
2. Ordinary rigidification and coherent nerve, compatibility with opposites,
   and the concrete lifted adjunction (`dj.lem.lift`).
3. Cellular characterization of free cofibrations (`dj.lem.free-cof`),
   preservation by rigidification, and accessibility of weak equivalences.
   The cellular characterization is complete: every free cofibration has an
   actual relative free-boundary-cell presentation, and saturation equality
   is proved. Preservation by rigidification and accessibility of the weak
   equivalences remain to prove.
4. The recognition theorem with `W = C†⁻¹(W†)` and the exact `FreeCofibration`
   class, followed by the fibrant counit and Quillen-equivalence criterion.

The `FreeCofibration` class requires freeness of new nondegenerate simplices
only in positive degrees. Replacing it by all monomorphisms would change B.
Mathlib has the coherent nerve's definition but not the required ordinary
Joyal–Bergner adjunction/equivalence. Mathlib supplies relative skeletons and
their successor formula. This companion now proves the actual dagger-cell
pushout decomposition as well. The ordinary Joyal–Bergner machinery and its
dagger-compatible lift are still required.

## C — recognition using the unitary core

Target: `dj.thm.intrinsic-equivalence` (line 2985).

The target applies to dagger quasi-categories. Its unitary core is the full Kan
subcomplex of a homotopy-fixed-point complex spanned by the canonical vertices.
Strict fixed points or the ordinary maximal core do not express this definition.

Required chain: Real realization and the reversal action; `EC₂` and homotopy
fixed points; canonical vertices and `def.unitary_core`; full Kan subcomplexes;
derived-fixed-point and Real edgewise comparison; equivariant path spaces and
the coherent unitary interval criterion; local mapping-space comparison and
ordinary recognition. Restricting the target to dagger Joyal fibrant objects
would also change its scope.

### Source statements that need explicit repair before formalization

`dj.prop.strict-borel-presentation` (line 2623) has a broken sentence. Its proof
uses an equivalence `e` at line 2636, but the proposition does not introduce `e`.
The intended input appears to be a monomorphism `O → A` and a specified
equivalence `e : A ≃ B` in `Fun(BC₂, S)_{O/}`, to be represented by a strict Borel
weak-equivalence zigzag under `O`. This restoration must be stated explicitly
before formalizing it; it has not been silently assumed in this library.

The earlier proof of `dj.prop.real-identity-section` also retains undeclared
`X`, `ρ`, and `σ`; the following detailed proof supplies typed composites.
These manuscript issues do not affect the new presheaf or strict obstruction
proofs. This development has not edited the separately maintained manuscript.

## D — failure of the two specified Quillen adjunctions

Target: `pointset.cor.no-naive-quillen` (line 3500).

Required chain:

1. The tagged index category and its quotient; presheaf comparison and the
   concrete left and right Kan-extension adjunctions $q_! \dashv q^* \dashv q_*$.
2. The DCH model structure's actual cofibrations and trivial cofibrations,
   together with B and the comparison of free completions.
3. The fixed-vertex obstruction (underlying predicates implemented above)
   shows the inclusion fails to preserve cofibrations.
4. The double-walking-isomorphism generator maps to a map that is not a dagger
   weak equivalence. This uses free completions, rigidification, and the
   integer groupoid's strict unitary obstruction (implemented above).

The two concrete examples alone do not prove D. Completion requires proving
failure of the two actual adjunctions to satisfy the Quillen conditions.

## External Kan–Quillen implementation to evaluate

The source of
[joelriou/topcat-model-category at 6c0c356](https://github.com/joelriou/topcat-model-category/tree/6c0c356fea469689fe76baeb47ba773460dfacee)
contains an actual simplicial-set `ModelCategory` instance in
[`ModelCategorySSet.lean`](https://github.com/joelriou/topcat-model-category/blob/6c0c356fea469689fe76baeb47ba773460dfacee/TopCatModelCategory/ModelCategorySSet.lean),
the realization–Sing Quillen adjunction, and unit/counit weak-equivalence proofs.
No corresponding `IsQuillenEquivalence` instance was found in that source;
the README's broader claim is not used as an instantiated theorem here.

Its pins are Lean `v4.25.0-rc2` and mathlib
`6c193806481aaf608f1396601b6dc95277ddcfe8`. This companion uses Lean `v4.27.0`
and mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900`.
The external source was inspected, not imported or compiled in this project.
Porting, compilation, license preservation, and a transitive axiom audit are
required before treating it as a checked dependency. It does not supply the
Bergner/Joyal/rigidification results needed by A–C.
