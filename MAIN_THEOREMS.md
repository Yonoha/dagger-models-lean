# Part I main-theorem formalization

The additive Theorem A bridge now passes local typechecking against accepted
dependencies, including `DaggerComparator.mainA.{u}` and its standard-three-axiom
check. The full current 2771-module sequential and ordinary Lake builds passed
locally. The expanded all-owner audit passed for 40,022 declarations, 71
advertised results and eight main roots, including all four negative controls
and a byte-identical restored positive. The local Comparator run passed five A
cases and five retained portable controls, including default-kernel replay for
the positive cases and rejection of three A negative fixtures.
The local ARM64 Linux partial-cache continuation passed all nine B/C/D lane
cases, including the public B/C/D re-exports from the new 2771-source
snapshot, and five A cases.
Its 40,022-declaration/71-result/eight-main-root audit, four rejected audit
mutations and separately restored byte-identical positive were accepted as one
local result; see [A_VERIFICATION.md](A_VERIFICATION.md). This is not a cold
rebuild, a single newer-controller run or hosted GitHub CI. The B/C/D evidence
below describes its separate frozen 2767-module scope.

The saved package passed official Comparator and default-kernel replay for B,
D, and the universe-zero instance of full C, with a passing normal control and
rejected theorem-mismatch and forbidden-axiom controls. The saved C wrapper
fixes `Statement.{0}`. The original C statement and proof, and the public
alias compiled below, are universe-polymorphic at `Statement.{u}`. The new
generic Challenge compiled and passed a strict closure guard against the old
frozen export: 46,951 non-root records match exactly, and the full root record
matches after `u = 0` specialization. Actual public C Comparator and
default-kernel replay subsequently passed locally. The source-correspondence
review found no concrete weakening or circular assumption in those three Lean
statement types. This is an agent review, not independent human validation of
the manuscript translation or of the proofs.

The public `MainTheoremsBCD.lean` aliases `DaggerComparator.mainB`,
`DaggerComparator.originalMainTheoremC` and `DaggerComparator.mainD` are now
in the local source-integrated library. The accepted 2767-module sequential
and default Lake build and the data-only audit of 40,006 owned declarations
passed locally; the audit rejected all four negative controls and passed the
restored positive run. The actual public B, generic C and D exports passed official Comparator and
default-kernel replay locally. Direct trusted data exports matched all three
kernel-accepted exports byte for byte. A separate exact-commit Linux result for
that historical 2767-module lane and new publication are not claimed. The 185 included
`TopCatModelCategory` modules reuse upstream source; provenance and unresolved
upstream terms are documented in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
The cited B/C/D records do not prove A. The 27 foundation Challenges and their
112 registered roots remain a separate retained lane.

The following foundation milestones were written before the B/C/D certificates;
where a dependency is described as open there, that statement is historical.
The labels refer to the author's Part I manuscript, with navigation details in
the source-correspondence review. No target is added as an axiom or a proof-hole
placeholder.

## Retained foundation milestones (historical scope)

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
  the full reduction lemma is proved. Ordinary colimits retain their root in
  the 99-line Challenge extended below for ordinary rigidification.
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
- Ordinary inputs to `bg.lem.I-inj`: `SSetBoundaryFibration.lean` proves that
  actual Mathlib boundary RLP implies its Kan fibration property.
  `SSetBoundaryCellsCore.lean`, `SSetBoundaryCellsAttachment.lean` and
  `SSetBoundaryCells.lean` construct actual countable relative boundary-cell
  presentations for all ordinary monos, using all new nondegenerate simplices,
  including vertices. They retain the original map, source and target, allow
  nonmonic characteristic maps, and prove boundary-cell closure equals monos
  and actual `I.rlp = monomorphisms.rlp`, for every value universe.
  `SSetMonoRLPRetraction.lean` and `SSetBoundaryRetraction.lean` supply one
  section and one cylinder homotopy with all four simultaneous laws over the
  target. No source/target Kan premise or weak-equivalence conclusion is used.
- The local part of `bg.def.IJ` and `bg.lem.Iinj-in-Jinj`:
  `DaggerLocalFibrations.lean` defines the actual positive horn family `J†loc`
  and proves its RLP is exactly Kan fibrations on every full hom space.
  Actual `I†` RLP implies object surjectivity and this local condition.
  Unitary interval extraction, lifting and the full `J†` condition remain open.
- Small-object input in the proof of `bg.thm.main`:
  `SmallObjectFiniteDomains.lean` proves the generic finite-domain bridge to
  Mathlib's `HasSmallObjectArgument`, with independent category/hom/auxiliary
  universes and explicit smallness, local-smallness and colimit hypotheses.
  `DaggerSmallObject.lean` discharges them for the original `I†`, using its
  finitely presentable boundary domains, initial empty domain, literal union
  smallness and proved dagger-category colimits. This gives unconditional
  small object and actual functorial factorization data at every common `u`,
  with left class `I†.rlp.llp` and right class `I†.rlp`. It does not identify
  either class with a model-structure predicate or treat `J†` interval cells.

The four 15/27/27/21-line Challenges protect seven results: four ordinary
lifting/cell conclusions, two simultaneous section/homotopy conclusions, and
one generic finite-domain theorem. Local `J†loc` and the actual `I†` application
are separately reviewed and audited auxiliary results. That stage retained
102 prior roots and 23 prior specifications/configurations. The ordinary
rigidification adjunction and its two natural comparisons add three roots by
extending the colimits Challenge from 40 to 99 lines, retaining all 109 preceding
roots and the other 26 specifications/configurations. Current coverage is 27
Challenges, 1,929 physical lines and 112 roots (109 mathematics plus three
markers), with the two existing 160/116-line exceptions unchanged.

`formalization.yaml` and `CORRESPONDENCE.md` specify the exact checked scope.

## A — dagger Bergner model structure

Targets: `bg.thm.main`, `bg.thm.left-proper`.

The following chain is an earlier foundation plan; its open markers are
historical, not the status of the current A theorem. The current A bridge
combines the existing standard model and left properness proofs. Its precise
verification status is in
[A_VERIFICATION.md](A_VERIFICATION.md).

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
   Ordinary boundary RLP now implies actual Kan fibrations, and all ordinary
   monos have actual relative boundary-cell presentations. Boundary-RLP maps
   have sections and cylinder homotopies over their targets. The actual local
   horn family has the correct all-hom Kan RLP equivalence, and `I†` admits
   unconditional small object and functorial factorization data. The missing
   ordinary comparison is with actual weak homotopy equivalences and trivial
   Kan fibrations. The full `J†` interval lifting and recognition hypotheses
   remain open.
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
a candidate source to evaluate, not an assumed theorem. The present boundary,
cellular and small-object proofs were constructed independently from pinned
Mathlib and this project's checked lemmas. At that foundation stage no
external Lean bodies were copied; later B/C/D source reuse is recorded below.

## B — dagger Joyal structure and rigidification equivalence

The original `dj.thm.main` and `dj.thm.equivalence` are represented by
`DaggerActualMainTheoremBChallenge.statement.{u}`. It includes the model
classes, local presentability and generators, left properness, and the
rigidification–nerve Quillen equivalence for the actual dagger simplicial set
and dagger simplicial category structures. The free-cofibration and weak-class
predicates agree with the manuscript definitions. The internal bridge from
ordinary boundary lifting to ordinary trivial Kan fibrations is explicit.
The local B certificate passes frozen-statement Comparator and kernel replay.

## C — recognition using the unitary core

`ChallengeOriginalMainTheoremC.Statement.{u}` expresses the three conditions of
`dj.thm.intrinsic-equivalence` for **every** map between original dagger
quasi-categories. The fully faithful condition quantifies over every ordered
pair of original vertices, including repeated pairs. Conditions (2) and (3)
use the same original unitary-core functor; no extra Kan, comparison or endpoint
hypothesis is added. The saved local C certificate passes its unchanged
pre-proof frozen Challenge at universe zero. The polymorphic source theorem
compiled and passed the all-owner audit; the generic Challenge compiled and
passed the frozen-closure guard; actual public Comparator and default-kernel
replay subsequently passed locally. Matching the
coslice-fibre implementation of mapping spaces to the manuscript's `Map_X(x,y)`
is a separate mathematical interpretation recorded in the source review.

The manuscript's `dj.prop.strict-borel-presentation` has an undeclared `e` in
its proof, and `dj.prop.real-identity-section` has undeclared symbols in an
earlier proof. The Lean C result did not silently edit those manuscript lines.

## D — failure of the two specified Quillen adjunctions

`ChallengeActualMainTheoremD.Statement.{u}` states existence of the DCH-side
model with all three classes identified, failure of **both** original tagged
quotient adjunctions to be Quillen, and failure of naive restriction by a
cofibration-class disagreement. It is not merely a non-Quillen claim
conditional on an assumed model. The local D certificate passes
frozen-statement Comparator and kernel replay. Internal source bridges identify
the right-induced weak equivalences and fibrations with the separately
constructed ordinary Joyal Smith model. An independent audit of the external
DCH literature is outside the recorded agent correspondence review.

## External Kan–Quillen reuse provenance

The early bounded probe of `joelriou/topcat-model-category` is recorded in
[EXISTING_FORMALIZATIONS.md](EXISTING_FORMALIZATIONS.md); its partial build
counts describe that probe, not the later local B/C/D certificate status.
The substantive later development reuses pinned Mathlib and selected
`TopCatModelCategory` source from original commit
`6c0c356fea469689fe76baeb47ba773460dfacee`, ported to Lean 4.27 and
Mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900`. Native API repair
and source provenance are recorded in the saved certificate package. This is
not a claim that the entire original external project was adopted unchanged,
that all of its source was independently reviewed, or that the current tree has
passed a cold rebuild or hosted GitHub CI. The current 185-module reused source closure
is included in the accepted local build and all-owner data-only audit; its
upstream distribution terms are not yet confirmed.
