# Existing formalizations and reuse decisions

Inventory date: 2026-10-01. Baseline companion commit:
`46153c46525fd99ca0f763afd75c6002e1e2a860`; Lean `v4.27.0`; Mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900`.

The author requests examination of existing results before new implementation
and permits retaining already checked custom proofs. Replacing every overlapping
proof is not an objective. The complete A–D targets remain in
[MAIN_THEOREMS.md](MAIN_THEOREMS.md); finding an upstream theorem does not
complete those targets.

## Evidence levels

- **Used:** the companion already imports the library and applies its results.
- **Source found:** an exact declaration was inspected, but it has not been
  integrated and verified with this companion's dependencies.
- **Compatibility tested:** only the named files compile in the tested environment.
- **Integrated and checked:** the actual companion build, transitive axiom audit,
  statement correspondence, and applicable Comparator checks pass.

An upstream README, a filename, or a related weaker theorem is not sufficient
evidence to promote a result to the next level.

## Results already reused

| Manuscript use | Existing result | Companion application and decision |
| --- | --- | --- |
| Small-object input to `bg.thm.main` | Mathlib `MorphismProperty.HasSmallObjectArgument` and its functorial factorization instance | Keep `SmallObjectFiniteDomains.lean` and `DaggerSmallObject.lean`. The general small object argument was not reconstructed here. |
| Monadicity in `bg.lem.presentable` | `Monad.monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms` | Keep `DaggerSimplicialMonadicity.lean`. The actual dagger split coequalizers and reflection hypotheses remain project-specific. |
| Presheaf and graph presentability | Mathlib `Presentable.Presheaf` and `Presentable.Adjunction` | Keep `Presentable.lean` and `DaggerGraphPresentable.lean`. The actual index categories and equivalences require their own constructions. |
| Ordinary Kan lifting in `bg.lem.I-inj` and `bg.def.IJ` | Mathlib `SimplicialSet.CategoryWithFibrations` | Keep `SSetBoundaryFibration.lean` and `DaggerLocalFibrations.lean`, retaining the original horn-lifting definition and arbitrary source/target objects. |

Pinned Mathlib also supplies `HomotopicalAlgebra.ModelCategory`, its
`ModelCategory.mk'` constructor from weak factorization systems, and general
lifting/factorization infrastructure. These are available tools, not an
already constructed dagger model structure.

## Overlap that does not require immediate replacement

Public Mathlib documentation contains
[`SSet.relativeCellComplexOfMono`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SimplicialSet/Skeleton.html):
every ordinary simplicial monomorphism is a relative cell complex on boundary
inclusions. This declaration is absent from the companion's pinned Mathlib
source. `SSetBoundaryCells.lean` already proves the corresponding construction
and its lifting-class consequences.

**Decision:** retain the checked companion implementation. If a dependency
upgrade is needed for a missing high-value result, assess this overlap during
that migration. Do not upgrade solely to replace a working proof or write
another ordinary cell decomposition. This ordinary theorem alone does not
supply the dagger orbit construction in `RelativeCellPresentation.lean`.

## Priority candidate: ordinary Kan–Quillen theory

Source:
[`joelriou/topcat-model-category` at `6c0c356fea469689fe76baeb47ba773460dfacee`](https://github.com/joelriou/topcat-model-category/tree/6c0c356fea469689fe76baeb47ba773460dfacee).
GitHub's commit API was checked on 2026-10-01: this was still `master`.
Its pins are Lean `v4.25.0-rc2` and Mathlib
`6c193806481aaf608f1396601b6dc95277ddcfe8`.

| Exact declaration | Meaning and required scope | Intended use |
| --- | --- | --- |
| `SSet.modelCategoryQuillen.weakEquivalence_iff_of_fibration` | For arbitrary `E B : SSet` and a Kan fibration `p : E ⟶ B`, `I.rlp p ↔ WeakEquivalence p`, without Kan assumptions on `E` or `B`. | Complete the ordinary comparison in `bg.lem.I-inj`. |
| `SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations` | Actual boundary RLP equals actual trivial fibrations for this weak-equivalence structure. | Combine with the proved object-surjectivity/all-hom boundary-RLP characterization of `I†`. |
| `SSet.modelCategoryQuillen.inst` | An actual `ModelCategory SSet` instance. | Supply ordinary model-category input, with further properties checked as required. |

The first theorem is in
[`SSet/KeyLemma.lean`](https://github.com/joelriou/topcat-model-category/blob/6c0c356fea469689fe76baeb47ba773460dfacee/TopCatModelCategory/SSet/KeyLemma.lean);
the other two are in
[`ModelCategorySSet.lean`](https://github.com/joelriou/topcat-model-category/blob/6c0c356fea469689fe76baeb47ba773460dfacee/TopCatModelCategory/ModelCategorySSet.lean).
The similarly named `SSet.KanComplex.weakEquivalence_iff_of_fibration` assumes
fibrant source and target and cannot replace the arbitrary-object result.

Upstream weak equivalences use geometric realization and the singular Kan
complex's homotopy/fundamental-groupoid invariants. They are not boundary RLP
renamed. A companion bridge must retain and explain these definitions, rather
than silently replacing the manuscript's weak equivalences.

**Status:** a fresh bounded compatibility test completed against the unchanged
archive and the companion's current pin. The `ModelCategorySSet` closure has
183 external modules and 40,050 lines. All 136 direct Mathlib import sources
exist; after retrieving their pinned caches, none of those direct artifacts
is missing. Of the 183 original modules, 44 compile (three with deprecation
warnings), 13 fail on source/API differences, and 126 are blocked by failed
prerequisites. Neither target theorem nor the complete model structure has
been compiled or transitively axiom-audited here. These module counts are not
percentages of proof completion.

The concrete issues include old import paths, newly bundled full-subcategory
morphisms, renamed ordered ordinal representations, and declarations now
already present in Mathlib. Two bounded adaptation experiments succeeded:
six mechanical edits in `Fin.lean` retained every statement and passed strict
compilation plus an audit of the four affected theorems; replacing one import
in `MonoidalClosed.lean` compiled the unchanged declarations and bodies.
Mixed duplicate modules must be adapted selectively, retaining their remaining
helpers. Diagnostic records are preserved locally under
`build/reuse-20261001/topcat-compatibility/`; they are not a published dependency
or a full-model verification certificate.

A bounded first compatibility pass is now frozen locally. Fourteen changed
modules compile with warnings treated as errors. A traversal with those late
strict recompiles accounted for has 61 compiled modules, five direct failures,
and 117 not compiled because prerequisites had not succeeded at their traversal
positions; that last count is not a fresh assertion that every such module still
fails. The remaining direct failures include `SSet.Subcomplex`, `Arrow`, the
pseudofunctor module, convenient categories and full-subcategory limits.

Nineteen reused declarations have explicit signature checks. These include
equality reversal in pushout/pullback statements, changed binder order, and
the opposite-object specialization of the generalized `uliftCoyoneda` API.
The original mathematical propositions and definition data are retained.
Lean's transitive axiom collector checks 439 declarations: 414 belonging to
the fourteen successfully adapted modules and 25 signature-bridge declarations
including generated auxiliaries. Only the three permitted standard axioms
occur. This is not an audit of every declaration in all 61 compiled modules.
The full model structure and the two desired comparison theorems remain
uncompiled and unaudited. The immutable original sources, exact adaptation
diff, source/artifact hashes and logs are preserved; local diagnostic copies
are under `build/reuse-20261001/topcat-compatibility/phase1/`.

Subsequent bounded passes retain the same dependency pins and upstream archive.
The fourth joint pass has 94 compiled modules, seven direct compilation failures,
and 82 modules blocked by prerequisites. These are compilation counts, not a
percentage of the target theorem proved. The key comparison in `SSet/KeyLemma`
and the final `ModelCategorySSet` module remain uncompiled and unaudited.

The latest six adapted modules reuse Mathlib's actual dimension classes,
standard-simplex face isomorphisms, endpoint inclusions and closed-category
classes. Twenty-nine named SSet duplicates and three duplicate instances were
replaced by their existing Mathlib declarations. Explicit checks retain the
original types and, for the constructed isomorphisms and inclusions, the full
data by `rfl` equalities. Nonduplicate helpers and unrestricted universes are
retained. The two convenient-category adaptations preserve the chosen internal
hom adjunction and the underlying open-immersion lifts.

Strict compilation and transitive audits cover all owned/generated declarations
and explicit compatibility checks: 308 declarations for the four SSet modules
and 131 for the two convenient-category modules. Independent agent/root source
review and diagnostic replay found no weakening of statements or data. This is
not independent human review or an exhaustive audit of all 94 compiled modules.
Frozen local evidence is under
`build/reuse-20261001/topcat-compatibility/phase4-{sset,core,joint}/`;
no external proof bodies have been integrated into the published companion.

**Decision:** prioritize a compatible pinned dependency or documented
compatibility adaptation before independently proving this standard theory.
Preserve attribution. Repository-level licensing was not established for the
inspected archive; no external proof bodies have been copied into the published
companion. Adoption must record the actual source and applicable terms.

## Concrete reuse route for ordinary rigidification

In the pinned `Mathlib/AlgebraicTopology/SimplicialNerve.lean`,
`CategoryTheory.SimplicialThickening.functor` constructs the actual enriched
functor induced by an order homomorphism. Its `functor_id` and `functor_comp`
lemmas permit bundling the standard cosimplicial diagram using the companion's
`SimplicialCat.of`. The mapping spaces remain nerves of the interval-subset
posets, with composition induced by union; no substitute diagram is needed.

`CategoryTheory.SimplicialNerve` has simplices
`EnrichedFunctor SSet (SimplicialThickening (ULift (Fin (n + 1)))) C`.
Its simplicial operators are precomposition by that exact thickening functor.
For the companion's bundled target, use the canonical `ForgetEnrichment SSet
C.Obj` type synonym with the inherited enrichment and underlying category.

The same pinned Mathlib's `CategoryTheory/Limits/Presheaf.lean` supplies
`Presheaf.restrictedULiftYoneda` and `Presheaf.uliftYonedaAdjunction`.
The latter constructs the left adjoint from a pointwise left Kan extension
along `uliftYoneda`. The companion's already proved
`DaggerModels.simplicialCatHasColimits` supplies ordinary simplicial-category
colimits. This supplies the following bridge in
`DaggerModels/OrdinaryRigidification.lean`:

1. Bundle the existing standard thickening diagram at every common universe.
2. Identify its restricted Yoneda functor naturally with the existing coherent
   nerve, retaining arbitrary object maps and all simplicial operators.
3. Apply Mathlib's Yoneda-extension adjunction to obtain ordinary rigidification.

This targets the ordinary adjunction recalled in `dj.not.adjunctions`, an input
to `dj.lem.lift`. It does not yet prove the dagger lift, opposite coherence,
fibrancy, model structures, or Quillen equivalence. The chosen left Kan extension
also has a natural isomorphism on standard simplices with the original thickening
diagram. Pinned Mathlib's `SSet.stdSimplex` is definitionally `uliftYoneda`.
Status: the 144-line bridge passes strict compilation and its 32 declarations
have only the three permitted standard axioms. The integrated 1,496-job build,
all 2,576 project declarations' transitive axiom audit, both audit negative
controls, Challenge registration checks and formalization metadata checks pass.
The 99-line expanded Challenge has 42 literal declaration comparisons with zero
differences, excluding only the four configured theorem-proof bodies.
The real Linux Comparator
[run 36859605890](https://github.com/Yonoha/dagger-models-lean/actions/runs/36859605890)
accepted all four simplicial-colimit/rigidification roots and 24 of the 27
registered groups overall (106 roots), and both negative controls passed.
GitHub then terminated the job at its configured 60-minute limit while the
boundary-cell group was running. This is not a successful complete Comparator
run. The job allowance is now 90 minutes, based on the observed roughly
2.3-minute positive-group replays; all 27 groups and both negative controls
remain required. The full green CI gate and independent human review are not
claimed by these partial-run results.

## Other primary sources checked

- Pinned Mathlib's `ModelCategory.mk'`,
  `MorphismProperty.IsWeakFactorizationSystem.mk'`, and
  `MorphismProperty.llp_rlp_of_hasSmallObjectArgument` provide the general assembly
  machinery. No complete Hovey/Smith recognition or monadic/right-induced
  transfer theorem was located in that inspected tree. The manuscript's actual
  lifting-class equalities and cellular weak-equivalence inclusions remain
  inputs to establish, not assumptions to postulate.
- Official newer Mathlib at
  [`738e62bd6df530a89ac01b20e937ad70923a7b96`](https://github.com/leanprover-community/mathlib4/blob/738e62bd6df530a89ac01b20e937ad70923a7b96/Mathlib/AlgebraicTopology/ModelCategory/Transport.lean)
  contains `ModelCategory.transport`. It transports a model structure along
  an equivalence of categories with the three inverse-image class equations.
  It is not a right-induced or monadic transfer theorem. It was inspected,
  not compiled or added as a dependency here.
- The inspected
  [TauCeti tree `b6a5eabd5b8d44c588393d9b5efedd5dd0ca5431`](https://github.com/TauCetiProject/TauCeti/tree/b6a5eabd5b8d44c588393d9b5efedd5dd0ca5431)
  has an enriched-opposite functor overlapping the companion's checked work.
  No Bergner/Joyal/rigidification/model-recognition implementation was located
  in that tree. Retain the checked companion opposite construction.
- Riou's `QuillenAdjunction.lean` defines `IsQuillenEquivalence`, but no instance
  for the SSet–TopCat adjunction was found in the inspected project. Its actual
  Quillen-adjunction instance and unit/counit weak-equivalence proofs should
  not be reported as an already integrated Quillen-equivalence instance.

## Remaining scope and implementation policy

Pinned Mathlib does not supply the ordinary Bergner model structure or the full
Joyal–Bergner rigidification equivalence required by A–C. It has enriched-category
infrastructure and the coherent nerve's definition. The bounded primary-source
search above is not a claim of global nonexistence elsewhere.

Before a substantial new implementation:

1. Record the manuscript statement and exact existing declarations examined.
2. Check types, hypotheses, universes, and definitions behind the predicates.
3. Prefer an application or a small bridge to a compatible existing theorem.
4. Retain checked custom results unless replacement has a concrete benefit.
5. Implement a missing result after recording the remaining gap.
6. Preserve independently reviewable Challenges, all comparison targets, axiom
   checks, and honest partial-status metadata. Explain dependency-pin or trusted
   specification changes before making them.

No main theorem A–D is claimed by this inventory. The frozen unintegrated stage
under `build/next-stage-after-46153c4` is not counted as a published result.
