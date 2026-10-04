# Existing formalizations and reuse decisions

Inventory date: 2026-10-01. Baseline companion commit:
`46153c46525fd99ca0f763afd75c6002e1e2a860`; Lean `v4.27.0`; Mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900`.

The author requests examination of existing results before new implementation
and permits retaining already checked custom proofs. Replacing every overlapping
proof is not an objective. The complete A–D targets remain in
[MAIN_THEOREMS.md](MAIN_THEOREMS.md); finding an upstream theorem does not
complete those targets.

Latest verified checkpoint (2026-10-04, Phase15): the private compatibility
adaptation of the original `ModelCategorySSet` dependency closure now compiles
**183/183 modules**, including the arbitrary-source/target `SSet.KeyLemma` and
the actual `ModelCategory SSet` instance. All 183 import together with the
published `DaggerModels` code. The fresh transitive axiom union for all
**8,696 owned/generated declarations** contains only `propext`,
`Classical.choice`, and `Quot.sound`; all 406 frozen evidence hashes were
verified. This completes this closure's local compatibility check, not the
Part I main theorems: **A–D remain 0/4**. The external adaptation is unpublished,
repository-level licensing remains unresolved, and public adoption and
verification of the manuscript bridge are separate remaining steps. Historical pass counts below
describe earlier checkpoints, not the current completion rate. The frozen
report metadata is in
`build/reuse-20261001/topcat-compatibility/phase15-joint/report.json`.

The next private application is now checked as well: the 70-line
`IinjBridge.lean` proves the actual `bg.lem.I-inj` equivalence, retaining the
existing dagger generators, object surjectivity, all object pairs (including
the diagonal), all boundary dimensions (including zero), and the original
geometric weak equivalence. Three additional exact-type checks confirm the
arbitrary-source/target upstream theorem, class equality, and ordinary model
instance. All eight new declarations pass strict compilation and a transitive
axiom-union check with only the three standard axioms. A separate agent source
review found no correspondence issue within the existing common universe
`{u,u}`; independent object/hom universe generalization is not claimed. This
application is not yet in the published library or Comparator registry.
Source and review evidence are archived under
`build/reuse-20261001/iinj-bridge-20261004/` and
`build/reuse-20261001/iinj-correspondence-review-20261004/`.

Two further private checkpoints now pass strict compilation, actual mixed
imports with `DaggerModels`, and scoped transitive axiom checks. The actual
coherent nerve has a natural opposite comparison `O ⋙ N ≅ N ⋙ S`, with full
enriched-functor inverse equations, all simplex-operator and target-functor
naturality, and double-opposite coherence (47 audited roots including checks).
Its actual degree-zero simplices are naturally equivalent to the original
object type, with equality of the full enriched-functor data (34 audited roots
including checks). Both retain the original thickening, outer lifts, and
common universe `u`, without an added fibrancy premise. Their 37 and 26 frozen
evidence entries and respectively 33 and 17 provider/artifact hashes were
checked again when recording this status. These two local checkpoints alone
do not prove the dagger adjunction or any A–D main theorem; the subsequent
adjunction checkpoint is described below. Published Comparator totals remain
unchanged. Metadata and project-owned scratch sources
are archived under `build/reuse-20261001/nerve-opposite-author-20261004/` and
`build/reuse-20261001/nerve-vertices-author-20261004/`.

Subsequent private results retain the same original constructions. The actual
dagger coherent nerve now has the strict reversal involution, full fixed
vertices and all dagger morphisms, with its literal underlying nerve functor
unchanged (27 audited roots including checks). The rigidification/opposite
isomorphism is the inverse mate under the original uncomposed adjunction;
its inverse, full mate formula and involution coherence are proved (43 roots).
Separate agent source/correspondence reviews approve both within this scope.
The canonical rigidification vertex/object map is the actual original unit
evaluated at the original zero object. Its bijectivity follows from the
representable formula and Mathlib's colimit-preserving Yoneda-extension API;
its eight checks and 33-root transitive audit pass. A separate source review
also approves this exact natural identification. All three batches pass strict
source/checks and actual `DaggerModels`
mixed imports, with only the three standard axioms. Evidence is archived under
`coherent-nerve-author-20261004/`, `rigidification-opposite-author-20261004/`, and
`rigidification-vertices-author-20261004/` inside `build/reuse-20261001/`.
The actual dagger left functor is now also checked and root source-reviewed
(37 roots including 19 exact checks). It reuses `ofOppositeFunctor` and
`Hom.ofCommutingOpposite`, fixes every original object via the canonical vertex
equivalence, and retains the entire original underlying functor literally.
The lifted dagger adjunction passes strict source checks, ten exact contracts,
mixed imports and a 30-root transitive axiom audit. The Hom bijection is the
restriction of the original ordinary adjunction, and the actual unit and full
enriched counit retain their original underlying maps; both triangle identities
hold. A separate agent source/correspondence review is complete with no
findings in this scope; its five frozen evidence entries were verified.
These two batches
are archived under `rigidification-dagger-author-20261004/` and
`lifted-adjunction-author-20261004/`.
The actual ordinary-category free dagger adjunction now reuses the existing
graph-free construction, `HomKernel`, and `HomQuotient`. Its original objects,
composition-preserving unit, full Hom equivalence and actual adjunction pass
13 exact checks and a 58-root audit, followed by separate agent source review.
The actual free-functor comparison then applies Mathlib's
`Adjunction.leftAdjointUniq`, retaining the identity mate and both composite
unit/counit equations. It is instantiated with this constructed adjunction;
no free-adjunction premise remains. All conclusions of `dj.lem.lift` pass
locally, including a further 21-root comparison audit and separate source
review. The reviewed final conjunction generalizes its four clauses to
independent universes; specializing all four to any common `u` gives the
manuscript statement. These batches and reviews are archived under
`ordinary-free-author-20261004/`, `ordinary-free-correspondence-review-20261004/`,
`free-comparison-author-20261004/`, and
`free-comparison-correspondence-review-20261004/` inside `build/reuse-20261001/`.
The explicit ordinary free-dagger pushout presentation in the separate remark
is still a later obligation. This paragraph records the private pre-integration
checkpoint. The final integration section below describes the subsequent local
build, 2,929-root audit and new registrations in `codex/part1-adjunction`.
The original frozen inputs are retained; the previously successful 112-root
Linux Comparator run applies to its old commit. A–D remain 0/4.

The fixed-object graph source map is also complete. It identifies the actual
fixed-`O`, identity-object-map category and exact Mathlib action/adjunction
inputs, followed by the checked external `TopPackage.modelCategory`
recognition constructor. The generator lifting-class equations, smallness,
and cell-complex weak-equivalence premises must still be proved. The map
itself is not a new theorem or model structure. Its eight
evidence entries and 35 providers were rechecked; metadata is archived under
`build/reuse-20261001/fixed-graph-reuse-map-20261004/`.

The ensuing private `bg.lem.gph-decomposition` construction is now checked.
It gives the full equivalence for the actual fixed-object graph category,
with upper-triangular simplicial sets and diagonal `BC₂` functors, retaining
the original arbitrary object type and all simplicial maps. The diagonal
nonidentity action is the original dagger. Both functors, natural unit/counit,
and both triangles are proved. Mathlib's action/functor-category equivalence,
product equivalences, and the existence of a chosen order on the same type
are reused. Seven strict modules, actual mixed imports, 54 retained contracts,
and a 244-root transitive axiom audit pass with only the three standard axioms;
both negative controls reject. Root source review, including the final eight
verification-only certificates, found no correspondence issue. The 78 author
evidence entries and 41 recorded provider entries were verified. Sources and
review metadata are archived under `fixed-graph-decomposition-author-20261004/`
and `fixed-graph-decomposition-root-review-20261004/` inside
`build/reuse-20261001/`. This proves the categorical decomposition privately;
it does not construct either graph or category model structures, and public
integration and Comparator registration remain pending.

The exact homwise detection step is also verified privately. The original
dagger commutation square gives an actual arrow isomorphism between the two
opposite hom maps; Mathlib's `MorphismProperty.arrow_mk_iso_iff` transports
the property. Its `RespectsIso` premise is discharged for actual horn Kan
fibrations and the actual geometric weak-equivalence class. The latter uses
the previously checked realization/singular-Kan formula, with no Kan premise
on the original hom spaces. The final statements use the same arbitrary
object type with a chosen order; no order or finiteness premise remains.
Seven exact checks, all printed type headers, mixed imports, and a 21-root
transitive audit pass, followed by separate source review. The 38 author
evidence entries and six review entries were verified and archived under
`fixed-graph-homwise-author-20261004/` and
`fixed-graph-homwise-correspondence-review-20261004/`. This does not yet supply
projective action model structures, generating cells, or the graph model structure.

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
The fourth joint pass obtained 94 compiled modules, seven direct compilation failures,
and 82 modules blocked by prerequisites. These are compilation counts, not a
percentage of the target theorem proved. The key comparison in `SSet/KeyLemma`
and the final `ModelCategorySSet` module remain uncompiled and unaudited.

That phase's six adapted modules reuse Mathlib's actual dimension classes,
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

The sixth joint pass had **112 compiled modules, six direct source/API
failures, and 65 modules blocked by prerequisites**, out of the same 183-module
target closure. All 112 successful modules import together with the actual
published `DaggerModels` environment. A fresh transitive axiom audit covers all
4,281 declarations owned by those external modules, including generated
declarations; only `propext`, `Classical.choice`, and `Quot.sound` occur.
This is stronger coverage than the earlier per-batch audits, but it still does
not cover the uncompiled target comparison theorems or model structure.

The combined source copy includes eight independently reviewed adaptations.
It reuses Mathlib's actual nondegenerate simplices, product-standard-simplex
equivalence and order homomorphism, and colimit/product dimension bounds.
The original full construction data and unrestricted signatures have explicit
checks. The old `SSet.IsFinite` product and pullback proofs remain unchanged;
they are not silently replaced by claims about the distinct `SSet.Finite` class.
Seven cached modules affected by changed prerequisites were discarded. The pass
retained only 99 artifacts with unchanged dependency closures and freshly
compiled 13 modules. The adapted `Quotient` source, although separately checked,
remains blocked in this combined pass by `IsFiniteCoproducts`.

At that checkpoint the six direct failures were `Skeleton`, `FundamentalGroupoid`,
`IsFiniteCoproducts`, `ConnectedComponents`, `FiniteInduction`, and
`NonemptyFiniteChains`.
The frozen pass, mixed-import result, complete successful-module axiom audit,
source/artifact hashes, and failure inventory are recorded under
`build/reuse-20261001/topcat-compatibility/phase6-joint/`. The external proofs
remain private compatibility experiments, not a published dependency.

The seventh joint pass, frozen on 2026-10-04, had **119 compiled modules,
six direct source/API failures, and 58 blocked modules** in the same original
183-module closure. All 119 successful modules import together with the actual
`DaggerModels` library. The six reviewed replacements preserve the original
statements and construction data. They also unblock the previously reviewed
`Quotient` source. All 112 baseline artifacts have unchanged full local source
dependency closures; the seven additional modules were compiled afresh.

Its complete successful-module audit covers **4,815 owned/generated
declarations**. All current names and owning modules were enumerated afresh.
The exact 4,281 baseline declarations retain their hash-bound per-declaration
audit because their artifacts and full dependency closures are unchanged;
the additional 534 declarations received fresh transitive axiom checks.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. A diagnostic module
with a foreign axiom was rejected by the new-owner audit path and its artifact
was removed before freezing the pass. This scratch check is separate from the
unchanged published Comparator checks below.

`Skeleton` reuses 15 canonical Mathlib declarations, with explicit old-type
contracts and full data comparisons. The original stage-specific `Unit`-indexed
relative cell complex is retained. `FundamentalGroupoid` retains the actual
relative-edge quotient, chosen composition and complete map functor. The four
finite/component modules retain the old `IsFinite` class and their component,
cofan, induction and chain data. Each of the three batches received an
independent agent review and fresh strict diagnostic replay; this is not human
review. Frozen records are under
`build/reuse-20261001/topcat-compatibility/phase7-{skeleton,fundamental,finite-components,joint}/`.

At that checkpoint the next six source failures were `AnodyneExtensionsAdjunctions`, `PtSimplex`,
`Presentable`, `Pseudofunctor`, `Pairing`, and `Subdivision`. Read-only source
comparison established the following bounded adaptation routes before editing:

- `AnodyneExtensionsAdjunctions` and `PtSimplex`: use the already checked
  `Subcomplex.liftFromPreimage` for the original preimage-equals-top contract,
  and canonical `Subcomplex.toRange`, `Subfunctor` components and `Fin.lt_def`.
  Preserve the existing relative morphisms, homotopies and pullback transport.
  Mathlib's same-named pointed-simplex constructions use a different relative
  morphism structure, so they are not direct type-preserving replacements.
- `Presentable`: the two stale names map to
  `Subfunctor.epi_iff_range_eq_top` and `Subfunctor.range_obj`. Mathlib already
  proves finite simplicial-set presentability, but its `Finite` class differs
  from the upstream `IsFinite`; applying that instance would require the
  explicit finite-dimension bridge. Keep the original nondegenerate coproduct,
  map and cofork, and retain the existing short proof when it checks.
- `Pseudofunctor`: package the same functors with `Functor.toCatHom` and the
  same natural isomorphisms with `Cat.Hom.isoMk`; extract underlying arrows
  with `.as.hom`. Transport all three existing coherence equalities through
  `Cat.Hom₂.ext`. Mathlib's `ModuleCat/Pseudofunctor.lean` supplies the exact
  constructor pattern; objectwise equivalences would not suffice.
- `Pairing` and `Subdivision`: use the same checked lift bridge, exact
  `Subfunctor` contracts and the existing nondegenerate-normal-form/membership
  lemmas. Keep the original pairing, ordinal/natural ranks, filtration,
  relative cell data, subdivision functors and natural transformations.
  Canonical pairing/rank definitions have changed and cannot be substituted
  without additional data bridges. These API and component-proof changes
  were subsequently compiled and independently reviewed in the eighth pass.

The eighth joint pass, frozen on 2026-10-04, has **128 compiled modules,
four direct source/API failures, and 51 blocked modules** in the original
183-module closure. This is about 70% of that dependency closure, not 70% of
Part I. All 128 successful modules import together with the actual
`DaggerModels` library. The six replacements above passed strict compilation,
full original-type/construction checks, and separate agent review with fresh
replays. The combined pass also compiled the unchanged `HomotopyGroup`,
`SmallObject`, and `CoconeNPrime` modules. All 119 baseline artifacts retain
unchanged full source dependency closures; nine modules were compiled afresh.

All **5,650 owned/generated roots** received a fresh transitive axiom audit.
The audit calls the original public Lean collector on every root with a shared
visited set, recording the complete root/owner list and the global axiom union.
It does not output a per-root axiom map. The only axioms are `propext`,
`Classical.choice`, and `Quot.sound`. Before adoption, the identical checker
matched the previous 4,815-root audit and rejected both an external foreign
axiom reached through a theorem and `sorryAx`. Those tests are reused by the
exact checker/collector hashes. The independent harness review also pins the
actual project sources/artifacts and import path before and after traversal.
Frozen evidence is under
`build/reuse-20261001/topcat-compatibility/phase8-{anodyne-pointed,presentable-pseudofunctor,pairing-subdivision,joint}/`
and `union-audit-validator/`. These are private compatibility experiments and
agent reviews, not a published dependency or independent human review.

The four failures first received the following read-only reuse mappings.
Their ninth-pass adaptations now pass bounded strict compilation and scoped
checks, followed by the combined downstream pass reported below:

- `Fibrations`: the pinned Mathlib `Subcomplex.isInitialBot` has an implicit
  ambient simplicial set. Pass `(X := A)` explicitly, preserving the original
  initial-object isomorphism and monomorphism proof.
- `HomotopySequence`: map the old subpresheaf inclusion/component names to
  `Subfunctor.ι`, `Subfunctor.ι_app`, and `Subfunctor.toFunctor_obj`, and use
  `Fin.lt_def`. The existing checked `Subcomplex.liftFromPreimage` bridge
  retains the original preimage-equals-top proofs and selected lift data;
  its full equality with the canonical lift is already proved. Keep the
  original connecting maps, fiber base point, homotopies, exactness statements,
  degree-zero cases, and all hypotheses. The source contains no explicit
  `sorry`; the failed build's `sorry` diagnostic follows earlier API errors.
- `FundamentalGroupoidAction`: use `Fin.lt_def` and `Fin.val_castSucc` for the
  three deprecated occurrences. Preserve the original action and coherence.
- `PairingSubdivision`: the pinned Lean `Fin.castSucc_lt_succ` has an implicit
  index, so specify `(i := j)`. Preserve the original pairing and rank proof.

The ninth joint pass, frozen on 2026-10-04, has **134 compiled modules,
five direct source/API failures, and 44 blocked modules** in the same
183-module closure, approximately 73% of this dependency compatibility task.
All 134 successful modules import with actual `DaggerModels`, and all
**6,200 owned/generated roots** received a fresh full transitive axiom-union
audit, with only the same three permitted standard axioms. All 128 prior
artifacts have unchanged dependency closures; six modules compiled afresh.
The four preceding failures are resolved. The two other newly compiled modules
are `KanComplexW` and `FundamentalGroupoidPiOne`.

Nineteen sources received reviewed compatibility edits. Of these, five compiled,
four revealed further API/elaboration failures, and ten remain blocked by
prerequisites; source adaptation alone is not verification. The new direct
failures are `HomotopySequenceAction`, `KanComplexWColimits`, `Homotopy`,
`KanComplexWRetracts`, and `SubdivisionAnodyneExtensions`. Frozen source-review,
compile, mixed-import and audit evidence is archived under
`build/reuse-20261001/topcat-compatibility/phase9-{source-review,joint}/`.

The actual `SSet.KeyLemma` comparison and `ModelCategorySSet` instance remain
blocked. This pass does not establish complete Kan–Quillen reuse or any of
the main theorem families A–D, and does not change published Comparator roots.

Before the tenth pass, source inspection establishes these further reuse routes:
`HomotopySequenceAction` and `Homotopy` must explicitly name the original
`KanComplex.FundamentalGroupoid.Edge`, whose relative-morphism data and endpoint
equations are already checked. The new Mathlib `SSet.Edge` shadows an opened
namespace at three sites; no replacement edge definition is needed.
For `KanComplexWColimits`, canonical `Subfunctor.range_ι` makes two other simp
arguments unused. The pinned `Types.isPullback_iff` provides its witnesses with
equations `t x₁ = x₂` and `l x₁ = x₃`; two proof lines must respect that
orientation, keeping the original `W_iff_naiveW` statement and witnesses.
These source correspondences precede the adaptations and their strict checks.
For `KanComplexWRetracts`, the same Kan-complex full subcategory now wraps its
homs in `InducedCategory.Hom`. Use canonical `ObjectProperty.homMk` on the
original two maps and four retract legs, and `ObjectProperty.hom_ext` on the
original square equations. Their underlying maps, composites and identities
are definitionally unchanged. The existing checked pseudofunctor evaluates
these wrapped maps via `.hom`, yielding the same actual fundamental-groupoid
equivalence predicate, with all four original fibrancy hypotheses retained.
For `SubdivisionAnodyneExtensions`, the checked upstream
`N.mapN_ι_simplex_mem_obj` proves the original last-vertex membership directly,
without destructing and reconstructing its dependent nondegeneracy proof.
Canonical `nerveMap` components and the existing `nerveNEquiv_apply` identify
the same last vertex with `ofN`; `mem_ofN_iff` gives exactly its simplex-image
membership. Apply these to the two horn-membership directions while retaining
the full arrow-isomorphism terms, backward witness, dimensions and hypotheses.
The bounded survey of the 44 blocked descendants also identifies eight exact
`Edge` qualifications across `FiberwiseHomotopy` and `MinimalFibrations`, plus
one receiver-style `S.lift` in `Loop`. The latter uses the original
preimage-equals-top proof, so pass `(B := S)` to the checked
`Subcomplex.liftFromPreimage` bridge, preserving the inner product lift and the
entire proof. Seven namespace-local `Edge` uses already resolve correctly and
are deliberately unchanged. These nine substitutions have source/provider
contracts and exact prospective byte hashes; compilation was checked separately
in the tenth combined pass below.

The tenth joint pass completes that gate: **158 compiled, two direct failures,
23 blocked**, in the original 183-module closure. All eight adapted sources
compile, along with sixteen unchanged downstream sources, including
`KanComplexKeyLemma`, `KanComplexWHomotopy`, `TopCat.W`, `FibrationSequence`,
and `MinimalFibrationsFactorization`. All 158 import with actual `DaggerModels`;
the fresh transitive global union over all **7,590 owned/generated roots** has
only the three permitted standard axioms. Evidence is frozen in
`build/reuse-20261001/topcat-compatibility/phase10-joint/`.
`SSet.KeyLemma` for arbitrary fibrations and `ModelCategorySSet` remain blocked;
the Kan-complex lemma alone does not supply these general targets.

Before further edits, the two new failure routes are confirmed directly in
providers: `CompleteLattice.MulticoequalizerDiagram.min_eq` is the deprecated
alias of the same `eq_inf` field, used twice in `BoundaryClosedEmbeddings`.
In `AffineMap`, the checked `S.le_iff_subcomplex` bridge restores the original
subcomplex-inclusion formulation of `S.le_iff`, preserving the following
`ofSection` and simplex-membership rewrites and the exact original witness.
Only these three names need changing in the eleventh proposed pass.

The eleventh joint pass verifies those changes: **163 compiled, three direct
failures, 17 blocked**, in the same 183-module closure. Five additional modules
compile, including `ModelCategoryTopCat` and
`SSet.CategoryWithWeakEquivalences`, which uses the actual geometric-realization
weak-equivalence class. All 163 import with actual `DaggerModels`; a fresh
transitive global union over **7,948 owned/generated roots** contains only the
three permitted standard axioms. All 389 frozen evidence entries were verified.
The report and metadata are archived under
`build/reuse-20261001/topcat-compatibility/phase11-joint/`; their source and
artifact paths refer to the frozen private compatibility root.
`SSet.KeyLemma` and `ModelCategorySSet` remain blocked. Thus 163/183 (about 89%)
measures this dependency compatibility pass only: main theorems A–D remain
0/4 complete, and this external dependency has not been published or integrated.

Before the twelfth pass, the three exposed failures were mapped to existing
providers. `ToTopDecomposition` can supply canonical
`Fin.succAbove_right_injective` to the same `Finset.sum_of_injOn` index map.
`Mesh` can replace the deprecated `Nat.lt_succ` with the identical statement
`Nat.lt_succ_iff`. `SdIso` can use the checked `S.le_iff_subcomplex` bridge to
retain its original subcomplex-inclusion proof and remove one redundant
simplification already performed by `by_contra!` using the canonical
`Finset.not_nonempty_iff_eq_empty` push rule. These are four proof-body changes;
the original theorem signatures, simplex data, and constructed isomorphisms
are retained.

The twelfth joint pass verifies all four edits and five further unchanged
downstream modules: **171 compiled, one direct failure, 11 blocked** in the
original closure. The new results include equalizer preservation by realization,
the subdivision comparison, local Serre fibration input, and factorization
through finite simplicial sets. All 171 modules import with `DaggerModels`, and
the fresh full transitive axiom union over **8,350 owned/generated roots** has
only the three permitted standard axioms. Frozen evidence and metadata are
recorded under `build/reuse-20261001/topcat-compatibility/phase12-joint/`.
The remaining direct blocker is `Convenient.SSet`, with full-subcategory
morphism packaging and hyperplane typeclass compatibility errors.
`SSet.KeyLemma` and `ModelCategorySSet` remain blocked, and A–D remain unproved.

The next mapped repair in `Convenient.SSet` uses
`ObjectProperty.homMk (toTop.map f)` for the same underlying realization map;
the inclusion functor recovers it by projection. Four radial-boundary proof
calls can explicitly name the original carrier `Hyperplane (n + 1)` before
typeclass synthesis. Their effect on the reported instance mismatch and
cascading errors is to be checked by strict compilation. A read-only downstream
map identifies the same full-subcategory packaging in `ToTopProducts` and
`SerreFibrationBundle`: retain the original product projections and product
lift, and the same open-subset inclusion, while using `homMk`, `.hom`, and
faithful-inclusion equality to express them in the current API. None of these
maps replaces a construction or adds a mathematical hypothesis.
The downstream `ToTopLocTrivial` map checks all sixteen raw `TopCat.ofHom`
expressions against their actual binders: each is used as a generated-space
morphism. Enclosing each whole expression in `ObjectProperty.homMk` retains
the continuous map, subtype-membership proofs, retractions, covering and
pullback data, and the surrounding composition and Over-category constructors.
No additional projections or speculative proof rewrites are included in this
map; any later elaboration failure must be checked separately.

The thirteenth joint pass verifies **175 compiled, one direct failure, seven
blocked**. `Convenient.SSet`, `Convenient.Fibrations`, `ToTopProducts`, and
`SerreFibrationBundle` now compile. All 175 modules import with `DaggerModels`;
the fresh full union for **8,508 owned/generated roots** contains only the
three standard permitted axioms. The original functor comparison and colimit
proofs passed unchanged; a fifth explicit Hyperplane carrier in the retraction
section proof also removed the final timeout at the default heartbeat limit.
The `ToTopLocTrivial` wrapper changes remain blocked, not checked, in this pass.
The next direct failure is an observed redundant `rfl` after `simp` already
closes the `fromPreimage` compatibility proof in `ToTopExact`; removing that
last tactic preserves the chosen pullback map and its original equation.
Metadata is archived under
`build/reuse-20261001/topcat-compatibility/phase13-joint/`.

The fourteenth pass verifies **178 compiled, one direct failure, four blocked**.
`ToTopExact`, the full `ToTopLocTrivial` source with its sixteen original-map
wrappers, and `TopCat.Homotopy` now compile. The actual mixed import succeeds;
the fresh full union over **8,610 owned/generated roots** contains only the
three permitted standard axioms. The remaining failure is a retract-mapping
API call in `SSet.ToTopFibration`. Canonical `RetractArrow.map F` is defined as
`Retract.map h F.mapArrow`; therefore the original `.map toTop.mapArrow` call
can use `.map toTop`, retaining the same underlying arrow-category retract,
its four legs, and both splitting equations. This replacement is mapped before
editing; the remaining general `KeyLemma` and `ModelCategorySSet` targets are
still unverified. Metadata is in
`build/reuse-20261001/topcat-compatibility/phase14-joint/`.

The fifteenth pass verifies **183 compiled, zero direct failures, zero blocked**.
The one reviewed `RetractArrow.map` API change unlocks `ToTopFibration`,
`FibrationSequenceAdj`, `KanComplexWUnit`, the general `KeyLemma`, and
`ModelCategorySSet`. Strict compilation, the actual all-module mixed import,
and a fresh full transitive axiom audit of **8,696 owned/generated roots** all
pass. The global union contains exactly the three permitted standard axioms;
this is not a per-root axiom map. All 406 frozen evidence entries were verified.
No external proof body has been adopted into the published companion, and no
Part I main theorem is newly claimed. The next mathematical integration check
must apply the exact arbitrary-object boundary-RLP/trivial-fibration theorem
to the companion's actual all-hom lifting characterization, retaining the
geometric-realization definition of weak equivalence. Metadata is in
`build/reuse-20261001/topcat-compatibility/phase15-joint/`.

A bounded external-source refresh on 2026-10-04 confirmed that the upstream
`master` still points to the same `6c0c356` commit; GitHub's repository license
metadata remains empty. The complete file tree of
[Tau Ceti at `c61a1cec`](https://github.com/TauCetiProject/TauCeti/tree/c61a1cec4d2112b701c802761bdbfb49a4026a26)
was also inspected, followed by its simplicial-set `TopAdj.lean` and
`Homotopy.lean`. Those two files provide singular-simplex naturality/range
lemmas and homotopies of pairs, not the required Kan–Quillen comparison.
That snapshot uses Lean `v4.35.0-rc3` and Mathlib `ec6a61ce`. In that Mathlib
snapshot, the inspected
[`CategoryWithFibrations.lean`](https://github.com/leanprover-community/mathlib4/blob/ec6a61cec0d8f9fda04453e9bb5761a79aa43a70/Mathlib/AlgebraicTopology/SimplicialSet/CategoryWithFibrations.lean)
still marks the full Quillen model structure as TODO while defining the
cofibration/fibration classes. This is a bounded tree/source survey, not proof
that no relevant theorem exists anywhere in those libraries. No newer package
was installed or substituted. Hash-bound source observations are saved under
`build/reuse-20261001/external-refresh-20261004/`.

**Decision:** prioritize a compatible pinned dependency or documented
compatibility adaptation before independently proving this standard theory.
Preserve attribution. Repository-level licensing was not established for the
inspected archive; no external proof bodies have been copied into the published
companion. Adoption must record the actual source and applicable terms.

The ninth-pass downstream inventory establishes 52 exact API substitutions in
15 further source files before applying them. The supplied token-aware map
distinguishes inclusion maps from their component lemmas and lift constructors
from their inclusion equations. Ten lift calls retain their original
`preimage = top` proofs and chosen morphisms through the checked
`Subcomplex.liftFromPreimage` bridge; all six associated inclusion-lemma uses
have corresponding bridge lemmas. Four equalizer references use the canonical
Mathlib `Subfunctor` definitions and the same full limiting fork. The remaining
changes use direct aliases or explicit arguments for the same initial object.
This is a source-contract review; in the joint pass one of these 15 modules
compiled, four failed at later elaboration/API steps, and ten remained blocked.
The map, provider hashes and individual lift-site review are recorded under
`build/reuse-20261001/topcat-compatibility/phase9-downstream-api-map/`.
The four phase-eight blockers passed bounded strict compilation, mixed imports
and scoped axiom audits before the successful 134-module joint import/audit.

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
The complete real Linux Comparator
[run 36868302980, attempt 2](https://github.com/Yonoha/dagger-models-lean/actions/runs/36868302980)
succeeded at companion commit `60c401897ce3cd56a6dff79531eb9b2efbb48452`.
Its actual job log confirms all 27 registered groups and 112 comparison roots,
including the four simplicial-colimit/rigidification roots, plus both the
weakened-statement and changed-definition negative controls. Group names were
checked against the current registry. The same commit's
[Lean CI run 36868302752](https://github.com/Yonoha/dagger-models-lean/actions/runs/36868302752)
also succeeded. The earlier 60-minute run was terminated by its job limit;
the successful run retains the same checks with a 90-minute job allowance.
These CI results cover the registered companion results, not the external
compatibility experiments or main theorems A–D. Independent human review is
not claimed.

The next opposite-comparison route was mapped before implementation using
19 pinned source/provider files. For `Jₙ = ULift (Fin (n.len + 1))`, lift
`Fin.rev` to `rₙ`. On Mathlib's original thickening paths, send a subset `I`
from `i` to `j` to the subset `rₙ '' I` from `rₙ j` to `rₙ i`; inclusion retains
its direction. Existing `nerveMap`, enriched opposite, and double-opposite
functors supply the remaining data for a candidate enriched reversal `ρₙ`.
The new obligations are its actual enriched identity/composition laws,
naturality for every simplex operator, and its full involutive coherence.
The bounded scratch implementation starts with these obligations. The source
map also states the subsequent restricted-Yoneda comparison, including the
outer `ULift`, arbitrary target functors, and the degree-zero enriched-data
condition; those statements are a plan, not proved results. No existing
complete comparison was located among the inspected providers. The exact map
is archived under `build/reuse-20261001/nerve-opposite-reuse-map-20261004/`.

The bounded thickening stage is now implemented and root-reviewed in scratch:
the actual reversed path image gives the full enriched reversal, both inverse
equations, every-simplex-operator naturality, the actual double-opposite
involution, and `rev ⋙ T ≅ T ⋙ O`. Strict compilation and the actual public
`DaggerModels` mixed import pass. The fresh scoped union covers all 49 owned
declarations (including private/generated helpers) and 21 diagnostic roots,
with only the three standard axioms. All 44 evidence entries, 19 provider
hashes and eight actual dependency artifact hashes were checked. The coherent
nerve comparison, its degree-zero enriched-data condition, and the subsequent
rigidification mate and dagger adjunction are separate obligations. This
checkpoint is not public adoption or completion of `dj.lem.lift`. Its source
and metadata are under
`build/reuse-20261001/thickening-reversal-author-20261004/`, with root review in
`build/reuse-20261001/thickening-reversal-root-review-20261004/`.

## Dagger adjunction integration (2026-10-04)

The preceding dated ordinary/thickening checkpoints are historical stages.
The actual reversal, nerve/opposite comparison, canonical vertex identifications,
rigidification mate, dagger left/right functors and their lifted adjunction have
now all passed local proof and correspondence checks. The original uncomposed
Yoneda-extension adjunction is retained, including its full Hom correspondence
in both directions and its unit and enriched counit.

The category-to-category free dagger adjunction reuses this companion's graph
free construction and semantic hom quotient, imposing the original identities
and compositions in every degree. It retains the original object type and the
identity object map of its unit. It is distinct from free composition on a graph.
No duplicate replacement of the already checked graph implementation was made.

| Existing declaration | Exact use | Remaining project-specific work |
| --- | --- | --- |
| `Adjunction.leftAdjointOfEquiv` and `Adjunction.adjunctionOfEquivLeft` | Build the ordinary free functor and adjunction from the full natural Hom equivalence | The doubled graph, semantic relation, actual lift/restriction and inverse laws |
| `CategoryTheory.mateEquiv` and `unit_mateEquiv_symm` | Transport the actual nerve/opposite comparison under the original adjunction | Original thickening reversal, both inverse laws, involution coherence and fixed vertices |
| `Adjunction.leftAdjointUniq` | Canonical natural isomorphism between the two actual composite left adjoints to the same right functor | The actual dagger lift and both actual free adjunctions |
| `Adjunction.unit_leftAdjointUniq_hom_app` and `Adjunction.leftAdjointUniq_hom_app_counit` | Full unit and counit compatibility of that comparison | No new uniqueness theorem required |

All conclusions of `dj.lem.lift` have passed local verification. The twelve
construction modules and the exact witness module are integrated in the isolated
`codex/part1-adjunction` checkout using the same Lean/Mathlib pins. The construction
modules change only standalone import prefixes; the witness is copied unchanged.
The frozen proof bodies are retained. The final 1,509-job build, 2,929-declaration
module-owned transitive axiom union, per-declaration metadata/axiom checks and
both invalid-proof controls pass. These local checks are distinct from real
Linux Comparator verification for this exact integration.

The exact problem definitions, original ordinary adjunction, full lift and
canonical comparison are now registered through self-contained Mathlib-only
specifications of 118 and 234 lines, following a separate agent source review.
The six registration negative mutations are rejected. All 27 prior groups and
112 ordered roots are retained, giving 29 groups, 114 unique roots and 115
comparisons, with only the existing colimits theorem checked in two contexts. The previously verified 27-group/112-root CI record above
continues to describe its exact old commit. No model structure or Quillen
property is claimed. The ordinary-category free pushout remark remains separate.
The private external Kan–Quillen source is not included in this public change.

## Other primary sources checked

- Pinned Mathlib's `ModelCategory.mk'`,
  `MorphismProperty.IsWeakFactorizationSystem.mk'`, and
  `MorphismProperty.llp_rlp_of_hasSmallObjectArgument` provide the general assembly
  machinery. No complete Hovey/Smith recognition or monadic/right-induced
  transfer theorem was located in that inspected tree. The manuscript's actual
  lifting-class equalities and cellular weak-equivalence inclusions remain
  inputs to establish, not assumptions to postulate.
- The private, fully audited Phase15 dependency provides an additional
  recognition route: `HomotopicalAlgebra.TopPackage.modelCategoryCat` and
  `TopPackage.modelCategory`. Its data require the actual small `I'`/`J'`,
  two-out-of-three and retract closure, `I'.rlp ≤ J'.rlp`, the exact
  `I'.rlp ↔ WeakEquivalence` criterion on `J'.rlp` maps, weak equivalences of
  sequential `J'` cell complexes, and coyoneda preservation for the specified
  generator sources along actual `I' ∨ J'` cell complexes. After those inputs,
  it constructs fibrations `J'.rlp` and cofibrations `I'.rlp.llp`. This can
  avoid a new general recognition proof; it does not discharge the specific
  graph/dagger cell and lifting inputs. The public external-adoption and
  licensing boundary is unchanged.
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
