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
  `DaggerSSet.forget` at every universe. Its identification with the explicit
  pushout $A \amalg_{\operatorname{sk}_0 A} A^{\mathrm{op}}$ remains to prove.
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

`formalization.yaml` and `CORRESPONDENCE.md` specify the exact checked scope.

## A — dagger Bergner model structure

Targets: `bg.thm.main` (line 1117), `bg.thm.left-proper` (line 1141).

Required chain:

1. Dagger simplicial categories (`bg.def.dagger-scat`), dagger graphs,
   free categories, limits/colimits, and local presentability.
2. Fixed-object model structures (`gb.cor.sGph-model`, `bg.thm.fixed-object`).
3. Natural unitary intervals, their extraction and realization, and coherent
   unitary equivalences (`bg.def.interval`, `bg.prop.cu-groupoid`).
4. The exact classes `W†`, `I†`, `J†` (`bg.def.W`, `bg.def.IJ`), two-out-of-three,
   cell and lifting results, and the recognition theorem's hypotheses.
5. The actual model structure, specified generating sets, characterization of
   trivial fibrations, combinatoriality, and left properness.

Pinned mathlib supplies enriched categories/functors, a general `ModelCategory`
class, weak factorization systems, and small object machinery. It does not
supply the ordinary Bergner model structure needed here. A degree-zero dagger
category does not replace a dagger simplicial category.

## B — dagger Joyal structure and rigidification equivalence

Targets: `dj.thm.main` (line 1810), `dj.thm.equivalence` (line 1848).

Required chain:

1. The presheaf equivalence, local presentability, and free–forgetful adjunction
   (implemented above); the explicit pushout description of free dagger
   completion (`dj.not.adjunctions`) remains to prove.
2. Ordinary rigidification and coherent nerve, compatibility with opposites,
   and the concrete lifted adjunction (`dj.lem.lift`).
3. Cellular characterization of free cofibrations (`dj.lem.free-cof`),
   preservation by rigidification, and accessibility of weak equivalences.
4. The recognition theorem with `W = C†⁻¹(W†)` and the exact `FreeCofibration`
   class, followed by the fibrant counit and Quillen-equivalence criterion.

The `FreeCofibration` class requires freeness of new nondegenerate simplices
only in positive degrees. Replacing it by all monomorphisms would change B.
Mathlib has the coherent nerve's definition but not the required ordinary
Joyal–Bergner adjunction/equivalence. Relative skeletons and their successor
formula are available; the boundary-cell pushout decomposition still needs
proof at the pinned revision.

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
