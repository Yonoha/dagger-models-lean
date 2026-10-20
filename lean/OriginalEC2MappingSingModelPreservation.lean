import OriginalEC2MappingWeakEquivalencePreservation
import TopCatModelCategory.ModelCategorySSet

/-!
# Model classes of the literal original singular EC₂ mapping functors

The existing singular-model comparison converts the proved original
compact-open mapping preservation to the native simplicial model classes.
The same holds for the manuscript's exact compact-generated mapping functor.
The original actions, continuous equivariant arrows and singular maps remain
unchanged; no unitary-core restriction theorem is inferred here.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra
open scoped TopCat.modelCategory SSet.modelCategoryQuillen DaggerOriginalBorelModelCategory
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2HomotopyFixedPointFunctor
open DaggerOriginalEC2MappingFibrationPreservation
open DaggerOriginalEC2MappingWeakEquivalencePreservation DaggerOriginalEC2MappingCompactGeneration

universe u

namespace DaggerOriginalEC2MappingSingModelPreservation

noncomputable section

/-- The literal original singular equivariant mapping arrow preserves Borel fibrations. -/
theorem mappingSing_map_fibration {X Y : ContAction TopCat.{u} C2.{u}}
    (p : X ⟶ Y) [Fibration p.hom] : Fibration (mappingSingFunctor.map p) :=
  (TopCat.modelCategory.fibration_toSSet_map_iff _).2 (originalPostcompose_fibration p)

/-- The literal original singular equivariant mapping arrow preserves every Borel weak map. -/
theorem mappingSing_map_weakEquivalence {X Y : ContAction TopCat.{u} C2.{u}}
    (p : X ⟶ Y) [WeakEquivalence p.hom] : WeakEquivalence (mappingSingFunctor.map p) :=
  (TopCat.weakEquivalence_toSSet_map_iff _).2 (originalPostcompose_weakEquivalence p)

/-- The literal original singular mapping functor preserves Borel trivial fibrations. -/
theorem mappingSing_map_trivialFibration {X Y : ContAction TopCat.{u} C2.{u}}
    (p : X ⟶ Y) [Fibration p.hom] [WeakEquivalence p.hom] :
    trivialFibrations SSet.{u} (mappingSingFunctor.map p) :=
  (mem_trivialFibrations_iff _).2
    ⟨mappingSing_map_fibration p, mappingSing_map_weakEquivalence p⟩

/-- The exact compact-generated singular mapping arrow preserves Borel fibrations. -/
theorem compactMappingSing_map_fibration {X Y : ContAction TopCat.{u} C2.{u}}
    (p : X ⟶ Y) [Fibration p.hom] : Fibration (compactMappingSingFunctor.map p) :=
  (TopCat.modelCategory.fibration_toSSet_map_iff _).2 (compactPostcompose_fibration p)

/-- The exact compact-generated singular mapping arrow preserves every Borel weak map. -/
theorem compactMappingSing_map_weakEquivalence {X Y : ContAction TopCat.{u} C2.{u}}
    (p : X ⟶ Y) [WeakEquivalence p.hom] :
    WeakEquivalence (compactMappingSingFunctor.map p) :=
  (TopCat.weakEquivalence_toSSet_map_iff _).2 (compactPostcompose_weakEquivalence p)

/-- The exact compact-generated singular mapping functor preserves Borel trivial fibrations. -/
theorem compactMappingSing_map_trivialFibration {X Y : ContAction TopCat.{u} C2.{u}}
    (p : X ⟶ Y) [Fibration p.hom] [WeakEquivalence p.hom] :
    trivialFibrations SSet.{u} (compactMappingSingFunctor.map p) :=
  (mem_trivialFibrations_iff _).2
    ⟨compactMappingSing_map_fibration p, compactMappingSing_map_weakEquivalence p⟩

end

end DaggerOriginalEC2MappingSingModelPreservation
