import OriginalEC2MappingSingModelPreservation

/-!
# Original dagger homotopy fixed points preserve underlying weak equivalences

The native realization criterion first gives a weak equivalence of the literal
underlying realized map. The proved original Borel model criterion supplies the
actual equivariant action weak equivalence. The proved original EC₂ singular
mapping preservation then applies to the existing dagger homotopy fixed point
functor. All input maps and actions are retained in every universe.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels HomotopicalAlgebra
open DaggerOriginalDaggerRealizationContinuousAction DaggerOriginalEC2HomotopyFixedPointFunctor
open DaggerOriginalEC2MappingSingModelPreservation
open scoped TopCat.modelCategory SSet.modelCategoryQuillen DaggerOriginalBorelModelCategory

universe u

namespace DaggerOriginalDaggerHomotopyFixedPointWeakEquivalences

noncomputable section

/-- The original realized continuous action map is Borel weak for an underlying weak map. -/
theorem realizedContinuousAction_map_weakEquivalence {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    [WeakEquivalence f.hom] : WeakEquivalence (realizedContinuousActionFunctor.map f).hom := by
  apply (DaggerOriginalBorelModelCategory.weakEquivalence_iff_underlying _).2
  change WeakEquivalence (SSet.toTop.map f.hom)
  exact (SSet.modelCategoryQuillen.weakEquivalence_iff f.hom).1 inferInstance

/-- The original dagger homotopy fixed point map preserves an underlying simplicial weak map. -/
theorem daggerHomotopyFixedPoint_map_weakEquivalence {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    [WeakEquivalence f.hom] : WeakEquivalence (daggerHomotopyFixedPointFunctor.map f) := by
  have : WeakEquivalence (realizedContinuousActionFunctor.map f).hom :=
    realizedContinuousAction_map_weakEquivalence f
  exact mappingSing_map_weakEquivalence (realizedContinuousActionFunctor.map f)

end

end DaggerOriginalDaggerHomotopyFixedPointWeakEquivalences
