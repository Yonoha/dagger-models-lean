import OriginalEC2GeneratorLifting
import OriginalEC2MappingCompactGeneration

/-!
# Native model-class recognition for the literal original EC₂ mapping arrow

The actual TopCat generating right-lifting classes give exact recognition of
fibrations and trivial fibrations of original postcomposition. The earlier
compact-generation comparison transports the same recognition to the manuscript's
compact-generated mapping arrow. This does not assert product cofibrations or
preservation of input Borel weak equivalences.
-/

set_option autoImplicit false

open CategoryTheory Topology HomotopicalAlgebra DaggerModels
open scoped TopCat.modelCategory
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2HomotopyFixedPointFunctor
open DaggerOriginalEC2CompactParameterHomEquiv DaggerOriginalEC2GeneratorLifting
open DaggerOriginalEC2MappingCompactGeneration

universe u

namespace DaggerOriginalEC2MappingFibrationRecognition

/-- Native fibration of original postcomposition is exact lifting against the original horn
products. -/
theorem originalPostcompose_fibration_iff {X Y : ContAction TopCat.{u} C2.{u}}
    (p : X ⟶ Y) :
    Fibration (postcompose p) ↔ ∀ (n : ℕ) (i : Fin (n + 2)),
      HasLiftingProperty (originalEC2TensorMap (SSet.toTop.map (SSet.horn (n + 1) i).ι))
        p.hom := by
  rw [fibration_iff]
  exact originalPostcompose_horn_rlp_iff p

/-- Original postcomposition is a trivial fibration precisely when the original boundary
products lift. -/
theorem originalPostcompose_trivialFibration_iff {X Y : ContAction TopCat.{u} C2.{u}}
    (p : X ⟶ Y) :
    (Fibration (postcompose p) ∧ WeakEquivalence (postcompose p)) ↔
      ∀ n, HasLiftingProperty (originalEC2TensorMap (SSet.toTop.map (SSet.boundary n).ι))
        p.hom := by
  have h : TopCat.modelCategory.I.rlp = trivialFibrations TopCat.{u} :=
    TopCat.modelCategory.packageTopCat.I_rlp_eq_trivialFibrations
  rw [← mem_trivialFibrations_iff, ← h]
  exact originalPostcompose_boundary_rlp_iff p

/-- The manuscript's compact-generated mapping fibration has the identical original horn
criterion. -/
theorem compactPostcompose_fibration_iff {X Y : ContAction TopCat.{u} C2.{u}}
    (p : X ⟶ Y) :
    Fibration (compactMappingTopFunctor.map p) ↔ ∀ (n : ℕ) (i : Fin (n + 2)),
      HasLiftingProperty (originalEC2TensorMap (SSet.toTop.map (SSet.horn (n + 1) i).ι))
        p.hom := by
  rw [compact_postcompose_fibration_iff]
  exact originalPostcompose_fibration_iff p

/-- Compact generation retains the exact original boundary criterion for trivial fibrations. -/
theorem compactPostcompose_trivialFibration_iff {X Y : ContAction TopCat.{u} C2.{u}}
    (p : X ⟶ Y) :
    (Fibration (compactMappingTopFunctor.map p) ∧
      WeakEquivalence (compactMappingTopFunctor.map p)) ↔
      ∀ n, HasLiftingProperty (originalEC2TensorMap (SSet.toTop.map (SSet.boundary n).ι))
        p.hom := by
  rw [compact_postcompose_fibration_iff, compact_postcompose_weakEquivalence_iff]
  exact originalPostcompose_trivialFibration_iff p

end DaggerOriginalEC2MappingFibrationRecognition
