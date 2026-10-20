import OriginalCounitRightConeQRealizationBoundaryReconciled
import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# Cofibration preservation for realization of the original Q

The boundary calculation and the native simplicial-set model category transfer
boundary lifting through the actual realization-singular adjunction. The native
boundary generators detect trivial fibrations, so singular preserves trivial
fibrations and realization preserves every cofibration. This does not assert
preservation of trivial cofibrations or the original rigidification counit.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerOriginalCounitRightConeQRealizationBoundary

universe u

namespace DaggerOriginalCounitRightConeQRealizationCofibrations

noncomputable section

/-- Trivial fibrations lift against every actual realized boundary inclusion. -/
theorem realization_boundary_lifting {X Y : SSet.{u}} (p : X ⟶ Y)
    [Fibration p] [WeakEquivalence p] (n : ℕ) :
    HasLiftingProperty (realization.{u}.map (∂Δ[n]).ι) p := by
  have := realization_boundary_cofibration.{u} n
  infer_instance

/-- Transfer these exact boundary lifting problems through the actual Q adjunction. -/
theorem singular_boundary_lifting {X Y : SSet.{u}} (p : X ⟶ Y)
    [Fibration p] [WeakEquivalence p] (n : ℕ) :
    HasLiftingProperty (SSet.boundary.{u} n).ι (singular.{u}.map p) :=
  (realizationSingularAdjunction.{u}.hasLiftingProperty_iff (∂Δ[n]).ι p).mp
    (realization_boundary_lifting p n)

/-- The native boundary generators show that singular sends trivial fibrations to such. -/
theorem singular_trivialFibration {X Y : SSet.{u}} (p : X ⟶ Y)
    [Fibration p] [WeakEquivalence p] :
    trivialFibrations SSet.{u} (singular.{u}.map p) := by
  rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
  intro A B i hi
  change MorphismProperty.ofHoms (fun n : ℕ ↦ (SSet.boundary.{u} n).ι) i at hi
  cases hi with
  | mk n => exact singular_boundary_lifting p n

/-- Register the verified preservation property with the native model-category API. -/
instance singular_preservesTrivialFibrations : singular.{u}.PreservesTrivialFibrations where
  trivialFibrations_le := by
    intro X Y p hp
    rw [mem_trivialFibrations_iff] at hp
    have : Fibration p := hp.1
    have : WeakEquivalence p := hp.2
    exact singular_trivialFibration p

/-- The same actual left adjoint preserves all cofibrations, by Mathlib's adjunction theorem. -/
instance realization_preservesCofibrations : realization.{u}.PreservesCofibrations :=
  realizationSingularAdjunction.{u}.preservesTrivialFibrations_iff_preservesCofibrations.mp
    inferInstance

/-- Cofibration preservation holds for arbitrary simplicial sets and arbitrary universe. -/
theorem realization_cofibration {X Y : SSet.{u}} (i : X ⟶ Y) [Cofibration i] :
    Cofibration (realization.{u}.map i) := inferInstance

end

end DaggerOriginalCounitRightConeQRealizationCofibrations
