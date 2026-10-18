import NativeRealEdgewiseHomotopyFixedPointComparison

/-! Apply the OLD realization and literal OLD EC2 mapping functor to ORIGINAL C2 actions. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalDaggerRealizationContinuousAction
open DaggerOriginalEC2HomotopyFixedPointFunctor DaggerOriginalEC2HomotopyFixedPointObject
open DaggerOriginalEC2MappingSingModelPreservation
open scoped TopCat.modelCategory SSet.modelCategoryQuillen DaggerOriginalBorelModelCategory
universe u
namespace DaggerNativeOriginalC2RealizationMapping
noncomputable section

/-- Realizing an original C2 action is jointly continuous for the OLD discrete group. -/
theorem realized_isContinuous (A : Action SSet.{u} C2.{u}) :
    ((SSet.toTop.mapAction C2.{u}).obj A).IsContinuous := by
  rw [Action.isContinuous_def]
  apply continuous_prod_of_discrete_left.mpr
  intro g
  exact (((SSet.toTop.mapAction C2.{u}).obj A).ρ g).asHom.hom.continuous

/-- The SAME native realization, lifted to the SAME continuous-action category. -/
def realizationFunctor : Action SSet.{u} C2.{u} ⥤ ContAction TopCat.{u} C2.{u} :=
  ObjectProperty.lift _ (SSet.toTop.mapAction C2.{u}) realized_isContinuous

theorem realization_map_hom {A B : Action SSet.{u} C2.{u}} (f : A ⟶ B) :
    (realizationFunctor.map f).hom.hom = SSet.toTop.map f.hom := rfl

/-- The OLD native realization criterion gives the exact OLD Borel weak class. -/
theorem realization_map_weak {A B : Action SSet.{u} C2.{u}} (f : A ⟶ B)
    [WeakEquivalence f.hom] : WeakEquivalence (realizationFunctor.map f).hom := by
  apply (DaggerOriginalBorelModelCategory.weakEquivalence_iff_underlying _).mpr
  change WeakEquivalence (SSet.toTop.map f.hom)
  exact (SSet.modelCategoryQuillen.weakEquivalence_iff f.hom).mp inferInstance

/-- Use the literal original compact-open equivariant EC2 mapping space and singular functor. -/
def mappingFunctor : Action SSet.{u} C2.{u} ⥤ SSet.{u} :=
  realizationFunctor ⋙ mappingSingFunctor

/-- No new replacement or homotopy-fixed-point functor is introduced. -/
theorem mapping_map_weak {A B : Action SSet.{u} C2.{u}} (f : A ⟶ B)
    [WeakEquivalence f.hom] : WeakEquivalence (mappingFunctor.map f) := by
  have : WeakEquivalence (realizationFunctor.map f).hom := realization_map_weak f
  exact mappingSing_map_weakEquivalence (realizationFunctor.map f)

instance mapping_kan (A : Action SSet.{u} C2.{u}) :
    SSet.KanComplex (mappingFunctor.obj A) :=
  mappingSing_kan (realizationFunctor.obj A)

/-- The edgewise endpoint is EXACTLY the previously fixed continuous realization. -/
theorem edgewise_realization_eq (X : DaggerSSet.{u}) :
    realizationFunctor.obj (DaggerNativeRealEdgewiseC2Action.action X) =
      DaggerNativeRealEdgewiseContinuousComparison.realizedEdgewiseContinuousFunctor.obj X := rfl

/-- The endpoint mapping object is EXACTLY the previously fixed point-set EC2 object. -/
theorem edgewise_mapping_eq (X : DaggerSSet.{u}) :
    mappingFunctor.obj (DaggerNativeRealEdgewiseC2Action.action X) =
      DaggerNativeRealEdgewiseHomotopyFixedPointComparison.edgewiseHomotopyFixedPointFunctor.obj
        X :=
  rfl

end
end DaggerNativeOriginalC2RealizationMapping
