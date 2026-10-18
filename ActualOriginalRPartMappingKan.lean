import NativeAmbientDaggerMappingKan
import ActualOriginalFixedRCoreZigzag

/-! The EXACT original R groupoidal part is natively fibrant, and the WHOLE original
enriched mapping space from EVERY cofibrant source is Kan and source weak-invariant.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels DaggerUnitaryInvariance OrdinaryRigidification
open DaggerOriginalFixedObjectDaggerCategories DaggerActualOriginalFixedRCoreZigzag
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerActualOriginalRPartMappingKan
noncomputable section

theorem replacedPart_fibrant (R : FunctorialFibrantReplacement.{u}) (X : DaggerSSet.{u})
    (b : DaggerUnitaryInterval.Vertex.{u} → (DaggerRigidification.obj X).Obj) :
    IsFibrant (replacedPart R X b) := by
  have := original_R_target_fibrant R X b
  exact DaggerNativeAmbientDaggerFibrancy.part_fibrant _

theorem mapping_kan (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u})
    [IsCofibrant A] (R : FunctorialFibrantReplacement.{u}) (X : DaggerSSet.{u})
    (b : DaggerUnitaryInterval.Vertex.{u} → (DaggerRigidification.obj X).Obj) :
    (A ⟶[SSet.{u}] replacedPart R X b).KanComplex := by
  have := replacedPart_fibrant R X b
  exact DaggerNativeAmbientDaggerMappingKan.mapping_kan A _

theorem mappingSource_weak {A B : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}}
    (i : A ⟶ B) [IsCofibrant A] [IsCofibrant B] [WeakEquivalence i]
    (R : FunctorialFibrantReplacement.{u}) (X : DaggerSSet.{u})
    (b : DaggerUnitaryInterval.Vertex.{u} → (DaggerRigidification.obj X).Obj) :
    WeakEquivalence (eHomWhiskerRight SSet i (replacedPart R X b)) := by
  have := replacedPart_fibrant R X b
  exact DaggerNativeAmbientDaggerMappingSourceInvariance.mappingSource_weak i _

end
end DaggerActualOriginalRPartMappingKan
