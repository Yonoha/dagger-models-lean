import NativeFixedDaggerPartFactor
import NativeAmbientDaggerMappingTargetLifting
import OriginalFixedObjectDaggerSimplicialEnrichment

/-! The SAME original all-isomorphism part inclusion and actual enriched postcomposition.
The inclusion is always a native fibration; the actual mapping arrow is a fibration
for every native cofibrant source, and is a monomorphism on the WHOLE mapping simplicial set.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectDaggerCategories DaggerNativeFixedDaggerIsomorphismPart
open DaggerOriginalFixedObjectDaggerDegreeCategories DaggerOriginalFixedObjectDegreeCategories
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerNativeFixedDaggerPartMappingFibrationMono
noncomputable section

theorem inclusion_fibration {O : Type u} (D : FixedDaggerCategory O) :
    Fibration (inclusion D) := by
  rw [DaggerOriginalFixedObjectAmbientDaggerModel.fibration_iff_original]
  intro i j
  exact DaggerActualIsomorphismPartLocalWeakInvariance.inclusion_fibration
    (originalDagger D).toSimplicialCat i j

theorem inclusion_mono {O : Type u} (D : FixedDaggerCategory O) : Mono (inclusion D) := by
  constructor
  intro H F G h
  exact DaggerNativeFixedDaggerPartFactor.inclusion_cancel F G h

theorem mapping_fibration {O : Type u} (A D : FixedDaggerCategory O) [IsCofibrant A] :
    Fibration (eHomWhiskerLeft SSet A (inclusion D)) := by
  have := inclusion_fibration D
  exact DaggerNativeAmbientDaggerMappingTargetLifting.mappingTarget_fibration A (inclusion D)

theorem mapping_mono {O : Type u} (A D : FixedDaggerCategory O) :
    Mono (eHomWhiskerLeft SSet A (inclusion D)) := by
  constructor
  intro K F G h
  apply NatTrans.ext
  funext q k
  apply Functor.HomObj.ext
  funext r α
  apply degreeDaggerHom_ext
  apply degreeHom_ext
  intro i j s
  apply Subtype.ext
  exact congrArg (fun t : (A ⟶[SSet.{u}] D).obj q ↦
    ((t.app r α).underlying.map i j) s) (congrFun (NatTrans.congr_app h q) k)

end
end DaggerNativeFixedDaggerPartMappingFibrationMono
