import ActualRigidificationComponentHoComparison
import NativeKanHomotopyCategoryGroupoid

/-! The original rigidification of every Kan complex has weak original completion Homs. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerActualRigidificationComponentHoComparison
open DaggerNativeKanHomotopyCategoryGroupoid
open DaggerOriginalAmbientDaggerPiZeroGroupoid DaggerOriginalSimplicialGroupoidCompletion
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualKanRigidificationCompletionWeak
noncomputable section

theorem component_groupoid (K : SSet.{u}) [K.KanComplex] :
    HasActualComponentGroupoid (rigidification.obj K) :=
  component_groupoid_of_ho_isIso K (fun f ↦ ho_isIso K f)

theorem localizationHom_weak (K : SSet.{u}) [K.KanComplex]
    (x y : (rigidification.obj K).Obj) :
    WeakEquivalence (localizationHom (rigidification.obj K) x y) :=
  DaggerActualOrdinaryRigidificationLocalization.localizationHom_weak K (component_groupoid K) x y

end
end DaggerActualKanRigidificationCompletionWeak
