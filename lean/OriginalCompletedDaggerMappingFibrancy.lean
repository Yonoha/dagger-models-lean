import OriginalStrictSimplicialGroupoidMappingKan
import OriginalCompletedDaggerMappingAction
import OriginalSimplicialActionModelCategory

/-! The actual completed dagger mapping action is projectively fibrant. -/

set_option autoImplicit false
open HomotopicalAlgebra DaggerModels
open DaggerOriginalCompletedDaggerMappingAction
open DaggerOriginalStrictSimplicialGroupoidMappingKan
open scoped SSet.modelCategoryQuillen DaggerOriginalSimplicialActionModelCategory
universe u

namespace DaggerOriginalCompletedDaggerMappingFibrancy

/-- The unchanged completion with its actual inverse-dagger action is projectively fibrant. -/
theorem completedMappingAction_fibrant (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) :
    IsFibrant (completedMappingAction C x y) :=
  (DaggerOriginalSimplicialActionModelCategory.isFibrant_iff_underlying _).2
    (completedHom_kan C.toSimplicialCat x y)

end DaggerOriginalCompletedDaggerMappingFibrancy
