import NativeAmbientDaggerFibrancy
import ActualOriginalBipointedRCoreZigzag
import OriginalStrictSimplicialGroupoidMappingKan

/-! The completed WHOLE original core, then restricted to the SAME original endpoints,
is native fibrant in the ORIGINAL ambient fixed-object model, with no extra hypothesis.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerActualDaggerOrdinaryCore DaggerActualOriginalBipointedRCoreZigzag
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerActualOriginalCoreCompletionFibrancy
noncomputable section

theorem target_fibrant (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    IsFibrant (DaggerActualDaggerCoreEndpointRestriction.target X x y) := by
  apply (DaggerNativeAmbientDaggerFibrancy.fibrant_iff_homs _).mpr
  intro i j
  exact DaggerOriginalStrictSimplicialGroupoidMappingKan.completedHom_kan
    (DaggerRigidification.obj (coreDagger X)).toSimplicialCat
    (coreLabels X x y i) (coreLabels X x y j)

end
end DaggerActualOriginalCoreCompletionFibrancy
