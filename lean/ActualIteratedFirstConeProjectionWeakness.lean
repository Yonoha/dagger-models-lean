import NativeDualTheoremASmallTarget
import ActualIteratedConeFibreComparison

/-! The actual first projection is weak from its original structured comma categories. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerActualIteratedRightConeIndex DaggerOriginalProductGadget DaggerSSetGluing
universe u
namespace DaggerActualIteratedFirstConeProjectionWeakness
noncomputable section

/-- The same original first projection with only its target hom universe raised. -/
theorem first_projection_lifted_GW (D : SimplicialCat.{u, u})
    (hD : ∀ x y : D.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    GW (nerveMap (toCones D a b ⋙ ULiftHom.up.{0, u, u})) :=
  DaggerNativeDualTheoremASmallTarget.lifted_nerveMap_GW (toCones D a b)
    (DaggerActualIteratedConeFibreComparison.first_projection_under_point_GW D hD a b)

/-- The whole original chain map of the actual first projection is geometrically weak. -/
theorem first_projection_GW (D : SimplicialCat.{u, u})
    (hD : ∀ x y : D.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    GW (DaggerNativeSmallHomNerveLift.mixedMap (toCones D a b)) :=
  DaggerNativeDualTheoremASmallTarget.mixedMap_GW (toCones D a b)
    (DaggerActualIteratedConeFibreComparison.first_projection_under_point_GW D hD a b)

end
end DaggerActualIteratedFirstConeProjectionWeakness
