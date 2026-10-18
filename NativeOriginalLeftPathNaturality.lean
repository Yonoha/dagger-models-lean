import NativeOriginalLeftMappingStrictPaths
import OriginalLeftMappingFunctoriality

/-! ALL original bipointed simplicial maps retain the coslice/path comparison. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial MonoidalCategory MonoidalClosed
open DaggerOriginalSimplexCoslice DaggerOriginalVertexCosliceContraction
open DaggerOriginalCosliceContractionOperators DaggerOriginalLeftMappingFunctoriality
open DaggerOriginalQuasicategoryLeftMappingSpace DaggerOriginalFullVertexSubcomplex
universe u
namespace DaggerNativeOriginalLeftPathNaturality
noncomputable section

theorem contraction_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    (cosliceMap f ⦋0⦌ x ⊗ₘ 𝟙 Δ[1]) ≫ contraction Y (f.app (op ⦋0⦌) x) =
      contraction X x ≫ cosliceMap f ⦋0⦌ x := by
  apply NatTrans.ext
  funext n st
  apply Subtype.ext
  exact (congrFun (f.naturality
    (contractionOperator n.unop (SSet.stdSimplex.objEquiv st.2)).op) st.1.val).symm

theorem coslice_comparison_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    cosliceMap f ⦋0⦌ x ≫
        DaggerNativeOriginalCoslicePathMap.comparison Y (f.app (op ⦋0⦌) x) =
      DaggerNativeOriginalCoslicePathMap.comparison X x ≫ (ihom Δ[1]).map f := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left,
    DaggerNativeOriginalCoslicePathMap.comparison, MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_natural_right,
    DaggerNativeOriginalCoslicePathMap.comparison, MonoidalClosed.uncurry_curry]
  apply NatTrans.ext
  funext n st
  change (cosliceProjection ⦋0⦌ Y (f.app (op ⦋0⦌) x)).app n
      ((contraction Y (f.app (op ⦋0⦌) x)).app n
        ((cosliceMap f ⦋0⦌ x).app n st.2, st.1)) = _
  have h := congrFun (NatTrans.congr_app (contraction_naturality f x) n) (st.2, st.1)
  change (contraction Y (f.app (op ⦋0⦌) x)).app n
      ((cosliceMap f ⦋0⦌ x).app n st.2, st.1) =
    (cosliceMap f ⦋0⦌ x).app n ((contraction X x).app n (st.2, st.1)) at h
  rw [h]
  exact congrFun (NatTrans.congr_app (cosliceMap_projection f ⦋0⦌ x) n)
    ((contraction X x).app n (st.2, st.1))

theorem comparison_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X _⦋0⦌) :
    leftMappingMap f x y ≫
        DaggerNativeOriginalLeftMappingStrictPaths.comparison Y
          (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) =
      DaggerNativeOriginalLeftMappingStrictPaths.comparison X x y ≫ strictPathFiberMap f x y := by
  apply (cancel_mono (strictPathFiber Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)).ι).mp
  rw [Category.assoc, DaggerNativeOriginalLeftMappingStrictPaths.comparison_ι,
    ← Category.assoc, leftMappingMap_ι, Category.assoc, coslice_comparison_naturality]
  dsimp only [strictPathFiberMap]
  rw [Category.assoc, SSet.Subcomplex.lift_ι]
  simp only [← Category.assoc, DaggerNativeOriginalLeftMappingStrictPaths.comparison_ι]

end
end DaggerNativeOriginalLeftPathNaturality
