import NativeRealEdgewiseStandardSimplexNerve
import NativeOrderTopNerveWeakContractibility
import NativeStandardSimplexContraction

/-! Native weak contractibility of the actual edgewise standard simplex and target projection. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial
open DaggerSSetGluing DaggerOriginalProductGadget DaggerNativeRealEdgewiseSSet
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeRealEdgewiseStandardSimplexWeak
noncomputable section

theorem point_GW (n : ℕ) : GW (pointMap (edgewise.obj (Δ[n] : SSet.{u}))) := by
  let e := DaggerNativeRealEdgewiseStandardSimplexNerve.simplexIso.{u} n
  have : WeakEquivalence (pointMap (nerve
      (ULift.{u} (DaggerNativeRealEdgewiseIntervalChains.Interval n)))) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerNativeOrderTopNerveWeakContractibility.point_GW _)
  have he : e.hom ≫ pointMap _ = pointMap (edgewise.obj (Δ[n] : SSet.{u})) :=
    pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

theorem targetProjection_GW (n : ℕ) : GW (targetProjection (Δ[n] : SSet.{u})) := by
  let e := SSet.stdSimplex.isoNerve.{u} n
  have : WeakEquivalence (pointMap (nerve (ULift.{u} (Fin (n + 1))))) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerNativeOrderTopNerveWeakContractibility.point_GW _)
  have he : e.hom ≫ pointMap _ = pointMap (Δ[n] : SSet.{u}) :=
    pointIsTerminal.hom_ext _ _
  have : WeakEquivalence (pointMap (Δ[n] : SSet.{u})) := by
    rw [← he]
    infer_instance
  have : WeakEquivalence (pointMap (edgewise.obj (Δ[n] : SSet.{u}))) :=
    (weakEquivalence_iff_GW _).mpr (point_GW n)
  apply (weakEquivalence_iff_GW _).mp
  exact weakEquivalence_of_postcomp_of_fac
    (show targetProjection (Δ[n] : SSet.{u}) ≫ pointMap _ =
      pointMap (edgewise.obj (Δ[n] : SSet.{u})) from pointIsTerminal.hom_ext _ _)

end
end DaggerNativeRealEdgewiseStandardSimplexWeak
