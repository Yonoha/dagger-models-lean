import NativeThickeningFullPathHomotopy
import NativeThickeningFullSection
import NativeOriginalCotensorFunctor

/-! The full-path homotopy is an enriched functor into the SAME original cotensor. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial
open DaggerModels OrdinaryRigidification DaggerOriginalCotensorPrecompositionWeak
open DaggerOriginalFixedObjectCotensors DaggerOriginalFixedObjectStrictGroupoidCotensors
open DaggerOriginalFixedObjectCotensorRepresentation DaggerNativeThickeningFullPathHomotopy
universe u
namespace DaggerNativeThickeningCotensorContraction
noncomputable section

/-- The literal native interval homotopy, curried in the original parameter-first order. -/
def contractionFunctor (n : SimplexCategory) : cosimplicialThickening.obj n ⟶
    originalCotensor (Δ[1] : SSet.{u}) (cosimplicialThickening.obj n) where
  obj x := x
  map x y := curry ((β_ (Δ[1] : SSet.{u})
    ((cosimplicialThickening.obj n).enriched.Hom x y)).hom ≫ contraction x.as y.as)
  map_id x := by
    ext q p
    cases p
    apply Functor.HomObj.ext
    funext r a k
    change (contraction x.as x.as).app r
      (((cosimplicialThickening.obj n).enriched.Hom x x).map a
        (((cosimplicialThickening.obj n).enriched.id x).app q PUnit.unit), k) =
          (((cotensor (Δ[1] : SSet.{u})
            ⟨(cosimplicialThickening.obj n).enriched⟩).enriched.id x).app q
              PUnit.unit).app r a k
    rw [cotensor_point_id]
    have h := (congrFun (((cosimplicialThickening.obj n).enriched.id x).naturality a)
      PUnit.unit).symm
    change ((cosimplicialThickening.obj n).enriched.Hom x x).map a
      (((cosimplicialThickening.obj n).enriched.id x).app q PUnit.unit) =
        ((cosimplicialThickening.obj n).enriched.id x).app r PUnit.unit at h
    rw [h]
    exact contraction_id x.as r k
  map_comp x y z := by
    ext q p
    apply Functor.HomObj.ext
    funext r a k
    change (contraction x.as z.as).app r
      (((cosimplicialThickening.obj n).enriched.Hom x z).map a
        (((cosimplicialThickening.obj n).enriched.comp x y z).app q (p.1, p.2)), k) =
          (((cotensor (Δ[1] : SSet.{u})
            ⟨(cosimplicialThickening.obj n).enriched⟩).enriched.comp x y z).app q
              ((curry ((β_ (Δ[1] : SSet.{u})
                ((cosimplicialThickening.obj n).enriched.Hom x y)).hom ≫
                  contraction x.as y.as)).app q p.1,
                (curry ((β_ (Δ[1] : SSet.{u})
                  ((cosimplicialThickening.obj n).enriched.Hom y z)).hom ≫
                    contraction y.as z.as)).app q p.2)).app r a k
    rw [cotensor_point_comp]
    have h := (congrFun
      (((cosimplicialThickening.obj n).enriched.comp x y z).naturality a) (p.1, p.2)).symm
    change ((cosimplicialThickening.obj n).enriched.Hom x z).map a
      (((cosimplicialThickening.obj n).enriched.comp x y z).app q (p.1, p.2)) =
        ((cosimplicialThickening.obj n).enriched.comp x y z).app r
          (((cosimplicialThickening.obj n).enriched.Hom x y).map a p.1,
            ((cosimplicialThickening.obj n).enriched.Hom y z).map a p.2) at h
    rw [h]
    exact contraction_comp x.as y.as z.as r _ _ k

end
end DaggerNativeThickeningCotensorContraction
