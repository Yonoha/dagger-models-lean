import NativeIhomParameterDiagonal

/-! The graph evaluation is an enriched functor on the SAME original cotensors. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial DaggerModels
open DaggerOriginalCotensorPrecompositionWeak DaggerOriginalFixedObjectCotensors
open DaggerOriginalFixedObjectStrictGroupoidCotensors DaggerNativeIhomParameterDiagonal
universe u
namespace DaggerNativeCotensorParameterDiagonal
noncomputable section

/-- Evaluate the two parameter slots at (theta(k),k), retaining all original objects. -/
def evaluationAlong {I K : SSet.{u}} (theta : K ⟶ I) (C : SimplicialCat.{u, u}) :
    originalCotensor I (originalCotensor K C) ⟶ originalCotensor K C where
  obj x := x
  map x y := diagonalHom theta (C.enriched.Hom x y)
  map_id x := by
    ext q p
    cases p
    apply Functor.HomObj.ext
    funext r a k
    change ((((cotensor I (cotensor K ⟨C.enriched⟩)).enriched.id x).app q
      PUnit.unit).app r a (theta.app r k)).app r (𝟙 r) k =
        (((cotensor K ⟨C.enriched⟩).enriched.id x).app q PUnit.unit).app r a k
    simp only [cotensor_point_id]
  map_comp x y z := by
    ext q p
    apply Functor.HomObj.ext
    funext r a k
    change ((((cotensor I (cotensor K ⟨C.enriched⟩)).enriched.comp x y z).app q
      (p.1, p.2)).app r a (theta.app r k)).app r (𝟙 r) k =
        (((cotensor K ⟨C.enriched⟩).enriched.comp x y z).app q
          ((diagonalHom theta (C.enriched.Hom x y)).app q p.1,
            (diagonalHom theta (C.enriched.Hom y z)).app q p.2)).app r a k
    simp only [cotensor_point_comp]
    rfl

end
end DaggerNativeCotensorParameterDiagonal
