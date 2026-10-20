import NativeSimpleSphereFreeClasses
import NativePiEvaluationFibreNaturality

/-! The actual free sphere component underlying a based class is natural in every Kan target. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra Simplicial
open DaggerNativeSimpleSphereFreeClasses DaggerNativePiEvaluationFibreNaturality
open DaggerNativePiEvaluationFibreComponents DaggerNativeUnitalMultiplicationAction
open DaggerOriginalFixedObjectCotensorPoints SSet.KanComplex
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeFreeSphereFibreNaturality
noncomputable section

theorem freeSphereFibre_natural_val (n : ℕ) (i : Fin (n + 2))
    (a : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) i : SSet.{u}))
    {X Y : SSet.{u}} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) (x : X _⦋0⦌)
    (hX : TrivialActionAt X x) (hY : TrivialActionAt Y (f.app _ x)) (s : π n X x) :
    SSet.mapπ₀ ((ihom (SSet.boundary (n + 1) : SSet.{u})).map f)
        (piFreeSphereFibreEquiv n i a X x hX s).val =
      (piFreeSphereFibreEquiv n i a Y (f.app _ x) hY (mapπ f n x _ rfl s)).val := by
  rw [piFreeSphereFibreEquiv_val, piFreeSphereFibreEquiv_val]
  calc
    _ = SSet.mapπ₀ (SSet.Subcomplex.fiber
        (pointEvaluation (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) Y)
          (f.app _ x)).ι
        (SSet.mapπ₀ (evaluationFibreMap
          (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) f x)
          (piEvaluationFibreEquiv n i a X x s)) := by
      rw [← SSet.mapπ₀_comp_apply, ← SSet.mapπ₀_comp_apply,
        evaluationFibreMap, SSet.Subcomplex.mapFiber_ι]
    _ = _ := by rw [piEvaluationFibreEquiv_natural]

end
end DaggerNativeFreeSphereFibreNaturality
