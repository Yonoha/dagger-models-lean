import NativeGeometricPointEvaluation
import NativeMappingEvaluationRealizationUnit
import NativeGeometricSphereClassFunctor

/-! Free geometric sphere evaluation retains its actual formula on every full row diagram. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Simplicial HomotopicalAlgebra
open DaggerNativeGeometricPointEvaluation DaggerNativeMappingEvaluationRealizationUnit
open DaggerNativeGeometricSphereClassFunctor
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeGeometricSphereRowEvaluation
noncomputable section

def geometricRowEvaluation (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ)
    (v : (SSet.boundary (n + 1) : SSet.{u}) _⦋0⦌) :
    (F ⋙ sphereClassFunctor n : SSet.{u}) ⟶
      (F ⋙ (SSet.toTop ⋙ TopCat.toSSet) ⋙ SSet.π₀Functor : SSet.{u}) :=
  (Functor.isoWhiskerLeft F (sphereClassesNatIso n)).hom ≫
    rowEvaluation (F ⋙ (SSet.toTop ⋙ TopCat.toSSet)) (SSet.const v)

theorem geometricRowEvaluation_mk (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ)
    (v : (SSet.boundary (n + 1) : SSet.{u}) _⦋0⦌) (k : SimplexCategoryᵒᵖ)
    (f : C(↑(TopCat.sphere n), ↑(SSet.toTop.obj (F.obj k)))) :
    (geometricRowEvaluation F n v).app k (Quot.mk ContinuousMap.Homotopic f) =
      SSet.π₀.mk (TopCat.toSSetObj₀Equiv.symm
        (f (DaggerCountableSphereQuotient.toSphere n
          (realizedVertex (SSet.boundary (n + 1) : SSet.{u}) v)))) :=
  sphereEvaluation_mk n (F.obj k) v f

def geometricEvaluationArrowIso (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ)
    (v : (SSet.boundary (n + 1) : SSet.{u}) _⦋0⦌) :
    Arrow.mk (geometricRowEvaluation F n v) ≅
      Arrow.mk (rowEvaluation (F ⋙ (SSet.toTop ⋙ TopCat.toSSet)) (SSet.const v)) :=
  Arrow.isoMk (Functor.isoWhiskerLeft F (sphereClassesNatIso n)) (Iso.refl _)
    (by
      change _ = geometricRowEvaluation F n v ≫ 𝟙 _
      rw [Category.comp_id]
      rfl)

theorem geometric_row_evaluation_fibration (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    [∀ k, IsFibrant (F.obj k)] (n : ℕ)
    (v : (SSet.boundary (n + 1) : SSet.{u}) _⦋0⦌)
    [Fibration (C := SSet.{u}) (rowEvaluation F (SSet.const v))] :
    Fibration (C := SSet.{u}) (geometricRowEvaluation F n v) := by
  have hp := realized_evaluation_fibration F (SSet.const v)
  exact (HomotopicalAlgebra.fibration_iff (C := SSet.{u}) _).mpr
    (((fibrations SSet.{u}).arrow_mk_iso_iff (geometricEvaluationArrowIso F n v)).mpr
      ((HomotopicalAlgebra.fibration_iff (C := SSet.{u}) _).mp hp))

end
end DaggerNativeGeometricSphereRowEvaluation
