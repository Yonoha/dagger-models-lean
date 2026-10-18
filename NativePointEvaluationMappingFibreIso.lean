import NativePushoutConstantMappingFibres
import OriginalFixedObjectCotensorPoints

/-! Fixing a global point in the parameter is the actual fibre of native point evaluation. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MonoidalClosed Simplicial Opposite
open DaggerNativePushoutConstantMappingFibres DaggerOriginalFixedObjectCotensorPoints
open DaggerNativePullbackFibreIso
universe u
namespace DaggerNativePointEvaluationMappingFibreIso
noncomputable section

theorem pointEvaluation_vertex {D X : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ D) (f : D ⟶ X) :
    (pointEvaluation a X).app _ (SSet.ihom₀Equiv.symm f) =
      f.app (op ⦋0⦌) (a.app _ PUnit.unit) := rfl

theorem unitEvaluation_constant_vertex (X : SSet.{u}) (x : X _⦋0⦌) :
    (pointEvaluation (𝟙 (𝟙_ SSet.{u})) X).app _
        (SSet.ihom₀Equiv.symm (SSet.const x)) = x := by
  rw [pointEvaluation_vertex]
  change X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op x = x
  have h : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  rw [h, op_id, X.map_id]
  rfl

theorem pointEvaluation_parameter_square {D : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ D)
    (X : SSet.{u}) :
    𝟙 ((ihom D).obj X) ≫ pointEvaluation a X =
      (MonoidalClosed.pre a).app X ≫ pointEvaluation (𝟙 (𝟙_ SSet.{u})) X := by
  simpa only [Category.id_comp] using
    (pointEvaluation_parameter a (𝟙 (𝟙_ SSet.{u})) X).symm

def pointFibreMap {D : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ D) (X : SSet.{u}) (x : X _⦋0⦌) :
    (constantMappingFibre a X x : SSet.{u}) ⟶
      (SSet.Subcomplex.fiber (pointEvaluation a X) x : SSet.{u}) :=
  SSet.Subcomplex.mapFiber ((MonoidalClosed.pre a).app X) (pointEvaluation a X)
    (𝟙 _) (pointEvaluation (𝟙 (𝟙_ SSet.{u})) X) (pointEvaluation_parameter_square a X)
    _ x (unitEvaluation_constant_vertex X x)

instance pointFibreMap_isIso {D : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ D)
    (X : SSet.{u}) (x : X _⦋0⦌) : IsIso (pointFibreMap a X x) := by
  have hs : IsPullback (𝟙 ((ihom D).obj X)) ((MonoidalClosed.pre a).app X)
      (pointEvaluation a X) (pointEvaluation (𝟙 (𝟙_ SSet.{u})) X) :=
    IsPullback.of_horiz_isIso ⟨pointEvaluation_parameter_square a X⟩
  exact mapFiber_isIso_of_isPullback _ _ _ _ hs _ _ (unitEvaluation_constant_vertex X x)

def pointFibreIso {D : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ D) (X : SSet.{u}) (x : X _⦋0⦌) :
    (constantMappingFibre a X x : SSet.{u}) ≅
      (SSet.Subcomplex.fiber (pointEvaluation a X) x : SSet.{u}) :=
  asIso (pointFibreMap a X x)

theorem pointFibreIso_hom_ι {D : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ D)
    (X : SSet.{u}) (x : X _⦋0⦌) :
    (pointFibreIso a X x).hom ≫ (SSet.Subcomplex.fiber (pointEvaluation a X) x).ι =
      (constantMappingFibre a X x).ι := by
  rw [pointFibreIso, asIso_hom, pointFibreMap, SSet.Subcomplex.mapFiber_ι, Category.comp_id]

end
end DaggerNativePointEvaluationMappingFibreIso
