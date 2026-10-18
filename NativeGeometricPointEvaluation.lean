import NativeGeometricSphereComponents
import OriginalFixedObjectCotensorPoints

/-! Actual evaluation of a realized map agrees with native internal-Hom point evaluation. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Simplicial
open DaggerNativeGeometricFreeMappingClasses DaggerNativeFreeMappingComponents
open DaggerOriginalFixedObjectCotensorPoints DaggerNativeGeometricSphereComponents
universe u
namespace DaggerNativeGeometricPointEvaluation
noncomputable section

def realizedVertex (K : SSet.{u}) (v : K _⦋0⦌) : ↑(SSet.toTop.obj K) :=
  TopCat.toSSetObj₀Equiv ((sSetTopAdj.unit.app K).app _ v)

theorem continuousAdjoint_vertex (K X : SSet.{u})
    (f : K ⟶ TopCat.toSSet.obj (SSet.toTop.obj X)) (v : K _⦋0⦌) :
    TopCat.toSSetObj₀Equiv (f.app _ v) =
      (continuousAdjointEquiv K X f) (realizedVertex K v) := by
  have h := congrArg (fun g : K ⟶ TopCat.toSSet.obj (SSet.toTop.obj X) ↦
    TopCat.toSSetObj₀Equiv (g.app _ v)) (DaggerSphereNullity.unit_singular_realized f)
  exact h.symm

theorem pointEvaluation_component {K X : SSet.{u}} (v : K _⦋0⦌) (f : K ⟶ X) :
    SSet.mapπ₀ (pointEvaluation (SSet.const v) X) (component f) =
      SSet.π₀.mk (f.app _ v) := by
  change SSet.π₀.mk
    (f.app _ (K.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op v)) = _
  have h : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  rw [h, op_id, K.map_id]
  rfl

def geometricEvaluation (K X : SSet.{u}) (v : K _⦋0⦌) :
    DaggerCountableContinuousClasses.Classes K X →
      (TopCat.toSSet.obj (SSet.toTop.obj X)).π₀ :=
  fun c ↦ SSet.mapπ₀ (pointEvaluation (SSet.const v) _)
    (geometricClassesEquiv K X c)

theorem geometricEvaluation_mk (K X : SSet.{u}) (v : K _⦋0⦌)
    (f : C(↑(SSet.toTop.obj K), ↑(SSet.toTop.obj X))) :
    geometricEvaluation K X v (Quot.mk ContinuousMap.Homotopic f) =
      SSet.π₀.mk (TopCat.toSSetObj₀Equiv.symm (f (realizedVertex K v))) := by
  change SSet.mapπ₀ (pointEvaluation (SSet.const v) _)
    (component ((continuousAdjointEquiv K X).symm f)) = _
  rw [pointEvaluation_component]
  congr 1
  apply TopCat.toSSetObj₀Equiv.injective
  rw [Equiv.apply_symm_apply, continuousAdjoint_vertex, Equiv.apply_symm_apply]

def sphereEvaluation (n : ℕ) (X : SSet.{u})
    (v : (SSet.boundary (n + 1) : SSet.{u}) _⦋0⦌) :
    DaggerCountableSphereQuotient.SphereClasses n X →
      (TopCat.toSSet.obj (SSet.toTop.obj X)).π₀ :=
  fun c ↦ SSet.mapπ₀ (pointEvaluation (SSet.const v) _) (sphereComponentsEquiv n X c)

theorem sphereEvaluation_mk (n : ℕ) (X : SSet.{u})
    (v : (SSet.boundary (n + 1) : SSet.{u}) _⦋0⦌)
    (f : C(↑(TopCat.sphere n), ↑(SSet.toTop.obj X))) :
    sphereEvaluation n X v (Quot.mk ContinuousMap.Homotopic f) =
      SSet.π₀.mk (TopCat.toSSetObj₀Equiv.symm
        (f (DaggerCountableSphereQuotient.toSphere n
          (realizedVertex (SSet.boundary (n + 1) : SSet.{u}) v)))) := by
  change geometricEvaluation (DaggerCountableSphereQuotient.Boundary n) X v
    ((DaggerCountableSphereQuotient.classesEquiv n X).symm
      (Quot.mk ContinuousMap.Homotopic f)) = _
  rw [DaggerCountableSphereQuotient.classesEquiv_symm_mk, geometricEvaluation_mk]
  rfl

end
end DaggerNativeGeometricPointEvaluation
