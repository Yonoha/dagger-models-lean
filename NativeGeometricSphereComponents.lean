import NativeGeometricMappingNaturality
import OriginalCountableSphereQuotientRecovered

/-! Reuse the original geometric boundary/sphere homeomorphism for exact free sphere classes. -/
set_option autoImplicit false
open CategoryTheory MonoidalClosed
open DaggerNativeFreeMappingComponents DaggerNativeGeometricFreeMappingClasses
open DaggerNativeGeometricMappingNaturality DaggerCountableSphereQuotient
universe u
namespace DaggerNativeGeometricSphereComponents
noncomputable section

def sphereComponentsEquiv (n : ℕ) (X : SSet.{u}) :
    SphereClasses n X ≃
      ((ihom (SSet.boundary (n + 1) : SSet.{u})).obj
        (TopCat.toSSet.obj (SSet.toTop.obj X))).π₀ :=
  (classesEquiv n X).symm.trans (geometricClassesEquiv (Boundary n) X)

theorem sphereComponentsEquiv_mk (n : ℕ) (X : SSet.{u})
    (f : C(↑(TopCat.sphere n), ↑(SSet.toTop.obj X))) :
    sphereComponentsEquiv n X (Quot.mk ContinuousMap.Homotopic f) =
      component ((continuousAdjointEquiv (Boundary n) X).symm (f.comp (toSphere n))) := by
  change geometricClassesEquiv (Boundary n) X
    ((classesEquiv n X).symm (Quot.mk ContinuousMap.Homotopic f)) = _
  rw [classesEquiv_symm_mk]
  rfl

def sphereClassMap (n : ℕ) {X Y : SSet.{u}} (g : X ⟶ Y) :
    SphereClasses n X → SphereClasses n Y :=
  Quot.map (fun f ↦ (SSet.toTop.map g).hom.comp f) (fun _ _ h ↦
    (ContinuousMap.Homotopic.refl (SSet.toTop.map g).hom).comp h)

theorem sphereComponentsEquiv_natural (n : ℕ) {X Y : SSet.{u}} (g : X ⟶ Y)
    (c : SphereClasses n X) :
    SSet.mapπ₀ ((ihom (SSet.boundary (n + 1) : SSet.{u})).map
      (TopCat.toSSet.map (SSet.toTop.map g))) (sphereComponentsEquiv n X c) =
        sphereComponentsEquiv n Y (sphereClassMap n g c) := by
  obtain ⟨f, rfl⟩ := Quot.mk_surjective c
  change SSet.mapπ₀ _ (sphereComponentsEquiv n X (Quot.mk ContinuousMap.Homotopic f)) =
    sphereComponentsEquiv n Y (Quot.mk ContinuousMap.Homotopic ((SSet.toTop.map g).hom.comp f))
  rw [sphereComponentsEquiv_mk, sphereComponentsEquiv_mk]
  exact geometricClassesEquiv_natural (Boundary n) g (Quot.mk _ (f.comp (toSphere n)))

end
end DaggerNativeGeometricSphereComponents
