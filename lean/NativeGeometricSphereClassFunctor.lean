import NativeGeometricSphereComponents

/-! Geometric free sphere classes form the native singular boundary mapping-component functor. -/
set_option autoImplicit false
open CategoryTheory MonoidalClosed
open DaggerCountableSphereQuotient DaggerNativeGeometricSphereComponents
universe u
namespace DaggerNativeGeometricSphereClassFunctor
noncomputable section

def sphereClassFunctor (n : ℕ) : SSet.{u} ⥤ Type u where
  obj X := SphereClasses n X
  map g := sphereClassMap n g
  map_id X := by
    funext c
    obtain ⟨f, rfl⟩ := Quot.mk_surjective c
    change Quot.mk ContinuousMap.Homotopic ((SSet.toTop.map (𝟙 X)).hom.comp f) =
      Quot.mk ContinuousMap.Homotopic f
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp g h := by
    funext c
    obtain ⟨f, rfl⟩ := Quot.mk_surjective c
    change Quot.mk ContinuousMap.Homotopic ((SSet.toTop.map (g ≫ h)).hom.comp f) =
      Quot.mk ContinuousMap.Homotopic
        ((SSet.toTop.map h).hom.comp ((SSet.toTop.map g).hom.comp f))
    rw [CategoryTheory.Functor.map_comp]
    rfl

def sphereClassesNatIso (n : ℕ) : sphereClassFunctor.{u} n ≅
    (SSet.toTop ⋙ TopCat.toSSet) ⋙
      ihom (SSet.boundary (n + 1) : SSet.{u}) ⋙ SSet.π₀Functor :=
  NatIso.ofComponents (fun X ↦ (sphereComponentsEquiv n X).toIso) (by
    intro X Y g
    funext c
    exact (sphereComponentsEquiv_natural n g c).symm)

end
end DaggerNativeGeometricSphereClassFunctor
