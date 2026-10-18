import NativeGeometricFreeMappingClasses

/-! The actual continuous-class comparison retains ordinary target postcomposition. -/
set_option autoImplicit false
open CategoryTheory MonoidalClosed
open DaggerNativeFreeMappingComponents DaggerNativeGeometricFreeMappingClasses
open DaggerCountableContinuousClasses
universe u
namespace DaggerNativeGeometricMappingNaturality
noncomputable section

def geometricClassMap (K : SSet.{u}) {X Y : SSet.{u}} (g : X ⟶ Y) :
    Classes K X → Classes K Y :=
  Quot.map (fun f ↦ (SSet.toTop.map g).hom.comp f) (fun _ _ h ↦
    (ContinuousMap.Homotopic.refl (SSet.toTop.map g).hom).comp h)

theorem geometricClassesEquiv_natural (K : SSet.{u}) {X Y : SSet.{u}} (g : X ⟶ Y)
    (c : Classes K X) :
    SSet.mapπ₀ ((ihom K).map (TopCat.toSSet.map (SSet.toTop.map g)))
      (geometricClassesEquiv K X c) = geometricClassesEquiv K Y (geometricClassMap K g c) := by
  obtain ⟨f, rfl⟩ := Quot.mk_surjective c
  change SSet.mapπ₀ ((ihom K).map (TopCat.toSSet.map (SSet.toTop.map g)))
      (component ((continuousAdjointEquiv K X).symm f)) =
    component ((continuousAdjointEquiv K Y).symm ((SSet.toTop.map g).hom.comp f))
  rw [component_target]
  exact congrArg component (sSetTopAdj.homEquiv_naturality_right
    (TopCat.ofHom f) (SSet.toTop.map g)).symm

end
end DaggerNativeGeometricMappingNaturality
