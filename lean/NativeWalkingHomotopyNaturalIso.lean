import NativeWalkingIntervalHomotopyCategory

/-!
# Whole J-homotopies induce native homotopy-category natural isomorphisms

All products are the existing Mathlib products and all homotopy categories
are SSet.hoFunctor. The parameter is the unchanged original walking interval.
No fibrancy, Joyal model, or substitute weak class is assumed.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DaggerModels
open DaggerActualFreeWalkingIsoIntegerObstruction
open DaggerActualWalkingIsoCategoricalCylinder
open DaggerActualFreeAntiWalkingCategoricalCylinder
open DaggerNativeWalkingIntervalHomotopyCategory
universe u
namespace DaggerNativeWalkingHomotopyNaturalIso
noncomputable section

def hoProductIso (X : SSet.{u}) :
    SSet.hoFunctor.obj (X ⊗ J) ≅ SSet.hoFunctor.obj X ⊗ SSet.hoFunctor.obj J :=
  prodComparisonIso SSet.hoFunctor X J

theorem hoEndpointComparison (X : SSet.{u}) (b : Bool) :
    SSet.hoFunctor.map (intervalEndpoint X b) ≫ (hoProductIso X).hom =
      lift (𝟙 (SSet.hoFunctor.obj X))
        (SSet.hoFunctor.map (SSet.const (ComposableArrows.mk₀ (parameterObject b)) : X ⟶ J)) := by
  rw [hoProductIso, prodComparisonIso_hom]
  change SSet.hoFunctor.map (intervalEndpoint X b) ≫
    lift (SSet.hoFunctor.map (fst X J)) (SSet.hoFunctor.map (snd X J)) = _
  rw [comp_lift, ← SSet.hoFunctor.map_comp, ← SSet.hoFunctor.map_comp]
  simp only [intervalEndpoint, lift_fst, lift_snd]
  rw [SSet.hoFunctor.map_id]

def pairedEndpointIso (X : SSet.{u}) :
    (lift (𝟙 (SSet.hoFunctor.obj X))
      (SSet.hoFunctor.map (SSet.const (ComposableArrows.mk₀ (parameterObject false)) : X ⟶ J))).toFunctor ≅
    (lift (𝟙 (SSet.hoFunctor.obj X))
      (SSet.hoFunctor.map (SSet.const (ComposableArrows.mk₀ (parameterObject true)) : X ⟶ J))).toFunctor :=
  NatIso.ofComponents (fun x ↦
    { hom := Prod.mkHom (𝟙 x) (hoWalkingObjectIso _ _).hom
      inv := Prod.mkHom (𝟙 x) (hoWalkingObjectIso _ _).inv
      hom_inv_id := by
        apply _root_.Prod.ext
        · change (𝟙 x) ≫ (𝟙 x) = 𝟙 x
          simp
        · exact Subsingleton.elim _ _
      inv_hom_id := by
        apply _root_.Prod.ext
        · change (𝟙 x) ≫ (𝟙 x) = 𝟙 x
          simp
        · exact Subsingleton.elim _ _ })
    (fun f ↦ by
      apply _root_.Prod.ext
      · change f ≫ (𝟙 _) = (𝟙 _) ≫ f
        simp
      · exact Subsingleton.elim _ _)

def endpointProductIso (X : SSet.{u}) :
    (SSet.hoFunctor.map (intervalEndpoint X false) ≫ (hoProductIso X).hom).toFunctor ≅
    (SSet.hoFunctor.map (intervalEndpoint X true) ≫ (hoProductIso X).hom).toFunctor :=
  eqToIso (congrArg Cat.Hom.toFunctor (hoEndpointComparison X false)) ≪≫
    pairedEndpointIso X ≪≫
    (eqToIso (congrArg Cat.Hom.toFunctor (hoEndpointComparison X true))).symm

theorem endpointProductInverse (X : SSet.{u}) (b : Bool) :
    (SSet.hoFunctor.map (intervalEndpoint X b) ≫ (hoProductIso X).hom).toFunctor ⋙
      (hoProductIso X).inv.toFunctor =
      (SSet.hoFunctor.map (intervalEndpoint X b)).toFunctor := by
  rw [← Cat.Hom.comp_toFunctor, Category.assoc, Iso.hom_inv_id, Category.comp_id]

def endpointHoIso (X : SSet.{u}) :
    (SSet.hoFunctor.map (intervalEndpoint X false)).toFunctor ≅
      (SSet.hoFunctor.map (intervalEndpoint X true)).toFunctor :=
  (eqToIso (endpointProductInverse X false)).symm ≪≫
    Functor.isoWhiskerRight (endpointProductIso X) (hoProductIso X).inv.toFunctor ≪≫
    eqToIso (endpointProductInverse X true)

/-- A full original J-cylinder identifies the two actual native ho functors. -/
def homotopyHoIso {X Y : SSet.{u}} (H : X ⊗ J ⟶ Y) (f g : X ⟶ Y)
    (h₀ : intervalEndpoint X false ≫ H = f)
    (h₁ : intervalEndpoint X true ≫ H = g) :
    (SSet.hoFunctor.map f).toFunctor ≅ (SSet.hoFunctor.map g).toFunctor :=
  (eqToIso (by
    rw [← Cat.Hom.comp_toFunctor, ← SSet.hoFunctor.map_comp, h₀])).symm ≪≫
    Functor.isoWhiskerRight (endpointHoIso X) (SSet.hoFunctor.map H).toFunctor ≪≫
    eqToIso (by
      rw [← Cat.Hom.comp_toFunctor, ← SSet.hoFunctor.map_comp, h₁])

end
end DaggerNativeWalkingHomotopyNaturalIso
