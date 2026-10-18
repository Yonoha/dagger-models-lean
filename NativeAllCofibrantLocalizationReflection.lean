import NativeFibrationHomotopyInverseWeak
import NativeRightHomotopyClassFunctor

/-! Localization reflects the native weak class in a model category whose objects are cofibrant. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerNativeFibrationHomotopyInverseWeak DaggerNativeRightHomotopyClassFunctor
universe u v w t

namespace DaggerNativeAllCofibrantLocalizationReflection
noncomputable section
variable {C : Type u} [Category.{v} C] [ModelCategory C] [∀ X : C, IsCofibrant X]

/-- Native fibrant homotopy classes detect a weak map with fibrant codomain. -/
theorem weakEquivalence_of_precomp_bijective {X Y : C} (f : X ⟶ Y) [IsFibrant Y]
    (h : ∀ (Z : C) [IsFibrant Z],
      Function.Bijective (fun g : RightHomotopyClass Y Z ↦ g.precomp f)) :
    WeakEquivalence f := by
  let d := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) f
  have : IsFibrant d.Z := isFibrant_of_fibration d.p
  have hp (Z : C) [IsFibrant Z] :
      Function.Bijective (fun g : RightHomotopyClass Y Z ↦ g.precomp d.p) := by
    rw [← Function.Bijective.of_comp_iff'
      (RightHomotopyClass.precomp_bijective_of_weakEquivalence Z d.i)]
    convert h Z using 1
    ext g
    obtain ⟨g, rfl⟩ := g.mk_surjective
    simp
  obtain ⟨g, hg⟩ := (hp d.Z).surjective (RightHomotopyClass.mk (𝟙 d.Z))
  obtain ⟨g, rfl⟩ := g.mk_surjective
  have hZ : RightHomotopyRel (d.p ≫ g) (𝟙 d.Z) := by
    change RightHomotopyClass.mk (d.p ≫ g) = RightHomotopyClass.mk (𝟙 d.Z) at hg
    rwa [RightHomotopyClass.mk_eq_mk_iff] at hg
  have hY : RightHomotopyRel (g ≫ d.p) (𝟙 Y) := by
    rw [← RightHomotopyClass.mk_eq_mk_iff]
    apply (hp Y).injective
    change RightHomotopyClass.mk (d.p ≫ (g ≫ d.p)) =
      RightHomotopyClass.mk (d.p ≫ 𝟙 Y)
    apply RightHomotopyClass.sound
    simpa [Category.assoc] using hZ.postcomp d.p
  have : WeakEquivalence d.p := fibration_weakEquivalence_of_homotopy_inverse d.p g hZ hY
  have hw : WeakEquivalence (d.i ≫ d.p) := inferInstance
  rwa [d.fac] at hw

variable {H : Type w} [Category.{t} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)]

/-- The implication uses only the actual model structure and the localization universal property. -/
theorem weakEquivalence_of_localization_isIso {X Y : C} (f : X ⟶ Y) [IsFibrant Y]
    [IsIso (L.map f)] : WeakEquivalence f :=
  weakEquivalence_of_precomp_bijective f
    (fun Z _ ↦ precomp_bijective_of_localization_isIso L f Z)

end
end DaggerNativeAllCofibrantLocalizationReflection
