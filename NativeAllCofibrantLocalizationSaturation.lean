import NativeAllCofibrantLocalizationReflection

/-! Native fibrant replacement extends localization reflection to every target object. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Limits
universe u v w t

namespace DaggerNativeAllCofibrantLocalizationSaturation
noncomputable section
variable {C : Type u} [Category.{v} C] [ModelCategory C] [∀ X : C, IsCofibrant X]
variable {H : Type w} [Category.{t} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)]

/-- The native weak class is reflected by localization for every original map. -/
theorem weakEquivalence_of_localization_isIso {X Y : C} (f : X ⟶ Y)
    [IsIso (L.map f)] : WeakEquivalence f := by
  let d := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
    (terminal.from Y)
  have : IsFibrant d.Z := (isFibrant_iff_of_isTerminal d.p terminalIsTerminal).mpr inferInstance
  have : IsIso (L.map d.i) := Localization.inverts L (weakEquivalences C) d.i
    (mem_weakEquivalences d.i)
  have : IsIso (L.map (f ≫ d.i)) := by
    rw [Functor.map_comp]
    infer_instance
  have : WeakEquivalence (f ≫ d.i) :=
    DaggerNativeAllCofibrantLocalizationReflection.weakEquivalence_of_localization_isIso
      L (f ≫ d.i)
  exact weakEquivalence_of_postcomp f d.i

/-- The full native weak class is precisely the maps inverted by any actual localization. -/
theorem weakEquivalence_iff_localization_isIso {X Y : C} (f : X ⟶ Y) :
    WeakEquivalence f ↔ IsIso (L.map f) := by
  constructor
  · intro hf
    have : WeakEquivalence f := hf
    exact Localization.inverts L (weakEquivalences C) f (mem_weakEquivalences f)
  · intro hf
    have : IsIso (L.map f) := hf
    exact weakEquivalence_of_localization_isIso L f

end
end DaggerNativeAllCofibrantLocalizationSaturation
