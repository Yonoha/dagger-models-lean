import Mathlib.AlgebraicTopology.ModelCategory.Homotopy

/-! Native homotopy lifting turns a fibrant homotopy inverse into a weak equivalence. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Limits
universe u v

namespace DaggerNativeFibrationHomotopyInverseWeak
noncomputable section
variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- A native left homotopy preserves the native weak class. -/
theorem weakEquivalence_of_leftHomotopyRel {X Y : C} {f g : X ⟶ Y}
    (h : LeftHomotopyRel f g) [WeakEquivalence g] : WeakEquivalence f := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.weakEquivalence_iff.mpr inferInstance

/-- Lift the native cylinder homotopy to replace a homotopy section by a strict section. -/
theorem strictSection_of_leftHomotopy {X Y : C} [IsCofibrant Y]
    (p : X ⟶ Y) [Fibration p] (g : Y ⟶ X) (h : LeftHomotopyRel (g ≫ p) (𝟙 Y)) :
    ∃ s : Y ⟶ X, LeftHomotopyRel g s ∧ s ≫ p = 𝟙 Y := by
  obtain ⟨P, hP, ⟨h⟩⟩ := h.exists_good_cylinder
  obtain ⟨s, hs, hsp⟩ := Cylinder.LeftHomotopy.covering_homotopy h p g rfl
  refine ⟨s, hs.leftHomotopyRel, ?_⟩
  rw [← hs.h₁, Category.assoc, hsp, h.h₁]

/-- A fibration between bifibrant objects with a native homotopy inverse is weak. -/
theorem fibration_weakEquivalence_of_homotopy_inverse {X Y : C}
    [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y]
    (p : X ⟶ Y) [Fibration p] (g : Y ⟶ X)
    (hX : RightHomotopyRel (p ≫ g) (𝟙 X))
    (hY : RightHomotopyRel (g ≫ p) (𝟙 Y)) : WeakEquivalence p := by
  obtain ⟨s, hgs, hsp⟩ := strictSection_of_leftHomotopy p g hY.leftHomotopyRel
  have h : LeftHomotopyRel (p ≫ s) (𝟙 X) :=
    ((hX.leftHomotopyRel.symm).trans (hgs.precomp p)).symm
  have : WeakEquivalence (p ≫ s) := weakEquivalence_of_leftHomotopyRel h
  let r : RetractArrow p (p ≫ s) :=
    { i := Arrow.homMk (𝟙 X) s (by simp)
      r := Arrow.homMk (𝟙 X) p (by simp [Category.assoc, hsp])
      retract := by
        ext <;> simp [hsp] }
  exact ⟨MorphismProperty.of_retract r (mem_weakEquivalences (p ≫ s))⟩

end
end DaggerNativeFibrationHomotopyInverseWeak
