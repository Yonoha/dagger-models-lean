import NativeIhomTensorComparison
import NativeJoyalMappingWeakProperties

/-!
# The fixed whole Joyal mapping weak predicate is stable under native tensor products

All quasi-category targets are retained. The actual internal-Hom currying square reduces
precomposition by K ◁ f to the same original test at the actual quasi-category ihom K Z.
Native ho carries the entire comparison square to an arrow isomorphism. No Cartesian
Joyal model or tensor stability hypothesis is supplied.
-/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory
open DaggerNativeJoyalMappingTest DaggerNativeCatEquivalenceWeakProperties
open DaggerNativeIhomQuasicategories DaggerNativeIhomTensorComparison
universe u
namespace DaggerNativeJoyalMappingTensor
noncomputable section

local instance nativeBraiding : BraidedCategory SSet.{u} :=
  BraidedCategory.ofCartesianMonoidalCategory

/-- Tensoring on the left preserves exactly the original all-target mapping weak test. -/
theorem weak_whiskerLeft (K : SSet.{u}) {A B : SSet.{u}} (f : A ⟶ B)
    (hf : weakCategoricalEquivalences f) : weakCategoricalEquivalences (K ◁ f) := by
  intro Z hZ
  haveI : ((ihom K).obj Z).Quasicategory := ihom_quasicategory K Z
  let g := (MonoidalClosed.pre (K ◁ f)).app Z
  let h := (MonoidalClosed.pre f).app ((ihom K).obj Z)
  let eA := comparisonIso K A Z
  let eB := comparisonIso K B Z
  let e : Arrow.mk (SSet.hoFunctor.map g) ≅ Arrow.mk (SSet.hoFunctor.map h) :=
    Arrow.isoMk (SSet.hoFunctor.mapIso eB) (SSet.hoFunctor.mapIso eA) (by
      change SSet.hoFunctor.map eB.hom ≫ SSet.hoFunctor.map h =
        SSet.hoFunctor.map g ≫ SSet.hoFunctor.map eA.hom
      rw [← SSet.hoFunctor.map_comp, ← SSet.hoFunctor.map_comp]
      exact congrArg SSet.hoFunctor.map (pre_naturality K Z f).symm)
  exact equivalences.of_retract (Retract.ofIso e) (hf ((ihom K).obj Z))

/-- Tensoring on the right preserves the same predicate by the actual native braiding. -/
theorem weak_whiskerRight {A B : SSet.{u}} (f : A ⟶ B)
    (hf : weakCategoricalEquivalences f) (K : SSet.{u}) :
    weakCategoricalEquivalences (f ▷ K) := by
  let e : Arrow.mk (f ▷ K) ≅ Arrow.mk (K ◁ f) :=
    Arrow.isoMk (β_ A K) (β_ B K) (by
      exact (BraidedCategory.braiding_naturality_left f K).symm)
  exact weakCategoricalEquivalences.of_retract (Retract.ofIso e)
    (weak_whiskerLeft K f hf)

/-- The entire native tensor map of two original mapping-weak maps is mapping weak. -/
theorem weak_tensor_map {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (hf : weakCategoricalEquivalences f) (hg : weakCategoricalEquivalences g) :
    weakCategoricalEquivalences (f ⊗ₘ g) := by
  rw [tensorHom_def]
  exact weakCategoricalEquivalences.comp_mem _ _
    (weak_whiskerRight f hf C) (weak_whiskerLeft B g hg)

end
end DaggerNativeJoyalMappingTensor
