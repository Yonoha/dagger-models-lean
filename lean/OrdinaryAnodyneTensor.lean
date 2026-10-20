import TopCatModelCategory.SSet.Fibrations
import TopCatModelCategory.ModelCategorySSet
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-! Arbitrary-factor tensor wrappers for the existing ordinary SSet anodyne property. -/

open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerOrdinaryAnodyneTensor

lemma whiskerLeft {A B : SSet.{u}} (i : A ⟶ B)
    (hi : SSet.anodyneExtensions i) (H : SSet.{u}) :
    SSet.anodyneExtensions (H ◁ i) := by
  intro X Y p hp
  letI : Fibration p := (fibration_iff p).2 hp
  exact ((ihom.adjunction H).hasLiftingProperty_iff i p).2
    (hi _ (mem_fibrations ((ihom H).map p)))

lemma whiskerRight {A B : SSet.{u}} (i : A ⟶ B)
    (hi : SSet.anodyneExtensions i) (H : SSet.{u}) :
    SSet.anodyneExtensions (i ▷ H) := by
  have e : Arrow.mk (H ◁ i) ≅ Arrow.mk (i ▷ H) :=
    Arrow.isoMk (β_ H A) (β_ H B) (by simp)
  exact (SSet.anodyneExtensions.arrow_mk_iso_iff e).1 (whiskerLeft i hi H)

lemma anodyne_iff_trivialCofibration {A B : SSet.{u}} (i : A ⟶ B) :
    SSet.anodyneExtensions i ↔ trivialCofibrations SSet.{u} i := by
  change (fibrations SSet.{u}).llp i ↔ trivialCofibrations SSet.{u} i
  rw [fibrations_llp]

end DaggerOrdinaryAnodyneTensor
