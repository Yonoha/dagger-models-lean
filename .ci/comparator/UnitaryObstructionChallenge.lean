import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Equivalence

/-! Parts (1)–(2) of `pointset.prop.weak-counterexample`, including actual groupoids. -/
set_option warningAsError false
open CategoryTheory
universe v₁ v₂ u₁ u₂
namespace DaggerModels

class DaggerCategory (C : Type u₁) [Category.{v₁} C] where
  dagger : ∀ {X Y : C}, (X ⟶ Y) → (Y ⟶ X)
  dagger_involutive : ∀ {X Y : C} (f : X ⟶ Y), dagger (dagger f) = f
  dagger_id : ∀ X : C, dagger (𝟙 X) = 𝟙 X
  dagger_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    dagger (f ≫ g) = dagger g ≫ dagger f
export DaggerCategory (dagger)

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C]
  {D : Type u₂} [Category.{v₂} D] [DaggerCategory D]

def IsUnitary {X Y : C} (f : X ⟶ Y) : Prop :=
  f ≫ dagger f = 𝟙 X ∧ dagger f ≫ f = 𝟙 Y

class DaggerFunctor (F : C ⥤ D) : Prop where
  map_dagger : ∀ {X Y : C} (f : X ⟶ Y), F.map (dagger f) = dagger (F.map f)

theorem map_isUnitary (F : C ⥤ D) [DaggerFunctor F] {X Y : C} {f : X ⟶ Y}
    (h : IsUnitary f) : IsUnitary (F.map f) := by sorry

def UnitarilyEssentiallySurjective (F : C ⥤ D) : Prop :=
  ∀ Y : D, ∃ (X : C) (f : F.obj X ⟶ Y), IsUnitary f

namespace UnitaryObstruction
theorem exists_equivalence_not_unitarilyEssentiallySurjective :
    ∃ (C D : Type) (gC : SmallGroupoid C) (gD : SmallGroupoid D),
      letI := gC
      letI := gD
      ∃ (dC : DaggerCategory C) (dD : DaggerCategory D),
        letI := dC
        letI := dD
        ∃ F : C ⥤ D, DaggerFunctor F ∧ F.Full ∧ F.Faithful ∧ F.IsEquivalence ∧
          ¬ UnitarilyEssentiallySurjective F := by sorry
end UnitaryObstruction
end DaggerModels
