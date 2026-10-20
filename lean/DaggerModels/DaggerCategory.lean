import Mathlib.CategoryTheory.Groupoid

/-!
# Ordinary dagger categories

The hom-level axioms here are the ordinary, discrete-mapping-space instance of
`bg.def.dagger-scat` in Part I. A unitary morphism has the dagger as its two-sided inverse.
This file does not identify strict unitarity with coherent unitarity in a simplicial category.
-/

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace DaggerModels

/-- An identity-on-objects, involutive contravariant operation on an ordinary category. -/
class DaggerCategory (C : Type u₁) [Category.{v₁} C] where
  dagger : ∀ {X Y : C}, (X ⟶ Y) → (Y ⟶ X)
  dagger_involutive : ∀ {X Y : C} (f : X ⟶ Y), dagger (dagger f) = f
  dagger_id : ∀ X : C, dagger (𝟙 X) = 𝟙 X
  dagger_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    dagger (f ≫ g) = dagger g ≫ dagger f

export DaggerCategory (dagger)

attribute [simp] DaggerCategory.dagger_involutive DaggerCategory.dagger_id
  DaggerCategory.dagger_comp

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C]
  {D : Type u₂} [Category.{v₂} D] [DaggerCategory D]

/-- A morphism is unitary when its dagger is its two-sided inverse. -/
def IsUnitary {X Y : C} (f : X ⟶ Y) : Prop :=
  f ≫ dagger f = 𝟙 X ∧ dagger f ≫ f = 𝟙 Y

/-- A unitary morphism defines an actual categorical isomorphism. -/
def IsUnitary.toIso {X Y : C} {f : X ⟶ Y} (h : IsUnitary f) : X ≅ Y where
  hom := f
  inv := dagger f
  hom_inv_id := h.1
  inv_hom_id := h.2

@[simp] theorem isUnitary_id (X : C) : IsUnitary (𝟙 X) := by
  simp [IsUnitary]

/-- An ordinary functor between dagger categories preserves the dagger operation. -/
class DaggerFunctor (F : C ⥤ D) : Prop where
  map_dagger : ∀ {X Y : C} (f : X ⟶ Y), F.map (dagger f) = dagger (F.map f)

/-- Dagger functors preserve strict unitary morphisms. -/
theorem map_isUnitary (F : C ⥤ D) [DaggerFunctor F] {X Y : C} {f : X ⟶ Y}
    (h : IsUnitary f) : IsUnitary (F.map f) := by
  constructor
  · rw [← DaggerFunctor.map_dagger, ← F.map_comp, h.1, F.map_id]
  · rw [← DaggerFunctor.map_dagger, ← F.map_comp, h.2, F.map_id]

/-- Every target object is connected to an image object by a unitary morphism.
The witness yields an isomorphism via `IsUnitary.toIso`. -/
def UnitarilyEssentiallySurjective (F : C ⥤ D) : Prop :=
  ∀ Y : D, ∃ (X : C) (f : F.obj X ⟶ Y), IsUnitary f

namespace DaggerCategory

/-- A full subcategory inherits the dagger, since it only restricts objects. -/
instance fullSubcategory (P : ObjectProperty C) : DaggerCategory P.FullSubcategory where
  dagger f := ObjectProperty.homMk (dagger f.hom)
  dagger_involutive f := by
    apply ObjectProperty.hom_ext
    exact dagger_involutive f.hom
  dagger_id X := by
    apply ObjectProperty.hom_ext
    exact dagger_id X.obj
  dagger_comp f g := by
    apply ObjectProperty.hom_ext
    exact dagger_comp f.hom g.hom

/-- The standard full-subcategory inclusion preserves the inherited dagger. -/
instance inclusionDaggerFunctor (P : ObjectProperty C) : DaggerFunctor P.ι where
  map_dagger _ := rfl

end DaggerCategory
end DaggerModels
