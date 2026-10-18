import OriginalFixedObjectDegreeCategories

/-!
# Actual ordinary dagger categories in each original degree

Retain the same category on O, the full pointwise dagger and every object-fixing
dagger functor. This is the exact degree target for Mathlib's existing enrichment.
-/

set_option autoImplicit false
open CategoryTheory
open DaggerOriginalFixedObjectDegreeCategories
universe u

namespace DaggerOriginalFixedObjectDaggerDegreeCategories

/-- An actual ordinary dagger structure on the exact given degree category. -/
structure DegreeDaggerCategory (O : Type u) where
  underlying : DegreeCategory O
  dagger : ∀ x y, underlying.category.Hom x y → underlying.category.Hom y x
  involutive : ∀ x y f, dagger y x (dagger x y f) = f
  identity : ∀ x, dagger x x (underlying.category.id x) = underlying.category.id x
  composition : ∀ x y z (f : underlying.category.Hom x y) (g : underlying.category.Hom y z),
    dagger x z (underlying.category.comp f g) =
      underlying.category.comp (dagger y z g) (dagger x y f)

/-- Every exact-O degree functor preserving the original pointwise dagger. -/
structure DegreeDaggerHom {O : Type u} (C D : DegreeDaggerCategory O) where
  underlying : DegreeHom C.underlying D.underlying
  map_dagger : ∀ x y f, underlying.map y x (C.dagger x y f) =
    D.dagger x y (underlying.map x y f)

/-- Equality of the full underlying Hom functor gives equality of the entire dagger functor. -/
theorem degreeDaggerHom_ext {O : Type u} {C D : DegreeDaggerCategory O}
    {F G : DegreeDaggerHom C D} (h : F.underlying = G.underlying) : F = G := by
  cases F
  cases G
  dsimp only at h
  cases h
  rfl

/-- The identity is exactly the native pointwise identity, with the original dagger. -/
def degreeDaggerId {O : Type u} (C : DegreeDaggerCategory O) : DegreeDaggerHom C C where
  underlying := degreeId C.underlying
  map_dagger _ _ _ := rfl

/-- Compose the same original degree Hom functions, preserving the same dagger. -/
def degreeDaggerComp {O : Type u} {C D E : DegreeDaggerCategory O}
    (F : DegreeDaggerHom C D) (G : DegreeDaggerHom D E) : DegreeDaggerHom C E where
  underlying := degreeComp F.underlying G.underlying
  map_dagger x y f := by
    change G.underlying.map y x (F.underlying.map y x (C.dagger x y f)) = _
    rw [F.map_dagger, G.map_dagger]
    rfl

/-- The exact fixed-object ordinary dagger categories form an ordinary category. -/
instance degreeDaggerCategoryCategory (O : Type u) : Category (DegreeDaggerCategory O) where
  Hom := DegreeDaggerHom
  id := degreeDaggerId
  comp := degreeDaggerComp
  id_comp _ := degreeDaggerHom_ext (degreeHom_ext (fun _ _ _ ↦ rfl))
  comp_id _ := degreeDaggerHom_ext (degreeHom_ext (fun _ _ _ ↦ rfl))
  assoc _ _ _ := degreeDaggerHom_ext (degreeHom_ext (fun _ _ _ ↦ rfl))

/-- Forget only the original pointwise dagger, retaining O and all original Hom functions. -/
def degreeDaggerForget (O : Type u) : DegreeDaggerCategory O ⥤ DegreeCategory O where
  obj := DegreeDaggerCategory.underlying
  map := DegreeDaggerHom.underlying

instance degreeDaggerForget_faithful (O : Type u) : (degreeDaggerForget O).Faithful where
  map_injective := degreeDaggerHom_ext

end DaggerOriginalFixedObjectDaggerDegreeCategories
