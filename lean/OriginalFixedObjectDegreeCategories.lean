import OriginalFixedObjectCompletionMappingComparison
import Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject

/-!
# Ordinary degree categories on the exact fixed object type

Package the actual ordinary category structure on O. All arrows have identity
object function and retain every original Hom function, identity and composition.
These are the degree categories used to reuse Mathlib's simplicial-object enrichment.
-/

set_option autoImplicit false
open CategoryTheory
universe u

namespace DaggerOriginalFixedObjectDegreeCategories

/-- An ordinary category with precisely the given object type O. -/
structure DegreeCategory (O : Type u) where
  category : Category.{u} O

/-- Every actual Hom function of a functor fixing O, with its full original laws. -/
structure DegreeHom {O : Type u} (C D : DegreeCategory O) where
  map : ∀ x y, C.category.Hom x y → D.category.Hom x y
  map_id : ∀ x, map x x (C.category.id x) = D.category.id x
  map_comp : ∀ x y z (f : C.category.Hom x y) (g : C.category.Hom y z),
    map x z (C.category.comp f g) = D.category.comp (map x y f) (map y z g)

/-- All original Hom functions determine the whole fixed-object degree functor. -/
theorem degreeHom_ext {O : Type u} {C D : DegreeCategory O} {F G : DegreeHom C D}
    (h : ∀ x y f, F.map x y f = G.map x y f) : F = G := by
  have he : F.map = G.map := funext fun x ↦ funext fun y ↦ funext fun f ↦ h x y f
  cases F
  cases G
  dsimp only at he
  cases he
  rfl

/-- The actual identity function on every original degree Hom. -/
def degreeId {O : Type u} (C : DegreeCategory O) : DegreeHom C C where
  map _ _ f := f
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

/-- Compose the full original Hom functions, retaining identity on O. -/
def degreeComp {O : Type u} {C D E : DegreeCategory O} (F : DegreeHom C D)
    (G : DegreeHom D E) : DegreeHom C E where
  map x y f := G.map x y (F.map x y f)
  map_id x := by rw [F.map_id, G.map_id]
  map_comp x y z f g := by rw [F.map_comp, G.map_comp]

/-- The ordinary category of exact-O degree categories and all object-fixing functors. -/
instance degreeCategoryCategory (O : Type u) : Category (DegreeCategory O) where
  Hom := DegreeHom
  id := degreeId
  comp := degreeComp
  id_comp _ := degreeHom_ext (fun _ _ _ ↦ rfl)
  comp_id _ := degreeHom_ext (fun _ _ _ ↦ rfl)
  assoc _ _ _ := degreeHom_ext (fun _ _ _ ↦ rfl)

/-- The literal full native ordinary functor, with exactly the identity object function. -/
def originalFunctor {O : Type u} {C D : DegreeCategory O} (F : C ⟶ D) :
    @Functor O C.category O D.category :=
  @CategoryTheory.Functor.mk O C.category O D.category id (fun {x y} ↦ F.map x y)
    F.map_id (fun {_ _ _} f g ↦ F.map_comp _ _ _ f g)

end DaggerOriginalFixedObjectDegreeCategories
