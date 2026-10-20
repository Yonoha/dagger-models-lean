import OriginalActionFreeForgetAdjunction
import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# Lifting the native functors and adjunctions to literal actions

A natural transformation gives a morphism of the literal actions by its
existing naturality square. Units and counits therefore lift the original
adjunction without changing its underlying maps or either category.
-/

set_option autoImplicit false

open CategoryTheory

universe u v w u' v' w'

namespace DaggerOriginalActionAdjunctionLift

noncomputable section

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (M : Type w) [Monoid M]

/-- The original natural transformation on the literal actions. -/
def actionNatTrans {F G : C ⥤ D} (α : F ⟶ G) : F.mapAction M ⟶ G.mapAction M where
  app X := { hom := α.app X.V, comm g := α.naturality (X.ρ g) }
  naturality _ _ f := by
    apply Action.Hom.ext
    exact α.naturality f.hom

/-- Functoriality of the native action construction in its original functor. -/
def actionLift : (C ⥤ D) ⥤ (Action C M ⥤ Action D M) where
  obj F := F.mapAction M
  map α := actionNatTrans M α
  map_id F := by ext X; rfl
  map_comp α β := by ext X; rfl

/-- The original unit and counit give the adjunction on literal actions. -/
def actionAdjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    F.mapAction M ⊣ G.mapAction M where
  unit :=
    { app X := { hom := adj.unit.app X.V, comm g := adj.unit.naturality (X.ρ g) }
      naturality _ _ f := by
        apply Action.Hom.ext
        exact adj.unit.naturality f.hom }
  counit :=
    { app X := { hom := adj.counit.app X.V, comm g := adj.counit.naturality (X.ρ g) }
      naturality _ _ f := by
        apply Action.Hom.ext
        exact adj.counit.naturality f.hom }
  left_triangle_components X := by
    apply Action.Hom.ext
    exact adj.left_triangle_components X.V
  right_triangle_components X := by
    apply Action.Hom.ext
    exact adj.right_triangle_components X.V

/-- The lifted hom correspondence retains the original underlying adjunction. -/
theorem actionAdjunction_homEquiv_hom {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (X : Action C M) (Y : Action D M) (f : (F.mapAction M).obj X ⟶ Y) :
    ((actionAdjunction M adj).homEquiv X Y f).hom = adj.homEquiv X.V Y.V f.hom := rfl

end

end DaggerOriginalActionAdjunctionLift
