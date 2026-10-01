import DaggerModels.FreeDaggerSimplicialCategory

/-!
# The original free functor acts on paths edgewise

The left adjoint constructed in `FreeDaggerSimplicialCategory` is identified
with its concrete path extension on every graph map, including arbitrary
vertex maps.
-/

open CategoryTheory

universe u

namespace DaggerModels.FreeDaggerSimplicialCategory

open DaggerSimplicialCat FreeSimplicialPaths FreeSimplicialExtension

/-- The actual graph map on the edge quiver in one simplicial degree. -/
def degreeMap {G H : DaggerSimplicialGraph.{u}} (k : G ⟶ H)
    (n : SimplexCategoryᵒᵖ) : At G n ⥤q At H n where
  obj := k.obj
  map {x y} e := (k.map x y).app n e

/-- The original adjoint functor extends the map to the singleton edges of its target. -/
theorem functor_map_eq_lift {G H : DaggerSimplicialGraph.{u}} (k : G ⟶ H) :
    FreeDaggerSimplicialCategory.functor.map k = lift (k ≫ unit H) := by
  change lift (k ≫ restrict (𝟙 (daggerCat H))) = lift (k ≫ unit H)
  rw [restrict, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The actual free functor retains the original, arbitrary vertex map. -/
@[simp] theorem functor_map_obj {G H : DaggerSimplicialGraph.{u}} (k : G ⟶ H) :
    (FreeDaggerSimplicialCategory.functor.map k).obj = k.obj := rfl

/-- On every finite path the original free functor applies the graph map edgewise. -/
theorem functor_map_app {G H : DaggerSimplicialGraph.{u}} (k : G ⟶ H)
    (n : SimplexCategoryᵒᵖ) {x y : G.Obj} (p : Path G n x y) :
    ((FreeDaggerSimplicialCategory.functor.map k).map x y).app n p =
      (degreeMap k n).mapPath p := by
  change value G (C := (daggerCat H).Obj) (k ≫ unit H).obj
    (k ≫ unit H).map n p = (degreeMap k n).mapPath p
  induction p with
  | nil => rfl
  | @cons y z p e ih =>
    rw [value_cons, ih]
    rfl

end DaggerModels.FreeDaggerSimplicialCategory
