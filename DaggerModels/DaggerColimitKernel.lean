import DaggerModels.DaggerGraphPresentable
import DaggerModels.FreeDaggerSimplicialCategory
import DaggerModels.DaggerHomKernel

/-! The semantic hom relation for a prospective colimit. The only
colimits used here are proved graph colimits. Actual dagger-category cocones
give free extensions; their joint kernel stays a proposition. No category
colimit or quotient is assumed or asserted in this file. -/

open CategoryTheory Limits MonoidalCategory

universe u

namespace DaggerModels.DaggerSimplicialCat.ColimitKernel

variable {J : Type u} [SmallCategory J] (K : J ⥤ DaggerSimplicialCat.{u, u})

attribute [local instance] daggerGraphHasColimits

/-- Identify the vertices and edges using the actual graph colimit first. -/
noncomputable def graph : DaggerSimplicialGraph.{u} := colimit (K ⋙ forgetGraph)

/-- The original free category on that graph, including new composable paths. -/
noncomputable def free : DaggerSimplicialCat.{u, u} :=
  FreeDaggerSimplicialCategory.functor.obj (graph K)

/-- Each existing cocone extends from the graph colimit by the proved adjunction. -/
noncomputable def freeLift (s : Cocone K) : free K ⟶ s.pt :=
  FreeDaggerSimplicialCategory.lift
    (colimit.desc (K ⋙ forgetGraph) (forgetGraph.mapCocone s))

/-- The graph map from an original diagram object to the free category. -/
noncomputable def leg (j : J) : forgetGraph.obj (K.obj j) ⟶ forgetGraph.obj (free K) :=
  colimit.ι (K ⋙ forgetGraph) j ≫ FreeDaggerSimplicialCategory.unit (graph K)

/-- Free extension recovers every original cocone leg exactly, including its objects. -/
theorem leg_freeLift (s : Cocone K) (j : J) :
    leg K j ≫ forgetGraph.map (freeLift K s) = forgetGraph.map (s.ι.app j) := by
  unfold leg freeLift
  rw [Category.assoc]
  change colimit.ι (K ⋙ forgetGraph) j ≫
      FreeDaggerSimplicialCategory.restrict
        (FreeDaggerSimplicialCategory.lift (C := s.pt)
          (colimit.desc (K ⋙ forgetGraph) (forgetGraph.mapCocone s))) = _
  rw [FreeDaggerSimplicialCategory.restrict_lift]
  exact colimit.ι_desc (forgetGraph.mapCocone s) j

/-- Intersect kernels of all actual cocones; the family has universe `u+1`. -/
noncomputable def rel (n : SimplexCategoryᵒᵖ) (X Y : (free K).Obj)
    (f g : (X ⟶[SSet.{u}] Y).obj n) : Prop :=
  HomKernel.rel (fun s : Cocone K ↦ freeLift K s) n X Y f g

/-- The image of an original identity is identified with the free identity. -/
theorem rel_id (j : J) (n : SimplexCategoryᵒᵖ) (X : (K.obj j).Obj) :
    rel K n ((leg K j).obj X) ((leg K j).obj X)
      (((leg K j).map X X).app n ((eId SSet X).app n PUnit.unit))
      ((eId SSet (C := (free K).Obj) ((leg K j).obj X)).app n PUnit.unit) := by
  intro s
  have h : ∀ X : (K.obj j).Obj,
      (((leg K j ≫ forgetGraph.map (freeLift K s)).map X X).app n
        ((eId SSet X).app n PUnit.unit)) =
      (eId SSet (C := s.pt.Obj)
        ((leg K j ≫ forgetGraph.map (freeLift K s)).obj X)).app n PUnit.unit := by
    rw [leg_freeLift]
    intro X
    exact congrArg (fun a ↦ a.app n PUnit.unit) ((s.ι.app j).map_id X)
  exact (h X).trans
    (congrArg (fun a ↦ a.app n PUnit.unit) ((freeLift K s).map_id ((leg K j).obj X))).symm

/-- The image of an original composite agrees with composition of its two images. -/
theorem rel_comp (j : J) (n : SimplexCategoryᵒᵖ) (X Y Z : (K.obj j).Obj)
    (f : (X ⟶[SSet.{u}] Y).obj n) (g : (Y ⟶[SSet.{u}] Z).obj n) :
    rel K n ((leg K j).obj X) ((leg K j).obj Z)
      (((leg K j).map X Z).app n ((eComp SSet X Y Z).app n (f, g)))
      ((eComp SSet (C := (free K).Obj)
        ((leg K j).obj X) ((leg K j).obj Y) ((leg K j).obj Z)).app n
        (((leg K j).map X Y).app n f, ((leg K j).map Y Z).app n g)) := by
  intro s
  have h : ∀ (X Y Z : (K.obj j).Obj)
      (f : (X ⟶[SSet.{u}] Y).obj n) (g : (Y ⟶[SSet.{u}] Z).obj n),
      ((leg K j ≫ forgetGraph.map (freeLift K s)).map X Z).app n
        ((eComp SSet X Y Z).app n (f, g)) =
      (eComp SSet (C := s.pt.Obj) ((leg K j ≫ forgetGraph.map (freeLift K s)).obj X)
        ((leg K j ≫ forgetGraph.map (freeLift K s)).obj Y)
        ((leg K j ≫ forgetGraph.map (freeLift K s)).obj Z)).app n
        (((leg K j ≫ forgetGraph.map (freeLift K s)).map X Y).app n f,
          ((leg K j ≫ forgetGraph.map (freeLift K s)).map Y Z).app n g) := by
    rw [leg_freeLift]
    intro X Y Z f g
    exact congrArg (fun a ↦ a.app n (f, g)) ((s.ι.app j).map_comp X Y Z)
  exact (h X Y Z f g).trans (congrArg
    (fun a ↦ a.app n (((leg K j).map X Y).app n f, ((leg K j).map Y Z).app n g))
    ((freeLift K s).map_comp ((leg K j).obj X) ((leg K j).obj Y) ((leg K j).obj Z))).symm

end DaggerModels.DaggerSimplicialCat.ColimitKernel
