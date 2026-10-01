import DaggerModels.DaggerSimplicialCategory

/-! Intersections of kernels of actual dagger simplicial functors.
The family may live in a larger universe than the original hom types. All
relations remain propositions, so taking hom quotients does not enlarge them.
This file does not construct a quotient or assert colimit existence. -/

open CategoryTheory MonoidalCategory

universe o v w

namespace DaggerModels.DaggerSimplicialCat.HomKernel

variable {C : DaggerSimplicialCat.{o, v}} {ι : Type w}
  {D : ι → DaggerSimplicialCat.{o, v}} (F : ∀ i, C ⟶ D i)

/-- Two actual hom simplices agree under every functor in the chosen family. -/
def rel (n : SimplexCategoryᵒᵖ) (X Y : C.Obj)
    (f g : (X ⟶[SSet.{v}] Y).obj n) : Prop :=
  ∀ i, ((F i).map X Y).app n f = ((F i).map X Y).app n g

theorem rel_refl (n : SimplexCategoryᵒᵖ) (X Y : C.Obj)
    (f : (X ⟶[SSet.{v}] Y).obj n) : rel F n X Y f f := fun _ ↦ rfl

theorem rel_symm (n : SimplexCategoryᵒᵖ) (X Y : C.Obj)
    {f g : (X ⟶[SSet.{v}] Y).obj n} (h : rel F n X Y f g) :
    rel F n X Y g f := fun i ↦ (h i).symm

theorem rel_trans (n : SimplexCategoryᵒᵖ) (X Y : C.Obj)
    {f g h : (X ⟶[SSet.{v}] Y).obj n} (h₁ : rel F n X Y f g)
    (h₂ : rel F n X Y g h) : rel F n X Y f h := fun i ↦ (h₁ i).trans (h₂ i)

/-- The same ordinary simplex operator preserves the kernel relation. -/
theorem rel_map {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) (X Y : C.Obj)
    {f g : (X ⟶[SSet.{v}] Y).obj n} (h : rel F n X Y f g) :
    rel F m X Y ((X ⟶[SSet.{v}] Y).map α f) ((X ⟶[SSet.{v}] Y).map α g) := by
  intro i
  calc
    ((F i).map X Y).app m ((X ⟶[SSet.{v}] Y).map α f) =
        (((F i).obj X) ⟶[SSet.{v}] ((F i).obj Y)).map α
          (((F i).map X Y).app n f) := congrFun (((F i).map X Y).naturality α) f
    _ = (((F i).obj X) ⟶[SSet.{v}] ((F i).obj Y)).map α
          (((F i).map X Y).app n g) := congrArg _ (h i)
    _ = ((F i).map X Y).app m ((X ⟶[SSet.{v}] Y).map α g) :=
      (congrFun (((F i).map X Y).naturality α) g).symm

/-- Original hom daggers preserve the relation and exchange both endpoints. -/
theorem rel_dagger (n : SimplexCategoryᵒᵖ) (X Y : C.Obj)
    {f g : (X ⟶[SSet.{v}] Y).obj n} (h : rel F n X Y f g) :
    rel F n Y X ((DaggerSimplicialStructure.dagger X Y).app n f)
      ((DaggerSimplicialStructure.dagger X Y).app n g) := by
  intro i
  calc
    ((F i).map Y X).app n ((DaggerSimplicialStructure.dagger X Y).app n f) =
        (DaggerSimplicialStructure.dagger ((F i).obj X) ((F i).obj Y)).app n
          (((F i).map X Y).app n f) :=
      (congrArg (fun a ↦ a.app n f) ((F i).map_dagger X Y)).symm
    _ = (DaggerSimplicialStructure.dagger ((F i).obj X) ((F i).obj Y)).app n
          (((F i).map X Y).app n g) := congrArg _ (h i)
    _ = ((F i).map Y X).app n ((DaggerSimplicialStructure.dagger X Y).app n g) :=
      congrArg (fun a ↦ a.app n g) ((F i).map_dagger X Y)

/-- Both composable factors can be changed within their respective relations. -/
theorem rel_comp (n : SimplexCategoryᵒᵖ) (X Y Z : C.Obj)
    {f f' : (X ⟶[SSet.{v}] Y).obj n} {g g' : (Y ⟶[SSet.{v}] Z).obj n}
    (hf : rel F n X Y f f') (hg : rel F n Y Z g g') :
    rel F n X Z ((eComp SSet X Y Z).app n (f, g))
      ((eComp SSet X Y Z).app n (f', g')) := by
  intro i
  calc
    ((F i).map X Z).app n ((eComp SSet X Y Z).app n (f, g)) =
        (eComp SSet ((F i).obj X) ((F i).obj Y) ((F i).obj Z)).app n
          (((F i).map X Y).app n f, ((F i).map Y Z).app n g) :=
      congrArg (fun a ↦ a.app n (f, g)) ((F i).map_comp X Y Z)
    _ = (eComp SSet ((F i).obj X) ((F i).obj Y) ((F i).obj Z)).app n
          (((F i).map X Y).app n f', ((F i).map Y Z).app n g') := by rw [hf i, hg i]
    _ = ((F i).map X Z).app n ((eComp SSet X Y Z).app n (f', g')) :=
      (congrArg (fun a ↦ a.app n (f', g')) ((F i).map_comp X Y Z)).symm

end DaggerModels.DaggerSimplicialCat.HomKernel
