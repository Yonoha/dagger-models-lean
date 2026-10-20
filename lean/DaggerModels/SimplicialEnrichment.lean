import DaggerModels.SimplicialCat
import Mathlib.CategoryTheory.EqToHom

/-!
# Simplicial enrichment in each degree

Every simplicial degree of an enriched category gives an ordinary category on
the same objects. Simplicial operators give identity-on-objects functors.
These are the degreewise categories used by the free path construction.
-/

open CategoryTheory MonoidalCategory

universe o o₁ v

namespace DaggerModels.SimplicialEnrichment

/-- The object type of a simplicial category, viewed in a specified degree. -/
def At (C : Type o) (_n : SimplexCategoryᵒᵖ) : Type o := C

variable (C : Type o) [EnrichedCategory SSet.{v} C]

instance atCategory (n : SimplexCategoryᵒᵖ) : Category (At C n) where
  Hom X Y := (EnrichedCategory.Hom (V := SSet.{v}) (C := C) X Y).obj n
  id X := (eId SSet (show C from X)).app n PUnit.unit
  comp {X Y Z} f g := (eComp SSet (show C from X) Y Z).app n (f, g)
  id_comp {X Y} f := by
    exact congrArg (fun p ↦ p.app n f) (e_id_comp SSet (show C from X) Y)
  comp_id {X Y} f := by
    exact congrArg (fun p ↦ p.app n f) (e_comp_id SSet (show C from X) Y)
  assoc {W X Y Z} f g h := by
    exact congrArg (fun p ↦ p.app n (f, g, h)) (e_assoc SSet (show C from W) X Y Z)

/-- A simplicial operator acts as a functor, retaining all object labels. -/
def map {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) : At C n ⥤ At C m where
  obj X := X
  map {X Y} f := (EnrichedCategory.Hom (V := SSet.{v}) (C := C) X Y).map α f
  map_id X := by
    exact (congrArg (fun p ↦ p PUnit.unit) ((eId SSet (show C from X)).naturality α)).symm
  map_comp {X Y Z} f g := by
    exact (congrArg (fun p ↦ p (f, g))
      ((eComp SSet (show C from X) Y Z).naturality α)).symm

@[simp] theorem map_id (n : SimplexCategoryᵒᵖ) : map C (𝟙 n) = 𝟭 (At C n) := by
  apply CategoryTheory.Functor.ext
  · intro X Y f
    simp [map]
  · intro X
    rfl

@[simp] theorem map_comp {n m k : SimplexCategoryᵒᵖ} (α : n ⟶ m) (β : m ⟶ k) :
    map C (α ≫ β) = map C α ⋙ map C β := by
  apply CategoryTheory.Functor.ext
  · intro X Y f
    simp [map]
  · intro X
    rfl

variable {C} {D : Type o₁} [EnrichedCategory SSet.{v} D]

/-- An enriched functor gives an ordinary functor in every simplicial degree. -/
def functor (F : EnrichedFunctor SSet.{v} C D) (n : SimplexCategoryᵒᵖ) :
    At C n ⥤ At D n where
  obj := F.obj
  map {X Y} f := (F.map X Y).app n f
  map_id X := congrArg (fun p ↦ p.app n PUnit.unit) (F.map_id X)
  map_comp {X Y Z} f g := congrArg (fun p ↦ p.app n (f, g)) (F.map_comp X Y Z)

/-- Degreewise functors commute with each actual simplex operator. -/
theorem functor_naturality (F : EnrichedFunctor SSet.{v} C D)
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    functor F n ⋙ map D α = map C α ⋙ functor F m := by
  apply CategoryTheory.Functor.ext
  · intro X Y f
    simpa [functor, map] using
      (congrArg (fun p ↦ p f) ((F.map X Y).naturality α)).symm
  · intro X
    rfl

end DaggerModels.SimplicialEnrichment
