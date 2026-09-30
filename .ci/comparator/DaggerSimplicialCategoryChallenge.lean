import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Enriched.Opposite

/-! Part I `bg.def.dagger-scat`: full mapping-space dagger and typed opposite functors.
These are specification obligations; no monadicity or model structure is asserted. -/
set_option warningAsError false
open CategoryTheory MonoidalCategory BraidedCategory Opposite Simplicial
universe o v
namespace DaggerModels

noncomputable instance sSetBraidedCategory : BraidedCategory SSet.{v} :=
  .ofCartesianMonoidalCategory

class DaggerSimplicialStructure (C : Type o) [EnrichedCategory SSet.{v} C] where
  dagger (X Y : C) : (X ⟶[SSet.{v}] Y) ⟶ (Y ⟶[SSet.{v}] X)
  dagger_involutive (X Y : C) : dagger X Y ≫ dagger Y X = 𝟙 _
  dagger_id (X : C) : eId SSet X ≫ dagger X X = eId SSet X
  dagger_comp (X Y Z : C) :
    eComp SSet X Y Z ≫ dagger X Z =
      (dagger X Y ⊗ₘ dagger Y Z) ≫
        (β_ (Y ⟶[SSet.{v}] X) (Z ⟶[SSet.{v}] Y)).hom ≫ eComp SSet Z Y X

namespace DaggerSimplicialStructure
variable {C : Type o} [EnrichedCategory SSet.{v} C] [DaggerSimplicialStructure C]

def daggerSimplex {X Y : C} {n : ℕ} (x : (X ⟶[SSet.{v}] Y) _⦋n⦌) :
    (Y ⟶[SSet.{v}] X) _⦋n⦌ := (dagger X Y).app (op ⦋n⦌) x

@[simp] theorem daggerSimplex_involutive {X Y : C} {n : ℕ}
    (x : (X ⟶[SSet.{v}] Y) _⦋n⦌) :
    daggerSimplex (daggerSimplex x) = x := by sorry

/-- The same simplex operator acts on both sides; its order is not reversed. -/
theorem daggerSimplex_map {X Y : C} {n k : ℕ} (α : ⦋k⦌ ⟶ ⦋n⦌)
    (x : (X ⟶[SSet.{v}] Y) _⦋n⦌) :
    daggerSimplex ((X ⟶[SSet.{v}] Y).map α.op x) =
      (Y ⟶[SSet.{v}] X).map α.op (daggerSimplex x) := by sorry

theorem dagger_id_app (X : C) (n : SimplexCategoryᵒᵖ) :
    (dagger X X).app n ((eId SSet X).app n PUnit.unit) =
      (eId SSet X).app n PUnit.unit := by sorry

theorem dagger_comp_app (X Y Z : C) (n : SimplexCategoryᵒᵖ)
    (f : (X ⟶[SSet.{v}] Y).obj n) (g : (Y ⟶[SSet.{v}] Z).obj n) :
    (dagger X Z).app n ((eComp SSet X Y Z).app n (f, g)) =
      (eComp SSet Z Y X).app n ((dagger Y Z).app n g, (dagger X Y).app n f) := by sorry

def daggerFunctor : EnrichedFunctor SSet.{v} C Cᵒᵖ where
  obj := Opposite.op
  map := dagger
  map_id := dagger_id
  map_comp X Y Z := dagger_comp X Y Z

def daggerInverse : EnrichedFunctor SSet.{v} Cᵒᵖ C where
  obj := Opposite.unop
  map X Y := dagger Y.unop X.unop
  map_id X := dagger_id X.unop
  map_comp X Y Z := by
    change (β_ _ _).hom ≫ eComp SSet Z.unop Y.unop X.unop ≫
      dagger Z.unop X.unop = _
    rw [dagger_comp, ← braiding_naturality_assoc]
    simp

@[simp] theorem daggerFunctor_comp_inverse :
    (daggerFunctor (C := C)).comp SSet daggerInverse = EnrichedFunctor.id SSet C := by sorry

@[simp] theorem daggerInverse_comp_functor :
    (daggerInverse (C := C)).comp SSet daggerFunctor =
      EnrichedFunctor.id SSet Cᵒᵖ := by sorry

end DaggerSimplicialStructure
end DaggerModels
