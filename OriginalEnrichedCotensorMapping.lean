import NativeCoherentCotensorConstants

/-! The FULL mapping SSet of original enriched functors; all object functions are retained. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalCotensorPrecompositionWeak DaggerNativeCoherentCotensorConstants
universe u
namespace DaggerOriginalEnrichedCotensorMapping
noncomputable section

/-- Every simplex is an entire original enriched functor into the actual simplex cotensor. -/
def mapping (A C : SimplicialCat.{u, u}) : SSet.{u} where
  obj q := ULift (A ⟶ originalCotensor (SSet.stdSimplex.obj q.unop) C)
  map a F := ⟨F.down ≫ restrictionFunctor (SSet.stdSimplex.map a.unop) C⟩
  map_id q := by
    funext F
    apply ULift.ext
    change F.down ≫ restrictionFunctor (SSet.stdSimplex.map (𝟙 q).unop) C = F.down
    rw [unop_id, CategoryTheory.Functor.map_id, restriction_id, Category.comp_id]
  map_comp a b := by
    funext F
    apply ULift.ext
    change F.down ≫ restrictionFunctor (SSet.stdSimplex.map (a ≫ b).unop) C =
      (F.down ≫ restrictionFunctor (SSet.stdSimplex.map a.unop) C) ≫
        restrictionFunctor (SSet.stdSimplex.map b.unop) C
    rw [unop_comp, SSet.stdSimplex.map_comp, restriction_comp, Category.assoc]

/-- Precompose every whole original enriched functor, without fixing its object function. -/
def pre {A B : SimplicialCat.{u, u}} (p : A ⟶ B) (C : SimplicialCat.{u, u}) :
    mapping B C ⟶ mapping A C where
  app _ F := ⟨p ≫ F.down⟩
  naturality _ _ _ := by
    funext F
    apply ULift.ext
    exact (Category.assoc p F.down _).symm

/-- The native identity acts identically on the entire mapping SSet. -/
theorem pre_id (A C : SimplicialCat.{u, u}) : pre (𝟙 A) C = 𝟙 (mapping A C) := by
  apply NatTrans.ext
  funext q F
  apply ULift.ext
  exact Category.id_comp F.down

/-- Source composition retains the entire original enriched functor. -/
theorem pre_comp {A B D : SimplicialCat.{u, u}} (p : A ⟶ B) (r : B ⟶ D)
    (C : SimplicialCat.{u, u}) : pre (p ≫ r) C = pre r C ≫ pre p C := by
  apply NatTrans.ext
  funext q F
  apply ULift.ext
  exact Category.assoc p r F.down

end
end DaggerOriginalEnrichedCotensorMapping
