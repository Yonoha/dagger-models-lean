import OriginalNerveLocalWeakPreservation
import OriginalOrdinaryLocalKanReplacementHomReconciled

/-! The same original ordinary local Kan replacement is weak on its whole diagonal nerve. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open OriginalOrdinaryLocalKanReplacement OriginalOrdinaryLocalKanReplacementHom
open DaggerOriginalSimplicialCategoryDiagonalNerve
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalLocalKanReplacementDiagonalWeak
noncomputable section

theorem unit_hom_weak (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    WeakEquivalence ((unit.app C).map x y) := by
  apply (SSet.modelCategoryQuillen.weakEquivalence_iff _).mpr
  apply (TopCat.modelCategory.weakEquivalence_iff _).mpr
  exact unit_hom_geometric C x y

theorem unit_diagonal_weak (C : SimplicialCat.{u, u}) :
    WeakEquivalence (diagonalNerveFunctor.map (unit.app C)) :=
  DaggerOriginalNerveLocalWeakPreservation.diagonalNerveMap_weak
    (unit.app C) (unit_obj_bijective C) (unit_hom_weak C)

theorem unit_diagonal_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    diagonalNerveFunctor.map (unit.app C) ≫ diagonalNerveFunctor.map (replacement.map F) =
      diagonalNerveFunctor.map F ≫ diagonalNerveFunctor.map (unit.app D) := by
  rw [← diagonalNerveFunctor.map_comp, ← diagonalNerveFunctor.map_comp]
  exact congrArg diagonalNerveFunctor.map (unit.naturality F).symm

end
end DaggerOriginalLocalKanReplacementDiagonalWeak
