import NativeOppositeLeftMappingIso
import NativeKanSimplicialOpposite

/-! The SAME literal right-cone mapping space is Kan for EVERY original quasi-category. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerActualGeneralRightConeMapping
open DaggerNativeRightConeSimplexPresentation
open DaggerNativeOppositeLeftMappingSimplex
open DaggerActualQuasicategoryMappingFibres
open DaggerNativeQuasicategoryOpposite DaggerNativeKanSimplicialOpposite
universe u
namespace DaggerActualGeneralRightConeKan
noncomputable section
variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))

def comparisonIso : rightMapping X a b ≅ oppositeLeft X a b :=
  presentationIso X a b ≪≫ (DaggerNativeOppositeLeftMappingSimplex.comparisonIso X a b).symm

theorem inv_simplex_value (q : SimplexCategoryᵒᵖ) (s : (oppositeLeft X a b).obj q) :
    DaggerOriginalCounitRightCone.simplexIncl q.unop.len ≫
        ((comparisonIso X a b).inv.app q s).val =
      SSet.yonedaEquiv.symm (raw X a b q s) := by
  change DaggerOriginalCounitRightCone.simplexIncl q.unop.len ≫
      coneOfSimplex X a b q ((DaggerNativeOppositeLeftMappingSimplex.forward X a b).app q s) = _
  exact simplex_coneOfSimplex X a b q
    ((DaggerNativeOppositeLeftMappingSimplex.forward X a b).app q s)

theorem hom_simplex_value (q : SimplexCategoryᵒᵖ) (s : (rightMapping X a b).obj q) :
    raw X a b q ((comparisonIso X a b).hom.app q s) =
      SSet.yonedaEquiv (DaggerOriginalCounitRightCone.simplexIncl q.unop.len ≫ s.val) := by
  have h := inv_simplex_value X a b q ((comparisonIso X a b).hom.app q s)
  have hh := congrFun (NatTrans.congr_app (comparisonIso X a b).hom_inv_id q) s
  change ((comparisonIso X a b).inv.app q ((comparisonIso X a b).hom.app q s)) = s at hh
  rw [hh] at h
  apply SSet.yonedaEquiv.symm.injective
  rw [Equiv.symm_apply_apply]
  exact h.symm

theorem oppositeLeft_kan [X.Quasicategory] : (oppositeLeft X a b).KanComplex := by
  have : X.op.Quasicategory := quasicategory_op X
  have : (leftMapping X.op (SSet.opObjEquiv.symm b)
      (SSet.opObjEquiv.symm a)).KanComplex := leftMapping_kan X.op _ _
  exact kan_op _

theorem rightMapping_kan [X.Quasicategory] : (rightMapping X a b).KanComplex := by
  have : (oppositeLeft X a b).KanComplex := oppositeLeft_kan X a b
  exact kan_of_iso (comparisonIso X a b).symm

end
end DaggerActualGeneralRightConeKan
