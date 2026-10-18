import OriginalWholeBarStrictComparisonWeak
import OriginalWholeBarReedyComparisonWeak
import OriginalSimplicialCategoryBarReplacementFibreComparison

/-! The SAME original strict comparison is weak also for the older unchanged-base replacement. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open DaggerOriginalWholeBarRelativeReedy DaggerOriginalWholeBarReedyComparisonWeak
open DaggerOriginalWholeBarStrictComparisonWeak DaggerOriginalWholeBarReedyDiagonalFibration
open DaggerOriginalSimplicialCategoryBarReplacementFibreComparison
open DaggerOriginalSimplicialCategoryBarFibre DaggerOriginalSimplicialCategoryWholeBarFibreIso
open DaggerOriginalAmbientDaggerPiZeroGroupoid DaggerNativeSSetFibrationSquareFibreWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalWholeBarFixedBaseComparisonBridge
noncomputable section

def bridgeSquare (C : SimplicialCat.{u, u}) :
    CommSq (totalComparison C) (projectionReplacement C).i (projection C)
      ((projectionReplacement C).p ≫ baseComparison C) := ⟨by
  rw [original_projection_square, ← Category.assoc, (projectionReplacement C).fac]⟩

theorem bridge_hasLift (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C) :
    (bridgeSquare C).HasLift := by
  have : Cofibration (projectionReplacement C).i :=
    ((mem_trivialCofibrations_iff _).mp (projectionReplacement C).hi).1
  have := projectionReplacement_i_weak C
  have : Fibration (projection C) := projection_fibration C hC
  infer_instance

def bridge (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C) :
    (projectionReplacement C).Z ⟶
      DaggerNativeBisimplicialDiagonal.diagonalFunctor.obj (replacedBar C).left := by
  have := bridge_hasLift C hC
  exact (bridgeSquare C).lift

theorem bridge_i (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C) :
    (projectionReplacement C).i ≫ bridge C hC = totalComparison C := by
  have := bridge_hasLift C hC
  unfold bridge
  exact CommSq.fac_left _

theorem bridge_p (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C) :
    bridge C hC ≫ projection C = (projectionReplacement C).p ≫ baseComparison C := by
  have := bridge_hasLift C hC
  unfold bridge
  exact CommSq.fac_right _

theorem bridge_weak (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C) :
    WeakEquivalence (bridge C hC) := by
  have := projectionReplacement_i_weak C
  have := totalComparison_weak C
  exact weakEquivalence_of_precomp_of_fac (bridge_i C hC)

def fibreBridge (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C) (x : C.Obj) :
    replacementFibre C x ⟶ DaggerOriginalWholeBarReedyStrictFibre.fibre C x :=
  fibreMap (projectionReplacement C).p (projection C) (bridge C hC) (baseComparison C)
    (bridge_p C hC).symm (sourceVertexMap C x)
    (DaggerOriginalWholeBarReedyStrictFibre.point C x) rfl

theorem fibreBridge_weak (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C)
    (x : C.Obj) : WeakEquivalence (fibreBridge C hC x) := by
  have := projectionReplacement_p_fibration C
  have : Fibration (projection C) := projection_fibration C hC
  have := bridge_weak C hC
  have := baseComparison_weak C
  exact fibreMap_weakEquivalence _ _ _ _ _ _ _ _

theorem strictComparison_bridge (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (x : C.Obj) :
    strictFibreComparison C x ≫ fibreBridge C hC x =
      DaggerOriginalWholeBarReedyStrictFibre.strictComparison C x := by
  apply pullback.hom_ext
  · simp only [fibreBridge, Category.assoc, fibreMap_fst, strictFibreComparison,
      DaggerOriginalWholeBarReedyStrictFibre.strictComparison_fst]
    simp only [← Category.assoc]
    rw [pullback.lift_fst, Category.assoc, bridge_i]
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

theorem fixedBaseStrictComparison_weak (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (x : C.Obj) :
    WeakEquivalence (strictFibreComparison C x) := by
  have := strictComparison_weak C hC x
  have := fibreBridge_weak C hC x
  exact weakEquivalence_of_postcomp_of_fac (strictComparison_bridge C hC x)

end
end DaggerOriginalWholeBarFixedBaseComparisonBridge
