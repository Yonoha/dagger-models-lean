import AmalgamFirstStageSquare

/-! Geometric weak equivalence of the SAME original collapse on the exceptional NN1 stage. -/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory DaggerModels
open DaggerAmalgamUnitBoundary DaggerAmalgamLowRankProducts DaggerAmalgamCollapse
open DaggerAmalgamRankFiltration

universe u

set_option autoImplicit false

namespace DaggerAmalgamSuccessor

noncomputable section

variable (C B : DaggerSimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

/-- Restrict the original Hom collapse, keeping the same rank-one apex. -/
def firstStageComparisonNN (z w : B.Obj) :
    (newNewStage C.toSimplicialCat B.toSimplicialCat x b 1 z w : SSet.{u}) ⟶
      (x ⟶[SSet] x) :=
  (newNewStage C.toSimplicialCat B.toSimplicialCat x b 1 z w).ι ≫ homNN C B x b z w

theorem firstStageOldNN_comparison (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) :
    firstStageOldNN C.toSimplicialCat B.toSimplicialCat x b z w hz hw ≫
        firstStageComparisonNN C B x b z w = toUnit (z ⟶[SSet] w) ≫ eId SSet x := by
  calc
    _ = evaluationNN C.toSimplicialCat B.toSimplicialCat x b z w 0 ≫
        homNN C B x b z w := by ext q v; rfl
    _ = _ := evaluationNN_zero_collapse C B x b z w

theorem firstStageProductNN_comparison (z w : B.Obj) :
    firstStageProductNN C.toSimplicialCat B.toSimplicialCat x b z w ≫
        firstStageComparisonNN C B x b z w =
      fst ((z ⟶[SSet] b) ⊗ (x ⟶[SSet] x)) (b ⟶[SSet] w) ≫
        snd (z ⟶[SSet] b) (x ⟶[SSet] x) := by
  calc
    _ = (oneNNIso C.toSimplicialCat B.toSimplicialCat x b z w).inv ≫
        evaluationNN C.toSimplicialCat B.toSimplicialCat x b z w 1 ≫
        homNN C B x b z w := by ext q v; rfl
    _ = _ := oneNNIso_inv_evaluation_collapse C B x b z w

/-- Every supplied pair of endpoint points is retained; no C-loop Kan or W premise is used. -/
theorem firstStageComparisonNN_geometric (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b)
    (l : 𝟙_ SSet.{u} ⟶ (z ⟶[SSet] b)) (r : 𝟙_ SSet.{u} ⟶ (b ⟶[SSet] w))
    (hL : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (toUnit (z ⟶[SSet] b)))))
    (hR : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (toUnit (b ⟶[SSet] w)))))
    (hB₀ : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (toUnit (z ⟶[SSet] w))))) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (firstStageComparisonNN C B x b z w))) :=
  DaggerAmalgamFirstStage.middle_supplied_geometric (eId SSet x) l r (eComp SSet z b w)
    (firstStageOldNN C.toSimplicialCat B.toSimplicialCat x b z w hz hw)
    (firstStageProductNN C.toSimplicialCat B.toSimplicialCat x b z w)
    (firstStageNN_isPushout C.toSimplicialCat B.toSimplicialCat x b z w hz hw)
    (firstStageComparisonNN C B x b z w)
    (firstStageOldNN_comparison C B x b z w hz hw)
    (firstStageProductNN_comparison C B x b z w) hL hR hB₀

end
end DaggerAmalgamSuccessor
