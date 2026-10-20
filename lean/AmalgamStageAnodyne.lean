import AmalgamZeroStage
import AmalgamRankFiltration
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-! Existing cobase and transfinite closure applied to the original rank stages.
The exceptional NN tail starts at one; its zero-to-one map is not asserted anodyne. -/

open CategoryTheory Limits CartesianMonoidalCategory HomotopicalAlgebra
open DaggerModels DaggerAmalgamPresentation DaggerAmalgamUnitBoundary
open DaggerAmalgamRankFiltration
open scoped SSet.modelCategoryQuillen

universe u

set_option autoImplicit false

namespace DaggerAmalgamSuccessor

noncomputable section

variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)
variable (hB : SSet.KanComplex.W
  (TopCat.toSSet.map (SSet.toTop.map (toUnit (b ⟶[SSet] b)))))

include hB in
theorem successorOO_anodyne (a d : C.Obj) (n : ℕ) :
    SSet.anodyneExtensions (successorOO C B x b a d n) :=
  SSet.anodyneExtensions.of_isPushout (successorOO_isPushout C B x b a d n)
    (boundaryOO_anodyne C B x b hB a d n)

include hB in
theorem successorON_anodyne (a : C.Obj) (w : B.Obj) (hw : w ≠ b) (n : ℕ) :
    SSet.anodyneExtensions (successorON C B x b a w n) :=
  SSet.anodyneExtensions.of_isPushout (successorON_isPushout C B x b a w hw n)
    (boundaryON_anodyne C B x b hB a w n)

include hB in
theorem successorNO_anodyne (z : B.Obj) (d : C.Obj) (hz : z ≠ b) (n : ℕ) :
    SSet.anodyneExtensions (successorNO C B x b z d n) :=
  SSet.anodyneExtensions.of_isPushout (successorNO_isPushout C B x b z d hz n)
    (boundaryNO_anodyne C B x b hB z d n)

include hB in
theorem successorNN_anodyne (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) (n : ℕ) :
    SSet.anodyneExtensions (successorNN C B x b z w (n + 1)) :=
  SSet.anodyneExtensions.of_isPushout (successorNN_isPushout C B x b z w hz hw (n + 1))
    (boundaryNN_anodyne C B x b hB z w n)

/-- The existing full original colimit data turns actual successor hypotheses into the same ι. -/
theorem stage_ι_anodyne (shift : Bool) (k : ℕ) (a d : Objects C B x b)
    (hsucc : ∀ n, SSet.anodyneExtensions
      (SSet.Subcomplex.homOfLE (stage_monotone C B x b shift a d (Nat.le_succ (k + n))))) :
    SSet.anodyneExtensions (stage C B x b shift k a d).ι := by
  apply SSet.anodyneExtensions.transfiniteCompositionsOfShape_le ℕ _
  refine ⟨{ toTransfiniteCompositionOfShape := transfiniteComposition C B x b shift k a d
            map_mem := ?_ }⟩
  intro n _
  exact hsucc n

include hB in
theorem oldOld_ι_anodyne (a d : C.Obj) :
    SSet.anodyneExtensions (oldOldStage C B x b 0 a d).ι := by
  apply stage_ι_anodyne C B x b false 0
  intro n
  exact successorOO_anodyne C B x b hB a d (0 + n)

include hB in
theorem oldNew_ι_anodyne (a : C.Obj) (w : B.Obj) (hw : w ≠ b) :
    SSet.anodyneExtensions (oldNewStage C B x b 0 a w).ι := by
  apply stage_ι_anodyne C B x b true 0
  intro n
  exact successorON_anodyne C B x b hB a w hw (0 + n)

include hB in
theorem newOld_ι_anodyne (z : B.Obj) (d : C.Obj) (hz : z ≠ b) :
    SSet.anodyneExtensions (newOldStage C B x b 0 z d).ι := by
  apply stage_ι_anodyne C B x b true 0
  intro n
  exact successorNO_anodyne C B x b hB z d hz (0 + n)

include hB in
theorem newNew_one_ι_anodyne (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) :
    SSet.anodyneExtensions (newNewStage C B x b 1 z w).ι := by
  apply stage_ι_anodyne C B x b true 1
  intro n
  change SSet.anodyneExtensions (successorNN C B x b z w (1 + n))
  rw [Nat.add_comm 1 n]
  exact successorNN_anodyne C B x b hB z w hz hw n

include hB in
/-- The original left factor functor has anodyne Hom maps, with every old endpoint retained. -/
theorem leftLeg_map_anodyne (a d : C.Obj) :
    SSet.anodyneExtensions ((leftLeg C B x b).map a d) := by
  have : IsIso (evaluationStageOO C B x b a d 0) :=
    evaluationStageOO_zero_isIso C B x b a d
  rw [← evaluationOO_zero, ← evaluationStageOO_ι C B x b a d 0]
  exact SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _)
    (oldOld_ι_anodyne C B x b hB a d)

include hB in
theorem leftLeg_map_trivial_geometric (a d : C.Obj) :
    trivialCofibrations SSet.{u} ((leftLeg C B x b).map a d) ∧
      SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map ((leftLeg C B x b).map a d))) :=
  anodyne_trivial_geometric _ (leftLeg_map_anodyne C B x b hB a d)

end
end DaggerAmalgamSuccessor
