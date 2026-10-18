import AmalgamEvaluationCollapse

/-! Whole simplicial morphism equations for the original low-rank collapse.
The complete source products, including their empty coordinate factors, are unchanged. -/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory DaggerModels
open DaggerAmalgamPresentation DaggerAmalgamPaddedClassification
open DaggerAmalgamUnitBoundary DaggerAmalgamCollapse

universe u

set_option autoImplicit false

namespace DaggerAmalgamSuccessor

noncomputable section

variable (C B : DaggerSimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem evaluationON_zero_collapse (a : C.Obj) (w : B.Obj) :
    evaluationON C.toSimplicialCat B.toSimplicialCat x b a w 0 ≫ homON C B x b a w =
      fst (a ⟶[SSet] x)
        (finitePower (b ⟶[SSet] b) 0 ⊗ (finitePower (x ⟶[SSet] x) 0 ⊗ (b ⟶[SSet] w))) := by
  ext q h
  exact ordinary_decodeON_zero C B x b q a w h

theorem evaluationNO_zero_collapse (z : B.Obj) (d : C.Obj) :
    evaluationNO C.toSimplicialCat B.toSimplicialCat x b z d 0 ≫ homNO C B x b z d =
      snd (z ⟶[SSet] b)
        (finitePower (x ⟶[SSet] x) 0 ⊗ (finitePower (b ⟶[SSet] b) 0 ⊗ (x ⟶[SSet] d))) ≫
      snd (finitePower (x ⟶[SSet] x) 0)
        (finitePower (b ⟶[SSet] b) 0 ⊗ (x ⟶[SSet] d)) ≫
      snd (finitePower (b ⟶[SSet] b) 0) (x ⟶[SSet] d) := by
  ext q h
  exact ordinary_decodeNO_zero C B x b q z d h

/-- The actual NN1 evaluation followed by the same collapse is the central projection. -/
theorem evaluationNN_one_collapse (z w : B.Obj) :
    evaluationNN C.toSimplicialCat B.toSimplicialCat x b z w 1 ≫ homNN C B x b z w =
      snd (z ⟶[SSet] b)
        (finitePower (x ⟶[SSet] x) 1 ⊗ (finitePower (b ⟶[SSet] b) 0 ⊗ (b ⟶[SSet] w))) ≫
      fst (finitePower (x ⟶[SSet] x) 1)
        (finitePower (b ⟶[SSet] b) 0 ⊗ (b ⟶[SSet] w)) ≫
      powerEval (x ⟶[SSet] x) 1 0 := by
  ext q h
  exact ordinary_decodeNN_one C B x b q z w h

end
end DaggerAmalgamSuccessor
