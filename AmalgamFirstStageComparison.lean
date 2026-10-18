import AmalgamLowRankCollapse
import AmalgamLowRankProducts

/-! The SAME original collapse after the complete accepted product isomorphisms.
The NN1 equation is the literal second leg required by the original first-stage helper. -/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory DaggerModels
open DaggerAmalgamPresentation DaggerAmalgamPaddedClassification
open DaggerAmalgamUnitBoundary DaggerAmalgamCollapse DaggerAmalgamLowRankProducts

universe u

set_option autoImplicit false

namespace DaggerAmalgamSuccessor

noncomputable section

variable (C B : DaggerSimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem zeroONIso_inv_evaluation_collapse (a : C.Obj) (w : B.Obj) :
    (zeroONIso C.toSimplicialCat B.toSimplicialCat x b a w).inv ≫
        evaluationON C.toSimplicialCat B.toSimplicialCat x b a w 0 ≫
        homON C B x b a w = fst (a ⟶[SSet] x) (b ⟶[SSet] w) := by
  ext q v
  exact ordinary_decodeON_zero C B x b q a w
    ((zeroONIso C.toSimplicialCat B.toSimplicialCat x b a w).inv.app q v)

theorem zeroNOIso_inv_evaluation_collapse (z : B.Obj) (d : C.Obj) :
    (zeroNOIso C.toSimplicialCat B.toSimplicialCat x b z d).inv ≫
        evaluationNO C.toSimplicialCat B.toSimplicialCat x b z d 0 ≫
        homNO C B x b z d = snd (z ⟶[SSet] b) (x ⟶[SSet] d) := by
  ext q v
  exact ordinary_decodeNO_zero C B x b q z d
    ((zeroNOIso C.toSimplicialCat B.toSimplicialCat x b z d).inv.app q v)

/-- No weak-equivalence hypothesis is used to identify this actual comparison-map leg. -/
theorem oneNNIso_inv_evaluation_collapse (z w : B.Obj) :
    (oneNNIso C.toSimplicialCat B.toSimplicialCat x b z w).inv ≫
        evaluationNN C.toSimplicialCat B.toSimplicialCat x b z w 1 ≫
        homNN C B x b z w =
      fst ((z ⟶[SSet] b) ⊗ (x ⟶[SSet] x)) (b ⟶[SSet] w) ≫
        snd (z ⟶[SSet] b) (x ⟶[SSet] x) := by
  ext q v
  exact ordinary_decodeNN_one C B x b q z w
    ((oneNNIso C.toSimplicialCat B.toSimplicialCat x b z w).inv.app q v)

end
end DaggerAmalgamSuccessor
