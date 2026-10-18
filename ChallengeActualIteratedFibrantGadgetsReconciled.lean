import ActualIteratedGadgetData
import OriginalCounitBNextConeEvaluationIndexReconciled
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.AlgebraicTopology.Quasicategory.Basic

/-! The literal original endpoints, entire extension maps, and all arrows are part of the task. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels OrdinaryRigidification DaggerActualIteratedGadgetData
open DaggerOriginalCounitBNextConeEvaluationIndex
universe u
namespace DaggerActualIteratedFibrantGadgetsChallenge
noncomputable section

def geometric {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map f))

def positive (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) : ObjectProperty (Over X a b) :=
  fun P ↦ 0 < P.code.level

def statement : Prop :=
  (∀ P : Code, geometric (toUnit
      (DaggerChosenRigidificationNecklace.RV (space.{u} P) (alpha P) ⟶[SSet.{u}]
        DaggerChosenRigidificationNecklace.RV (space P) (omega P))) ∧
    (0 < P.level → SSet.Quasicategory (space.{u} P))) ∧
  (∀ (D : SimplicialCat.{u, u})
      (_hD : ∀ x y : D.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y))
      (a b : (coherentNerve.obj D).obj (op ⦋0⦌)),
    ∃ r : OriginalOrdinaryLocalKanReplacement.replacement.obj D ⟶ D,
    ∃ _hr : OriginalOrdinaryLocalKanReplacement.unit.app D ≫ r = 𝟙 D,
    ∃ G : Over (coherentNerve.obj D) a b ⥤ Over (coherentNerve.obj D) a b,
    ∃ η : 𝟭 (Over (coherentNerve.obj D) a b) ⟶ G,
      (∀ P, (G.obj P).code = ⟨P.code.base, P.code.level + 1⟩) ∧
      (∀ P, HEq (G.obj P).map (DaggerActualFibrantGadgetData.extension D r P.map)) ∧
      (∀ P, HEq (η.app P).hom.map (DaggerActualFibrantGadgetData.unit.app (space P.code))) ∧
      (∀ (P Q : Over (coherentNerve.obj D) a b) (f : P ⟶ Q),
        HEq (G.map f).hom.map (DaggerActualFibrantGadgetData.gadget.map f.hom.map)) ∧
      geometric (nerveMap G) ∧ geometric (nerveMap ((positive (coherentNerve.obj D) a b).ι))) ∧
  (∀ (P : BaseCode) (k : ℕ),
    (rightConeSimplices
      (OriginalOrdinaryLocalKanReplacement.replacement.obj (rigidification.obj (spaceAt.{u} P k)))
      (alphaAt P (k + 1)) (omegaAt P (k + 1))).KanComplex ∧
    geometric (toUnit (rightConeSimplices
      (OriginalOrdinaryLocalKanReplacement.replacement.obj (rigidification.obj (spaceAt.{u} P k)))
      (alphaAt P (k + 1)) (omegaAt P (k + 1)))))

end
end DaggerActualIteratedFibrantGadgetsChallenge
