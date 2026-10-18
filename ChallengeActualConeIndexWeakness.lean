import ActualIteratedRightConeIndex

/-! Fix the dual Theorem A and both literal maps into and out of the original small cone index. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerActualIteratedRightConeIndex DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerOriginalCounitBNextConeEvaluationIndex
universe u
namespace DaggerActualConeIndexWeaknessChallenge
noncomputable section

def geometric {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map f))

/-- Apply the actual first projection to each whole chain, in the original target hom universe. -/
def firstMap (D : SimplicialCat.{u, u})
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    nerve (DoubleComma D a b) ⟶ nerve (SimplexIndex (rightConeSimplices D a b)) where
  app _ := ((toCones D a b).mapComposableArrows _).obj

/-- Apply the actual cone index to each whole chain, keeping every original coneMap operator. -/
def indexMap (D : SimplicialCat.{u, u})
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    nerve (SimplexIndex (rightConeSimplices D a b)) ⟶
      nerve (DaggerActualIteratedGadgetData.Over (coherentNerve.obj D) a b) where
  app _ := ((index D a b).mapComposableArrows _).obj

def statement : Prop :=
  (∀ (C D : Type u) [Category.{u} C] [Category.{u} D] (F : C ⥤ D),
    (∀ d : D, geometric (DaggerOriginalProductGadget.pointMap
      (nerve (StructuredArrow d F)))) → geometric (nerveMap F)) ∧
  (∀ (D : SimplicialCat.{u, u})
      (_hD : ∀ x y : D.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y))
      (a b : (coherentNerve.obj D).obj (op ⦋0⦌)), geometric (firstMap D a b)) ∧
  (∀ (D : SimplicialCat.{u, u})
      (_hD : ∀ x y : D.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y))
      (a b : (coherentNerve.obj D).obj (op ⦋0⦌)), geometric (indexMap D a b))

end
end DaggerActualConeIndexWeaknessChallenge
