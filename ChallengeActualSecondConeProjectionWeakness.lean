import ActualIteratedRightConeIndex

/-! Fix the original simplex-index nerve and the actual second comma projection. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels OrdinaryRigidification DaggerActualIteratedRightConeIndex
universe u
namespace DaggerActualSecondConeProjectionWeaknessChallenge
noncomputable section

def geometric {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map f))

def statement : Prop :=
  (∀ X : SSet.{u}, geometric (toUnit X) →
    geometric (toUnit (nerve (CostructuredArrow uliftYoneda.{u, 0, 0} X)))) ∧
  (∀ (D : SimplicialCat.{u, u})
      (a b : (coherentNerve.obj D).obj (op ⦋0⦌))
      (Q : DaggerActualIteratedGadgetShift.FibrantOver D a b),
    geometric (DaggerOriginalProductGadget.pointMap
      (nerve (CostructuredArrow (toPositive D a b) Q)))) ∧
  (∀ (D : SimplicialCat.{u, u}) (a b : (coherentNerve.obj D).obj (op ⦋0⦌)),
    geometric (nerveMap (toPositive D a b)))

end
end DaggerActualSecondConeProjectionWeaknessChallenge
