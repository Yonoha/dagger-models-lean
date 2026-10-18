import NativeSimplicialReplacement
import OriginalCounitBNextConeRealizationFactorizationReconciled

/-! Fix the original Q-weighted simplex diagram and its literal realization augmentation. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitBNextConeRealizationFactorization
open DaggerNativeSimplicialReplacement
universe u
namespace DaggerActualWeightedConeCompositeChallenge
noncomputable section

abbrev Index (X : SSet.{u}) := ULiftHom.{u} (SimplexIndex X)

/-- Every original Q weight and every original cone simplex operator are fixed by the old diagram. -/
def diagram (X : SSet.{u}) : Index X ⥤ SSet.{u} :=
  ULiftHom.down.{0, u, u} ⋙ simplexDiagram X

/-- Use the entire original Q realization cocone, with only the hom universe lifted. -/
def augmentation (X : SSet.{u}) : diagram X ⟶
    (Functor.const (Index X)).obj (realization.obj X) :=
  Functor.whiskerLeft ULiftHom.down.{0, u, u} (simplexCocone X).ι

def toRealization (X : SSet.{u}) :
    DaggerBisimplicialDiagonal.diag (replacement (diagram X)) ⟶ realization.obj X :=
  diagonalAugmentation (diagram X) (augmentation X)

def geometric {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map f))

/-- Only the original local Kan hypothesis is supplied; the full original composite must be proved. -/
def statement : Prop :=
  ∀ (D : SimplicialCat.{u, u})
    (_hD : ∀ x y : D.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)),
    geometric (toRealization (rightConeSimplices D a b) ≫ coneRigidificationMap D a b)

end
end DaggerActualWeightedConeCompositeChallenge
