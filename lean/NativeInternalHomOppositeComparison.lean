import Mathlib.AlgebraicTopology.SimplicialSet.HoFunctorMonoidal
import Mathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.CategoryTheory.Monoidal.Closed.Functor

/-!
# Actual internal Hom under simplicial opposite

Use Mathlib's exponential comparison and its exact precomposition naturality.
Its invertibility follows from the native opposite equivalence and the existing
Cartesian-closed-functor theorem for a full faithful right adjoint.
-/
set_option autoImplicit false
open CategoryTheory Limits
universe u
namespace DaggerNativeInternalHomOppositeComparison
noncomputable section

local instance opFunctorEquivalence : SSet.opFunctor.{u}.IsEquivalence :=
  show SSet.opEquivalence.functor.IsEquivalence by infer_instance

local instance opFunctorPreservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) SSet.opFunctor.{u} := by
  infer_instance

local instance opFunctorClosed : MonoidalClosedFunctor SSet.opFunctor.{u} :=
  cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts SSet.opFunctor
    SSet.opEquivalence.toAdjunction

/-- The literal exponential comparison on the actual opposite functor. -/
def comparisonHom (A Z : SSet.{u}) :
    ((ihom A).obj Z).op ⟶ (ihom A.op).obj Z.op :=
  (expComparison SSet.opFunctor A).natTrans.app Z

/-- The native comparison is an isomorphism for every source and every target. -/
def comparisonIso (A Z : SSet.{u}) :
    ((ihom A).obj Z).op ≅ (ihom A.op).obj Z.op :=
  asIso ((expComparison SSet.opFunctor A).natTrans.app Z)

/-- Its forward map is exactly the native comparison used in the precomposition square. -/
theorem comparisonIso_hom (A Z : SSet.{u}) :
    (comparisonIso A Z).hom = comparisonHom A Z := rfl

/-- Every actual precomposition map commutes with the same native opposite comparison. -/
theorem pre_naturality {A B : SSet.{u}} (f : A ⟶ B) (Z : SSet.{u}) :
    SSet.opFunctor.map ((MonoidalClosed.pre f).app Z) ≫ (comparisonIso A Z).hom =
      (comparisonIso B Z).hom ≫
        (MonoidalClosed.pre (SSet.opFunctor.map f)).app Z.op := by
  exact (congrArg (fun α ↦ α.natTrans.app Z)
    (expComparison_whiskerLeft SSet.opFunctor f)).symm

end
end DaggerNativeInternalHomOppositeComparison
