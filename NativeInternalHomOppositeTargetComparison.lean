import NativeInternalHomOppositeComparison

/-!
# The opposite internal-Hom comparison with the original target

Use the native target double-opposite isomorphism, and retain the exact
precomposition square after transporting that target.
-/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeInternalHomOppositeComparison
universe u
namespace DaggerNativeInternalHomOppositeTargetComparison
noncomputable section

/-- Compare with the same original target rather than its double opposite. -/
def targetComparisonIso (A Z : SSet.{u}) :
    ((ihom A).obj Z.op).op ≅ (ihom A.op).obj Z :=
  comparisonIso A Z.op ≪≫ (ihom A.op).mapIso (SSet.opFunctorCompOpFunctorIso.app Z)

/-- The target transport commutes with every original precomposition map. -/
theorem target_pre_naturality {A B : SSet.{u}} (f : A ⟶ B) (Z : SSet.{u}) :
    SSet.opFunctor.map ((MonoidalClosed.pre f).app Z.op) ≫
        (targetComparisonIso A Z).hom =
      (targetComparisonIso B Z).hom ≫
        (MonoidalClosed.pre (SSet.opFunctor.map f)).app Z := by
  dsimp only [targetComparisonIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, pre_naturality f Z.op, Category.assoc]
  have hn :
      (ihom B.op).map (SSet.opFunctorCompOpFunctorIso.app Z).hom ≫
          (MonoidalClosed.pre (SSet.opFunctor.map f)).app Z =
        (MonoidalClosed.pre (SSet.opFunctor.map f)).app Z.op.op ≫
          (ihom A.op).map (SSet.opFunctorCompOpFunctorIso.app Z).hom :=
    (MonoidalClosed.pre (SSet.opFunctor.map f)).naturality
      (SSet.opFunctorCompOpFunctorIso.hom.app Z)
  simpa only [Category.assoc] using
    congrArg (fun k ↦ (comparisonIso B Z.op).hom ≫ k) hn.symm

end
end DaggerNativeInternalHomOppositeTargetComparison
