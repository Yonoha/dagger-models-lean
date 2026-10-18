import OriginalSingularStrictPaths
import TopCatModelCategory.TopCat.Homotopy

/-!
# Original singular paths and realized cylinders for arbitrary simplicial parameters

The native internal-hom adjunction, realization-singular adjunction, and the existing
realization-times-one-simplex isomorphism give an actual hom equivalence for every original
simplicial parameter. Applying Yoneda makes this an equivalence in every simplicial degree.
No restriction to fixed endpoints or resulting simplicial path-space isomorphism is asserted.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory

universe u

namespace DaggerOriginalSingularPathCylinderAdjunction

noncomputable section

/-- Maps into the original singular path object correspond to realized original cylinders. -/
def singularPathHomCylinderEquiv (T : TopCat.{u}) (A : SSet.{u}) :
    (A ⟶ (TopCat.toSSet.obj T).path) ≃ (SSet.toTop.obj A ⊗ TopCat.I ⟶ T) :=
  ((ihom.adjunction (Δ[1] : SSet.{u})).homEquiv A (TopCat.toSSet.obj T)).symm.trans
    ((Iso.homFromEquiv (β_ (Δ[1] : SSet.{u}) A)).trans
      ((sSetTopAdj.homEquiv (A ⊗ Δ[1]) T).symm.trans
        (Iso.homFromEquiv (SSet.stdSimplex.toTopTensorDeltaOneIso A))))

/-- In every original simplicial degree, the same path simplices are actual realized cylinders.
-/
def singularPathSimplexCylinderEquiv (T : TopCat.{u}) (n : SimplexCategory) :
    ((TopCat.toSSet.obj T).path).obj (op n) ≃
      (SSet.toTop.obj (SSet.stdSimplex.obj n) ⊗ TopCat.I ⟶ T) :=
  SSet.yonedaEquiv.symm.trans (singularPathHomCylinderEquiv T (SSet.stdSimplex.obj n))

end

end DaggerOriginalSingularPathCylinderAdjunction
