import SSetRightProper
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-! Restrict weak maps using native subcomplex pullbacks and right properness. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeSubcomplexWeakRestriction
noncomputable section

theorem isPullback {X Y : SSet.{u}} (f : X ⟶ Y) (A : X.Subcomplex) (B : Y.Subcomplex)
    (g : (A : SSet.{u}) ⟶ (B : SSet.{u})) (h : g ≫ B.ι = A.ι ≫ f)
    (hm : ∀ q x, x ∈ A.obj q ↔ f.app q x ∈ B.obj q) :
    IsPullback g A.ι B.ι f := by
  have hAB : A = B.preimage f := by
    ext q x
    exact hm q x
  subst A
  have hg : g = B.fromPreimage f := by
    apply (cancel_mono B.ι).mp
    exact h.trans (B.fromPreimage_ι f).symm
  rw [hg]
  exact (B.preimage_isPullback f).flip

theorem weakEquivalence {X Y : SSet.{u}} (f : X ⟶ Y) (A : X.Subcomplex)
    (B : Y.Subcomplex) (g : (A : SSet.{u}) ⟶ (B : SSet.{u}))
    (h : g ≫ B.ι = A.ι ≫ f) (hm : ∀ q x, x ∈ A.obj q ↔ f.app q x ∈ B.obj q)
    [Fibration B.ι] [WeakEquivalence f] : WeakEquivalence g :=
  DaggerSSetRightProper.weakEquivalence_of_isPullback (isPullback f A B g h hm)

end
end DaggerNativeSubcomplexWeakRestriction
