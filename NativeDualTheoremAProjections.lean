import NativeDualTheoremACells

/-! Both projections of the literal dual comparison preserve the whole original chains. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalProductGadget DaggerNativeDualTheoremACells DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeDualTheoremAProjections
noncomputable section

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)

def targetProjection : comparison F ⟶ DaggerNerveTheoremA.outerDegreeConstant (nerve D) where
  app q := familyProjection (rowFamily F q)
  naturality {q r} α := by apply NatTrans.ext; rfl

def sourceProjection : comparison F ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (nerve C) where
  app q :=
    { app k x := x.2 ⋙ StructuredArrow.proj (last x.1) F
      naturality {k l} β := by rfl }
  naturality {q r} α := by apply NatTrans.ext; rfl

/-- The diagonal target map is the original full D chain. -/
def targetDiagonal : DaggerBisimplicialDiagonal.diag (comparison F) ⟶ nerve D :=
  DaggerBisimplicialDiagonal.diagMap (targetProjection F) ≫
    eqToHom (DaggerNerveTheoremA.diag_outerDegreeConstant (nerve D))

/-- The diagonal source map is the entire original projection of the under-chain. -/
def sourceDiagonal : DaggerBisimplicialDiagonal.diag (comparison F) ⟶ nerve C :=
  DaggerBisimplicialDiagonal.diagMap (sourceProjection F)

theorem targetProjection_row_GW
    (hF : ∀ d : D, GW (pointMap (nerve (StructuredArrow d F))))
    (q : SimplexCategoryᵒᵖ) : GW ((targetProjection F).app q) :=
  familyProjection_GW (rowFamily F q) (fun d ↦ hF (last d))

/-- Dual Theorem A uses exactly its original StructuredArrow hypothesis here. -/
theorem targetDiagonal_GW
    (hF : ∀ d : D, GW (pointMap (nerve (StructuredArrow d F)))) :
    GW (targetDiagonal F) := by
  have : WeakEquivalence (DaggerBisimplicialDiagonal.diagMap (targetProjection F)) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerOriginalDiagonalGeometric.diagMap_geometric_row
        (targetProjection F) (targetProjection_row_GW F hF))
  apply (weakEquivalence_iff_GW _).mp
  dsimp only [targetDiagonal]
  infer_instance

end
end DaggerNativeDualTheoremAProjections
