import NativeDualTheoremAProjections

/-! The dual comparison column is exactly the family of actual native over-category nerves. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalProductGadget DaggerNativeDualTheoremACells
open DaggerNativeStructuredArrowChainDecomposition
universe u
namespace DaggerNativeDualTheoremAColumnComparison
noncomputable section

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)

def columnFamily (k : SimplexCategoryᵒᵖ) (c : (nerve C).obj k) : SSet.{u} :=
  nerve (Over (F.obj (c.obj 0)))

/-- Swap only the two independent chain labels, retaining their whole connecting arrow. -/
def bridgeSwap (q k : SimplexCategoryᵒᵖ) :
    (Σ d : (nerve D).obj q, Σ c : (nerve C).obj k, last d ⟶ F.obj (c.obj 0)) ≃
    (Σ c : (nerve C).obj k, Σ d : (nerve D).obj q, last d ⟶ F.obj (c.obj 0)) where
  toFun p := ⟨p.2.1, p.1, p.2.2⟩
  invFun p := ⟨p.2.1, p.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reuse the full StructuredArrow and Over chain equivalences, retaining the actual bridge. -/
def columnEquiv (q k : SimplexCategoryᵒᵖ) :
    Cell F q k ≃ (familySSet (columnFamily F k)).obj q :=
  (Equiv.sigmaCongrRight (fun d ↦ chainEquiv F (last d) k.unop.len)).trans
    ((bridgeSwap F q k).trans (Equiv.sigmaCongrRight (fun c ↦
      (DaggerNativeOverChainDecomposition.overChainEquiv D (F.obj (c.obj 0)) q.unop.len).symm)))

/-- The forward comparison has its literal original whole-chain formula. -/
theorem columnEquiv_apply (q k : SimplexCategoryᵒᵖ) (x : Cell F q k) :
    columnEquiv F q k x =
      ⟨x.2 ⋙ StructuredArrow.proj (last x.1) F,
        DaggerNativeOverChainDecomposition.chainLift x.1 (x.2.obj 0).hom⟩ := rfl

theorem column_natural {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (k : SimplexCategoryᵒᵖ) (x : Cell F q k) :
    columnEquiv F r k (horizontal F α k x) =
      (familySSet (columnFamily F k)).map α (columnEquiv F q k x) := by
  rw [columnEquiv_apply, columnEquiv_apply]
  change (⟨x.2 ⋙ StructuredArrow.proj (last x.1) F,
    DaggerNativeOverChainDecomposition.chainLift ((nerve D).map α x.1)
      (lastArrow α x.1 ≫ (x.2.obj 0).hom)⟩ : (familySSet (columnFamily F k)).obj r) =
    ⟨x.2 ⋙ StructuredArrow.proj (last x.1) F,
      (nerve (Over (F.obj (x.2.obj 0).right))).map α
        (DaggerNativeOverChainDecomposition.chainLift x.1 (x.2.obj 0).hom)⟩
  apply congrArg (fun t ↦ (⟨x.2 ⋙ StructuredArrow.proj (last x.1) F, t⟩ :
    (familySSet (columnFamily F k)).obj r))
  exact (DaggerNativeOverChainDecomposition.chainLift_precompose x.1 (x.2.obj 0).hom
    (SimplexCategory.toCat.map α.unop).toFunctor).symm

/-- Every original horizontal operator is included in the native column isomorphism. -/
def columnIso (k : SimplexCategoryᵒᵖ) :
    (comparison F).flip.obj k ≅ familySSet (columnFamily F k) :=
  NatIso.ofComponents (fun q ↦ Equiv.toIso (columnEquiv F q k)) (by
    intro q r α
    funext x
    exact column_natural F α k x)

end
end DaggerNativeDualTheoremAColumnComparison
