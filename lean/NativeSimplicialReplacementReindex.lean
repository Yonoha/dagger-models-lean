import NativeSimplicialReplacement

/-! Reindex the original whole simplicial replacement without discarding parameter simplices. -/
set_option autoImplicit false
open CategoryTheory Opposite HomotopicalAlgebra
open DaggerNativeSimplicialReplacement DaggerNativeSimplicialReplacementCells
open DaggerOriginalProductGadget DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeSimplicialReplacementReindex
noncomputable section

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable (F : C ⥤ D) (G : D ⥤ SSet.{u})

/-- Apply F to every object and arrow of the original chain, keeping its entire parameter. -/
def reindex : replacement (F ⋙ G) ⟶ replacement G where
  app q :=
    { app _ x := ⟨x.1 ⋙ F, x.2⟩
      naturality := by intros; rfl }
  naturality := by intros; apply NatTrans.ext; rfl

def diagonalReindex :
    DaggerBisimplicialDiagonal.diag (replacement (F ⋙ G)) ⟶
      DaggerBisimplicialDiagonal.diag (replacement G) :=
  DaggerBisimplicialDiagonal.diagMap (reindex F G)

/-- Both whole-chain projections agree with the original nerve map of F. -/
theorem projection_square : diagonalReindex F G ≫ diagonalProjection G =
    diagonalProjection (F ⋙ G) ≫ nerveMap F := by
  apply NatTrans.ext
  rfl

/-- Contractible weights transfer the original nerve weakness to this exact weighted map. -/
theorem diagonalReindex_GW
    (hF : GW (nerveMap F)) (hG : ∀ d, GW (pointMap (G.obj d))) :
    GW (diagonalReindex F G) := by
  have : WeakEquivalence (nerveMap F) := (weakEquivalence_iff_GW _).mpr hF
  have : WeakEquivalence (diagonalProjection (F ⋙ G)) :=
    (weakEquivalence_iff_GW _).mpr (diagonalProjection_GW (F ⋙ G) (fun c ↦ hG (F.obj c)))
  have : WeakEquivalence (diagonalProjection G) :=
    (weakEquivalence_iff_GW _).mpr (diagonalProjection_GW G hG)
  apply (weakEquivalence_iff_GW _).mp
  apply (weakEquivalence_postcomp_iff (diagonalReindex F G) (diagonalProjection G)).mp
  rw [projection_square]
  infer_instance

/-- Every original augmentation commutes with the full reindexing map. -/
theorem augmentation_square {X : SSet.{u}} (η : G ⟶ (Functor.const D).obj X) :
    diagonalReindex F G ≫ diagonalAugmentation G η =
      diagonalAugmentation (F ⋙ G) (Functor.whiskerLeft F η) := by
  apply NatTrans.ext
  rfl

end
end DaggerNativeSimplicialReplacementReindex
