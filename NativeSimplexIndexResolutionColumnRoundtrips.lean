import NativeSimplexIndexResolutionColumnData

/-! The full original column cells and the under-category family are mutually inverse. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeSimplexIndexResolution DaggerNativeSimplicialReplacementCells
open DaggerNativeSimplexIndexResolutionColumnData DaggerOriginalProductGadget
universe u
namespace DaggerNativeSimplexIndexResolutionColumnRoundtrips
noncomputable section

theorem from_to (X : SSet.{u}) (q k : SimplexCategoryᵒᵖ) (z : Cell (diagram X) q k) :
    fromFamily X q k (toFamily X q k z) = z := by
  rcases z with ⟨c, t⟩
  change (⟨c, ULift.up ((parameterArrow X k (first c) t ≫
    c.map (homOfLE (Fin.zero_le 0))).down.left)⟩ : Cell (diagram X) q k) = ⟨c, t⟩
  have hid : c.map (homOfLE (Fin.zero_le 0)) = 𝟙 (c.obj 0) := c.map_id 0
  rw [hid]
  exact congrArg (fun f : simplexObj X k ((ULiftHom.down.{0, u, u}.obj (first c)).hom.app k t)
      ⟶ first c ↦ (⟨c, ULift.up f.down.left⟩ : Cell (diagram X) q k))
    (Category.comp_id (parameterArrow X k (first c) t))

theorem fromFamily_natural (X : SSet.{u}) {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (k : SimplexCategoryᵒᵖ) (z : (familySSet (columnFamily X k)).obj q) :
    horizontal (diagram X) α k (fromFamily X q k z) =
      fromFamily X r k ((familySSet (columnFamily X k)).map α z) := by
  rcases z with ⟨x, c⟩
  dsimp only [horizontal, fromFamily]
  apply congrArg (fun t ↦
    (⟨(nerve (LiftedIndex X)).map α
      (c ⋙ StructuredArrow.proj (simplexObj X k x) (𝟭 (LiftedIndex X))), t⟩ :
      Cell (diagram X) r k))
  apply ULift.ext
  exact congrArg (fun f ↦ f.down.left) (StructuredArrow.w (initialArrow α c))

end
end DaggerNativeSimplexIndexResolutionColumnRoundtrips
