import NativeSimplexIndexResolutionColumnInverse

/-! Each original column is the family of the actual source-simplex under-category nerves. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeSimplexIndexResolution DaggerNativeSimplicialReplacementCells
open DaggerNativeSimplexIndexResolutionColumnData DaggerNativeSimplicialReplacement
open DaggerNativeSimplexIndexResolutionColumnRoundtrips
open DaggerNativeSimplexIndexResolutionColumnInverse DaggerOriginalProductGadget DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeSimplexIndexResolutionColumnComparison
noncomputable section

def columnEquiv (X : SSet.{u}) (q k : SimplexCategoryᵒᵖ) :
    (familySSet (columnFamily X k)).obj q ≃ Cell (diagram X) q k where
  toFun := fromFamily X q k
  invFun := toFamily X q k
  left_inv := to_from X q k
  right_inv := from_to X q k

/-- The simplicial isomorphism retains the whole original chain and every parameter operator. -/
def columnIso (X : SSet.{u}) (k : SimplexCategoryᵒᵖ) :
    familySSet (columnFamily X k) ≅ (resolution X).flip.obj k :=
  NatIso.ofComponents (fun q ↦ Equiv.toIso (columnEquiv X q k)) (by
    intro q r α
    funext z
    exact (fromFamily_natural X α k z).symm)

def columnAugmentation (X : SSet.{u}) (k : SimplexCategoryᵒᵖ) :
    (resolution X).flip.obj k ⟶ DaggerOriginalFlagFlankification.constantSSet (X.obj k) :=
  { app q z := image X q k z
    naturality {q r} α := by
      funext z
      exact congrFun (NatTrans.congr_app
        ((augmentation (diagram X) (diagramAugmentation X)).naturality α) k) z }

/-- The original full augmentation is exactly the family projection through the column isomorphism. -/
theorem columnAugmentation_eq (X : SSet.{u}) (k : SimplexCategoryᵒᵖ) :
    columnAugmentation X k = (columnIso X k).inv ≫ familyProjection (columnFamily X k) := rfl

theorem columnAugmentation_GW (X : SSet.{u}) (k : SimplexCategoryᵒᵖ) :
    GW (columnAugmentation X k) := by
  have : WeakEquivalence (familyProjection (columnFamily X k)) :=
    (weakEquivalence_iff_GW _).mpr
      (familyProjection_GW (columnFamily X k) (columnFamily_point_GW X k))
  apply (weakEquivalence_iff_GW _).mp
  rw [columnAugmentation_eq]
  infer_instance

end
end DaggerNativeSimplexIndexResolutionColumnComparison
