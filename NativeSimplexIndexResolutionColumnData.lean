import NativeSimplexIndexResolution

/-! The literal column comparison uses each original simplex as an under-category source. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeSimplexIndexResolution DaggerNativeSimplicialReplacementCells
open DaggerSSetGluing DaggerOriginalProductGadget
universe u
namespace DaggerNativeSimplexIndexResolutionColumnData
noncomputable section

/-- The original k-simplex is its original Yoneda map, with only the Hom universe lifted. -/
def simplexObj (X : SSet.{u}) (k : SimplexCategoryᵒᵖ) (x : X.obj k) : LiftedIndex X :=
  ULiftHom.up.{0, u, u}.obj (CostructuredArrow.mk
    (uliftYonedaEquiv.symm x : uliftYoneda.obj k.unop ⟶ X))

abbrev Under (X : SSet.{u}) (k : SimplexCategoryᵒᵖ) (x : X.obj k) :=
  StructuredArrow (simplexObj X k x) (𝟭 (LiftedIndex X))

/-- The entire parameter operator gives the original arrow from its image simplex. -/
def parameterArrow (X : SSet.{u}) (k : SimplexCategoryᵒᵖ) (P : LiftedIndex X)
    (t : ((diagram X).obj P).obj k) :
    simplexObj X k ((ULiftHom.down.{0, u, u}.obj P).hom.app k t) ⟶ P :=
  ULiftHom.up.{0, u, u}.map (CostructuredArrow.homMk t.down (by
    apply uliftYonedaEquiv.injective
    have hm := uliftYonedaEquiv_uliftYoneda_map.{u, 0, 0} t.down
    exact (uliftYonedaEquiv_comp (uliftYoneda.map t.down)
      (ULiftHom.down.{0, u, u}.obj P).hom).trans
        ((congrArg ((ULiftHom.down.{0, u, u}.obj P).hom.app k) hm).trans
          ((uliftYonedaEquiv (F := X) (X := k.unop)).apply_symm_apply _).symm)))

/-- A whole replacement cell determines its original image simplex. -/
def image (X : SSet.{u}) (q k : SimplexCategoryᵒᵖ) (z : Cell (diagram X) q k) : X.obj k :=
  (ULiftHom.down.{0, u, u}.obj (first z.1)).hom.app k z.2

/-- Keep the full original chain and postcompose its actual starting arrow with every 0-to-i arrow. -/
def underChain (X : SSet.{u}) (q k : SimplexCategoryᵒᵖ) (z : Cell (diagram X) q k) :
    (nerve (Under X k (image X q k z))).obj q where
  obj i := StructuredArrow.mk (Y := z.1.obj i)
    (parameterArrow X k (first z.1) z.2 ≫ z.1.map (homOfLE (Fin.zero_le i)))
  map {i j} f := StructuredArrow.homMk (z.1.map f) (by
    change (parameterArrow X k (first z.1) z.2 ≫ z.1.map _) ≫ z.1.map f =
      parameterArrow X k (first z.1) z.2 ≫ z.1.map _
    rw [Category.assoc, ← z.1.map_comp]
    congr 1)
  map_id i := by apply StructuredArrow.hom_ext; exact z.1.map_id i
  map_comp f g := by apply StructuredArrow.hom_ext; exact z.1.map_comp f g

def columnFamily (X : SSet.{u}) (k : SimplexCategoryᵒᵖ) (x : X.obj k) : SSet.{u} :=
  nerve (Under X k x)

/-- This uses the actual original identity object of the under-category. -/
theorem columnFamily_point_GW (X : SSet.{u}) (k : SimplexCategoryᵒᵖ) (x : X.obj k) :
    GW (pointMap (columnFamily X k x)) :=
  DaggerNerveTheoremA.underNervePointMap_GW (simplexObj X k x)

def toFamily (X : SSet.{u}) (q k : SimplexCategoryᵒᵖ) (z : Cell (diagram X) q k) :
    (familySSet (columnFamily X k)).obj q := ⟨image X q k z, underChain X q k z⟩

/-- Project the full under-category chain and retain the whole original starting operator. -/
def fromFamily (X : SSet.{u}) (q k : SimplexCategoryᵒᵖ)
    (z : (familySSet (columnFamily X k)).obj q) : Cell (diagram X) q k :=
  ⟨z.2 ⋙ StructuredArrow.proj (simplexObj X k z.1) (𝟭 (LiftedIndex X)),
    ULift.up (z.2.obj 0).hom.down.left⟩

/-- Every actual under-arrow has its exact original source simplex as the image of its operator. -/
theorem underArrow_image (X : SSet.{u}) (k : SimplexCategoryᵒᵖ) (x : X.obj k)
    (P : LiftedIndex X) (f : simplexObj X k x ⟶ P) :
    (ULiftHom.down.{0, u, u}.obj P).hom.app k (ULift.up f.down.left) = x := by
  have h := congrArg (uliftYonedaEquiv (F := X) (X := k.unop)) (CostructuredArrow.w f.down)
  have hm := uliftYonedaEquiv_uliftYoneda_map.{u, 0, 0} f.down.left
  have hc := uliftYonedaEquiv_comp (uliftYoneda.map f.down.left)
    (ULiftHom.down.{0, u, u}.obj P).hom
  exact ((congrArg ((ULiftHom.down.{0, u, u}.obj P).hom.app k) hm).symm.trans hc.symm).trans
    (h.trans ((uliftYonedaEquiv (F := X) (X := k.unop)).apply_symm_apply x))

/-- The backward comparison retains the full original source label. -/
theorem image_fromFamily (X : SSet.{u}) (q k : SimplexCategoryᵒᵖ)
    (z : (familySSet (columnFamily X k)).obj q) :
    image X q k (fromFamily X q k z) = z.1 :=
  underArrow_image X k z.1 (z.2.obj 0).right (z.2.obj 0).hom

end
end DaggerNativeSimplexIndexResolutionColumnData
