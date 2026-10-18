import NativeDualTheoremAWeakProjections

/-! A dual Theorem A for the original StructuredArrow nerves, using the native comparison homotopy. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalProductGadget DaggerNativeDualTheoremACells DaggerSSetGluing
open DaggerNativeDualTheoremAProjections DaggerNativeDualTheoremAWeakProjections
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeDualTheoremA
noncomputable section

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)

/-- Feed the whole original D chain and the entire F-image chain into the existing Id comparison. -/
def idCell (q : SimplexCategoryᵒᵖ) (x : Cell F q q) : DaggerNerveTheoremA.Cell (𝟭 D) q q :=
  { source := x.1
    target := x.2 ⋙ StructuredArrow.proj (last x.1) F ⋙ F
    bridge := (x.2.obj 0).hom }

/-- The comparison preserves every original simplex operator and its original under-arrow triangle. -/
def diagonalCellMap : DaggerBisimplicialDiagonal.diag (comparison F) ⟶
    DaggerBisimplicialDiagonal.diag (DaggerNerveTheoremA.comparison (𝟭 D)) where
  app q := idCell F q
  naturality {q r} α := by
    funext x
    change idCell F r ((DaggerBisimplicialDiagonal.diag (comparison F)).map α x) =
      (DaggerBisimplicialDiagonal.diag (DaggerNerveTheoremA.comparison (𝟭 D))).map α
        (idCell F q x)
    rw [DaggerNerveTheoremA.comparison_diag_map]
    apply DaggerNerveTheoremA.Cell.ext (𝟭 D)
      (x := idCell F r ((DaggerBisimplicialDiagonal.diag (comparison F)).map α x))
      (y := DaggerNerveTheoremA.Cell.map (𝟭 D) α α (idCell F q x)) rfl rfl
    apply heq_of_eq
    change lastArrow α x.1 ≫
      (x.2.obj ((SimplexCategory.toCat.map α.unop).toFunctor.obj
        (0 : Fin (r.unop.len + 1)))).hom =
      lastArrow α x.1 ≫ (x.2.obj 0).hom ≫
        F.map ((x.2.map (homOfLE (Fin.zero_le _))).right)
    rw [StructuredArrow.w]

/-- Reuse the actual native Id-comparison homotopy, retaining both whole original projections. -/
def comparisonHomotopy : SSet.Homotopy (targetDiagonal F) (sourceDiagonal F ≫ nerveMap F) :=
  ((DaggerNerveTheoremA.comparisonHomotopy (𝟭 D)).precomp (diagonalCellMap F)).congr
    (by apply NatTrans.ext; rfl) (by apply NatTrans.ext; rfl)

/-- Dual Theorem A has exactly the original StructuredArrow contractibility hypothesis. -/
theorem nerveMap_GW
    (hF : ∀ d : D, GW (pointMap (nerve (StructuredArrow d F)))) : GW (nerveMap F) := by
  have hcomp : GW (sourceDiagonal F ≫ nerveMap F) :=
    (SSet.KanComplex.W.iff_homotopy (comparisonHomotopy F).toTop.toSSet).mp
      (targetDiagonal_GW F hF)
  have : WeakEquivalence (sourceDiagonal F) :=
    (weakEquivalence_iff_GW _).mpr (sourceDiagonal_GW F)
  apply (weakEquivalence_iff_GW _).mp
  apply (weakEquivalence_precomp_iff (sourceDiagonal F) (nerveMap F)).mp
  exact (weakEquivalence_iff_GW _).mpr hcomp

end
end DaggerNativeDualTheoremA
