import DaggerModels.OrdinaryTwoObjectCell
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-! Replace an arbitrary mono by its actual range inclusion, retaining the complete
original enriched attaching map, pushout apex and both outgoing legs. -/

open CategoryTheory CategoryTheory.Limits DaggerModels

universe u

namespace DaggerOrdinaryCellImage

noncomputable section

abbrev image {K L : SSet.{u}} (i : K ⟶ L) : L.Subcomplex := SSet.Subcomplex.range i

variable {K L : SSet.{u}} (i : K ⟶ L) [Mono i]

def imageIso : K ≅ (image i : SSet.{u}) := asIso (SSet.Subcomplex.toRange i)

theorem imageIso_hom : (imageIso i).hom = SSet.Subcomplex.toRange i := rfl

theorem imageIso_ι : (imageIso i).hom ≫ (image i).ι = i :=
  SSet.Subcomplex.toRange_ι i

theorem imageIso_val (q : SimplexCategoryᵒᵖ) (t : K.obj q) :
    ((imageIso i).hom.app q t).val = i.app q t := rfl

def attachingMap {C : SimplicialCat.{u, u}} {x y : C.Obj}
    (u0 : K ⟶ (x ⟶[SSet] y)) : (image i : SSet.{u}) ⟶ (x ⟶[SSet] y) :=
  (imageIso i).inv ≫ u0

theorem attachingMap_precomp {C : SimplicialCat.{u, u}} {x y : C.Obj}
    (u0 : K ⟶ (x ⟶[SSet] y)) : (imageIso i).hom ≫ attachingMap i u0 = u0 := by
  simp [attachingMap, ← Category.assoc]

def arrowIso : Arrow.mk i ≅ Arrow.mk (image i).ι :=
  Arrow.isoMk (imageIso i) (Iso.refl L) (by simpa using (imageIso_ι i).symm)

theorem property_iff (P : MorphismProperty SSet.{u}) [P.RespectsIso] :
    P i ↔ P (image i).ι := P.arrow_mk_iso_iff (arrowIso i)

theorem cellMap_precomp :
    OrdinaryTwoObjectCell.map (imageIso i).hom ≫ OrdinaryTwoObjectCell.map (image i).ι =
      OrdinaryTwoObjectCell.map i := by
  change OrdinaryTwoObjectCell.functor.map (imageIso i).hom ≫
    OrdinaryTwoObjectCell.functor.map (image i).ι = OrdinaryTwoObjectCell.functor.map i
  rw [← Functor.map_comp, imageIso_ι]

theorem cellAttaching_precomp (C : SimplicialCat.{u, u}) (x y : C.Obj)
    (u0 : K ⟶ (x ⟶[SSet] y)) :
    OrdinaryTwoObjectCell.map (imageIso i).hom ≫
        OrdinaryTwoObjectCell.fromData (image i) C x y (attachingMap i u0) =
      OrdinaryTwoObjectCell.fromData K C x y u0 := by
  change OrdinaryTwoObjectCell.functor.map (imageIso i).hom ≫
    OrdinaryTwoObjectCell.fromData (image i) C x y (attachingMap i u0) = _
  rw [← OrdinaryTwoObjectCell.fromData_naturality_left, attachingMap_precomp]

variable (C D : SimplicialCat.{u, u}) (x y : C.Obj) (u0 : K ⟶ (x ⟶[SSet] y))
  (g : OrdinaryTwoObjectCell.cell L ⟶ D) (f : C ⟶ D)

theorem pushoutToImage
    (sq : IsPushout (OrdinaryTwoObjectCell.map i)
      (OrdinaryTwoObjectCell.fromData K C x y u0) g f) :
    IsPushout (OrdinaryTwoObjectCell.map (image i).ι)
      (OrdinaryTwoObjectCell.fromData (image i) C x y (attachingMap i u0)) g f := by
  apply sq.of_iso (OrdinaryTwoObjectCell.functor.mapIso (imageIso i))
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa using (cellMap_precomp i).symm
  · simpa using (cellAttaching_precomp i C x y u0).symm
  · simp
  · simp

theorem pushoutFromImage
    (sq : IsPushout (OrdinaryTwoObjectCell.map (image i).ι)
      (OrdinaryTwoObjectCell.fromData (image i) C x y (attachingMap i u0)) g f) :
    IsPushout (OrdinaryTwoObjectCell.map i)
      (OrdinaryTwoObjectCell.fromData K C x y u0) g f := by
  apply sq.of_iso (OrdinaryTwoObjectCell.functor.mapIso (imageIso i).symm)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · have h := cellMap_precomp i
    rw [← h]
    change _ = OrdinaryTwoObjectCell.functor.map (imageIso i).inv ≫
      (OrdinaryTwoObjectCell.functor.map (imageIso i).hom ≫ _)
    rw [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
    rw [CategoryTheory.Functor.map_id]
    simp
  · have h := cellAttaching_precomp i C x y u0
    rw [← h]
    change _ = OrdinaryTwoObjectCell.functor.map (imageIso i).inv ≫
      (OrdinaryTwoObjectCell.functor.map (imageIso i).hom ≫ _)
    rw [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
    rw [CategoryTheory.Functor.map_id]
    simp
  · simp
  · simp

theorem pushout_iff :
    IsPushout (OrdinaryTwoObjectCell.map i) (OrdinaryTwoObjectCell.fromData K C x y u0) g f ↔
      IsPushout (OrdinaryTwoObjectCell.map (image i).ι)
        (OrdinaryTwoObjectCell.fromData (image i) C x y (attachingMap i u0)) g f :=
  ⟨pushoutToImage i C D x y u0 g f, pushoutFromImage i C D x y u0 g f⟩

end

end DaggerOrdinaryCellImage
