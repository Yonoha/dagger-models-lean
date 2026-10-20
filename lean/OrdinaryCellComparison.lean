import RelativeOneCellPresentation
import SimplicialIsoHoms
import OrdinaryCellImage

/-! Transport full Hom properties from the actual relative presentation to any original
ordinary enriched pushout. The actual Arrow isomorphisms retain endpoint transports. -/

open CategoryTheory DaggerModels
open DaggerRelativeOneCellPresentation DaggerSimplicialIsoHoms DaggerOrdinaryCellImage

universe u

namespace DaggerOrdinaryCellComparison

noncomputable section

variable (C : SimplicialCat.{u, u}) (x y : C.Obj) {K L : SSet.{u}}
  (i : K ⟶ L) (u0 : K ⟶ (x ⟶[SSet] y))
  {D : SimplicialCat.{u, u}} (g : OrdinaryTwoObjectCell.cell L ⟶ D) (f : C ⟶ D)
  (sq : IsPushout (OrdinaryTwoObjectCell.map i)
    (OrdinaryTwoObjectCell.fromData K C x y u0) g f) (a b : C.Obj)

/-- The source is unchanged; the target uses the actual full Hom iso and endpoint equations. -/
def homArrowIso : Arrow.mk ((v C x y i u0).map a b) ≅ Arrow.mk (f.map a b) :=
  Arrow.isoMk (Iso.refl _)
    ((homIso (originalIso C x y i u0 g f sq) a b).trans
      (eqToIso (by
        rw [originalIso_obj C x y i u0 g f sq a, originalIso_obj C x y i u0 g f sq b]
        rfl))) (by
    simpa [homIso] using (originalIso_map C x y i u0 g f sq a b).symm)

theorem homArrowIso_left : (homArrowIso C x y i u0 g f sq a b).hom.left = 𝟙 _ := rfl

theorem homArrowIso_right :
    (homArrowIso C x y i u0 g f sq a b).hom.right =
      (originalIso C x y i u0 g f sq).hom.map a b ≫
        eqToHom (by
          rw [originalIso_obj C x y i u0 g f sq a, originalIso_obj C x y i u0 g f sq b]
          rfl) := rfl

include g sq

theorem hom_property_iff (P : MorphismProperty SSet.{u}) [P.RespectsIso] :
    P ((v C x y i u0).map a b) ↔ P (f.map a b) :=
  P.arrow_mk_iso_iff (homArrowIso C x y i u0 g f sq a b)

theorem hom_mono_iff : Mono ((v C x y i u0).map a b) ↔ Mono (f.map a b) :=
  hom_property_iff C x y i u0 g f sq a b (MorphismProperty.monomorphisms SSet.{u})

variable [Mono i]

/-- The range reduction leaves the original pushout apex and both outgoing maps untouched. -/
def imageHomArrowIso :
    Arrow.mk ((v C x y (image i).ι (attachingMap i u0)).map a b) ≅
      Arrow.mk (f.map a b) :=
  homArrowIso C x y (image i).ι (attachingMap i u0) g f
    (pushoutToImage i C D x y u0 g f sq) a b

theorem image_hom_property_iff (P : MorphismProperty SSet.{u}) [P.RespectsIso] :
    P ((v C x y (image i).ι (attachingMap i u0)).map a b) ↔ P (f.map a b) :=
  P.arrow_mk_iso_iff (imageHomArrowIso C x y i u0 g f sq a b)

theorem image_hom_mono_iff :
    Mono ((v C x y (image i).ι (attachingMap i u0)).map a b) ↔ Mono (f.map a b) :=
  image_hom_property_iff C x y i u0 g f sq a b (MorphismProperty.monomorphisms SSet.{u})

end

end DaggerOrdinaryCellComparison
