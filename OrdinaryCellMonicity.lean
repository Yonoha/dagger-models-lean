import OrdinaryCellComparison
import OrdinaryCellNormalizer
import OrdinaryFirstWord

/-! The full original object-bijection and Hom-monomorphism conclusions of
`bg.lem.ordinary-cell(1)`, for every original ordinary enriched pushout. -/

open CategoryTheory DaggerModels

universe u

namespace DaggerOrdinaryCellMonicity

variable (C : SimplicialCat.{u, u}) (x y : C.Obj) {K L : SSet.{u}}
  (i : K ⟶ L) (u0 : K ⟶ (x ⟶[SSet] y))
  {D : SimplicialCat.{u, u}} (g : OrdinaryTwoObjectCell.cell L ⟶ D) (f : C ⟶ D)
  (sq : IsPushout (OrdinaryTwoObjectCell.map i)
    (OrdinaryTwoObjectCell.fromData K C x y u0) g f) [Mono i]

include g sq

/-- Every original Hom map is monic, with the original object map and endpoints. -/
theorem hom_mono (a b : C.Obj) : Mono (f.map a b) :=
  (DaggerOrdinaryCellComparison.image_hom_mono_iff C x y i u0 g f sq a b).1
    (DaggerOrdinaryCellNormalizer.oldMap_mono C x y (DaggerOrdinaryCellImage.image i)
      (DaggerOrdinaryCellImage.attachingMap i u0) a b)

/-- Both conclusions of the manuscript's first ordinary-cell assertion. -/
theorem ordinary_cell_part_one :
    Function.Bijective f.obj ∧ ∀ a b : C.Obj, Mono (f.map a b) :=
  ⟨DaggerOrdinaryFirstWord.objectMap_bijective i x y u0 f g sq,
    hom_mono C x y i u0 g f sq⟩

end DaggerOrdinaryCellMonicity
