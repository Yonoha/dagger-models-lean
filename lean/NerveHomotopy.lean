import NerveNatTrans
import TopCatModelCategory.SSet.KanComplexWHomotopy
import TopCatModelCategory.TopCat.Homotopy
import TopCatModelCategory.TopCat.HornDeformationRetract

set_option autoImplicit false

open CategoryTheory CategoryTheory.Category
open scoped SSet.modelCategoryQuillen

universe u v w

namespace DaggerNerveHomotopy

noncomputable section

/-- The existing singular-realization functor, without a new replacement choice. -/
abbrev R : SSet.{w} ⥤ SSet.{w} := SSet.toTop ⋙ TopCat.toSSet

variable {C D : Type u} [Category.{v} C] [Category.{v} D] {F G : C ⥤ D}

/-- A supplied natural transformation gives a full simplicial homotopy of nerve maps. -/
def natTransHomotopy (α : F ⟶ G) : SSet.Homotopy (nerveMap F) (nerveMap G) :=
  SSet.Homotopy.mk (natTransMap α) (natTransMap_zero α) (natTransMap_one α)

/-- The same homotopy after the existing realization and singular functors. -/
def natTransHomotopyR (α : F ⟶ G) :
    SSet.Homotopy (R.map (nerveMap F)) (R.map (nerveMap G)) :=
  (natTransHomotopy α).toTop.toSSet

/-- A finite zigzag of actual natural transformations, allowing either orientation. -/
abbrev NatTransZigzag (F G : C ⥤ D) : Prop :=
  Relation.EqvGen (fun H K : C ⥤ D ↦ Nonempty (H ⟶ K)) F G

/-- A zigzag induces homotopy after R; arbitrary input nerves need not be Kan. -/
theorem zigzagHomotopy (h : NatTransZigzag F G) :
    Nonempty (SSet.Homotopy (R.map (nerveMap F)) (R.map (nerveMap G))) := by
  induction h with
  | rel _ _ h => exact ⟨natTransHomotopyR h.some⟩
  | refl => exact ⟨SSet.Subcomplex.RelativeMorphism.Homotopy.ofEq rfl⟩
  | symm _ _ _ ih => exact ⟨ih.some.symm⟩
  | trans _ _ _ _ _ ih ih' => exact ⟨ih.some.trans ih'.some⟩

/-- The actual two nerve maps with both complete inverse homotopies. -/
def nerveHomotopyEquiv (F : C ⥤ D) (G : D ⥤ C)
    (hC : NatTransZigzag (F ⋙ G) (𝟭 C)) (hD : NatTransZigzag (G ⋙ F) (𝟭 D)) :
    SSet.HomotopyEquiv (R.obj (nerve C)) (R.obj (nerve D)) where
  hom := R.map (nerveMap F)
  inv := R.map (nerveMap G)
  homInvId := (zigzagHomotopy hC).some.congr
    (CategoryTheory.Functor.map_comp R (nerveMap F) (nerveMap G))
    (CategoryTheory.Functor.map_id R (nerve C))
  invHomId := (zigzagHomotopy hD).some.congr
    (CategoryTheory.Functor.map_comp R (nerveMap G) (nerveMap F))
    (CategoryTheory.Functor.map_id R (nerve D))

/-- Geometric weak equivalence of the original forward nerve map. -/
theorem nerveMap_geometricW (F : C ⥤ D) (G : D ⥤ C)
    (hC : NatTransZigzag (F ⋙ G) (𝟭 C)) (hD : NatTransZigzag (G ⋙ F) (𝟭 D)) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (nerveMap F))) :=
  SSet.KanComplex.W.homotopyEquivHom (nerveHomotopyEquiv F G hC hD)

/-- Geometric weak equivalence of the original inverse nerve map. -/
theorem nerveMap_inverse_geometricW (F : C ⥤ D) (G : D ⥤ C)
    (hC : NatTransZigzag (F ⋙ G) (𝟭 C)) (hD : NatTransZigzag (G ⋙ F) (𝟭 D)) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (nerveMap G))) :=
  SSet.KanComplex.W.homotopyEquivInv (nerveHomotopyEquiv F G hC hD)

end

end DaggerNerveHomotopy
