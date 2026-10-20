import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe u

namespace DaggerOriginalNerveProduct

noncomputable section

variable (C D : Type u) [Category.{u} C] [Category.{u} D]

/-- The existing Mathlib comparison for the right-adjoint nerve functor. -/
def nerveProductIso : nerve (C × D) ≅ nerve C ⊗ nerve D :=
  prodComparisonIso nerveFunctor (Cat.of C) (Cat.of D)

theorem nerveProductIso_hom :
    (nerveProductIso C D).hom = lift (nerveMap (CategoryTheory.Prod.fst C D))
      (nerveMap (CategoryTheory.Prod.snd C D)) := rfl

theorem nerveProductIso_hom_fst :
    (nerveProductIso C D).hom ≫ fst _ _ = nerveMap (CategoryTheory.Prod.fst C D) :=
  prodComparison_fst nerveFunctor (Cat.of C) (Cat.of D)

theorem nerveProductIso_hom_snd :
    (nerveProductIso C D).hom ≫ snd _ _ = nerveMap (CategoryTheory.Prod.snd C D) :=
  prodComparison_snd nerveFunctor (Cat.of C) (Cat.of D)

theorem nerveProductIso_inv_fst :
    (nerveProductIso C D).inv ≫ nerveMap (CategoryTheory.Prod.fst C D) = fst _ _ := by
  rw [← nerveProductIso_hom_fst, Iso.inv_hom_id_assoc]

theorem nerveProductIso_inv_snd :
    (nerveProductIso C D).inv ≫ nerveMap (CategoryTheory.Prod.snd C D) = snd _ _ := by
  rw [← nerveProductIso_hom_snd, Iso.inv_hom_id_assoc]

theorem nerveProductIso_hom_inv :
    (nerveProductIso C D).hom ≫ (nerveProductIso C D).inv = 𝟙 _ :=
  (nerveProductIso C D).hom_inv_id

theorem nerveProductIso_inv_hom :
    (nerveProductIso C D).inv ≫ (nerveProductIso C D).hom = 𝟙 _ :=
  (nerveProductIso C D).inv_hom_id

variable {C D} {C' D' : Type u} [Category.{u} C'] [Category.{u} D']

/-- Naturality retains the nerve of the actual product functor on the source. -/
theorem nerveProductIso_naturality (F : C ⥤ C') (G : D ⥤ D') :
    nerveMap (F.prod G) ≫ (nerveProductIso C' D').hom =
      (nerveProductIso C D).hom ≫ (nerveMap F ⊗ₘ nerveMap G) :=
  prodComparison_natural nerveFunctor F.toCatHom G.toCatHom

end

end DaggerOriginalNerveProduct
