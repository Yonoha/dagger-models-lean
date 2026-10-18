import OriginalRealizationLocallyCompactProducts
import TopCatModelCategory.SSet.AnodyneExtensionsAdjunctions

/-!
# Original realized union products as native topological pushout tensors

The native simplicial union product is realized and compared with the actual
ordinary products. The pushout, both inclusion legs, and the resulting arrow
retain their literal maps. Its cofibration follows from the original simplicial
inclusion. Local compactness is required only of the realized second factor
and its original subcomplex.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra
open scoped TopCat.modelCategory SSet.modelCategoryQuillen
open DaggerOriginalRealizationLocallyCompactProducts
open DaggerOriginalRealizationMonomorphismCofibrations

universe u

namespace DaggerOriginalRealizedPushoutTensorCofibrations

noncomputable section

variable {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
variable [LocallyCompactSpace (SSet.toTop.obj Y)]
  [LocallyCompactSpace (SSet.toTop.obj B.toSSet)]

/-- The original realized union is the actual pushout tensor of the realized inclusions. -/
def realizedUnionProd : Functor.PushoutObjObj (curriedTensor TopCat.{u})
    (SSet.toTop.map A.ι) (SSet.toTop.map B.ι) where
  pt := SSet.toTop.obj (A.unionProd B).toSSet
  inl := (realizationProductIso X B.toSSet).inv ≫ SSet.toTop.map (SSet.Subcomplex.unionProd.ι₁ A B)
  inr := (realizationProductIso A.toSSet Y).inv ≫ SSet.toTop.map (SSet.Subcomplex.unionProd.ι₂ A B)
  isPushout := ((SSet.Subcomplex.unionProd.isPushout A B).map SSet.toTop).of_iso
    (realizationProductIso A.toSSet B.toSSet) (realizationProductIso X B.toSSet)
    (realizationProductIso A.toSSet Y) (Iso.refl _)
    (by simpa using realizationProductIso_naturality A.ι (𝟙 B.toSSet))
    (by simpa using realizationProductIso_naturality (𝟙 A.toSSet) B.ι)
    (by simp) (by simp)

/-- The first realized inclusion leg retains precisely the original second-factor map. -/
theorem realizedUnionProd_inl_comp :
    (realizedUnionProd A B).inl ≫ SSet.toTop.map (A.unionProd B).ι ≫
      (realizationProductIso X Y).hom = SSet.toTop.obj X ◁ SSet.toTop.map B.ι := by
  have h : SSet.toTop.map (SSet.Subcomplex.unionProd.ι₁ A B) ≫
      SSet.toTop.map (A.unionProd B).ι ≫ (realizationProductIso X Y).hom =
      (realizationProductIso X B.toSSet).hom ≫
        (SSet.toTop.obj X ◁ SSet.toTop.map B.ι) := by
    rw [← Category.assoc, ← Functor.map_comp, SSet.Subcomplex.unionProd.ι₁_ι]
    simpa using realizationProductIso_naturality (𝟙 X) B.ι
  change ((realizationProductIso X B.toSSet).inv ≫ _) ≫ _ = _
  simp only [Category.assoc]
  rw [h]
  simp

/-- The second realized inclusion leg retains precisely the original first-factor map. -/
theorem realizedUnionProd_inr_comp :
    (realizedUnionProd A B).inr ≫ SSet.toTop.map (A.unionProd B).ι ≫
      (realizationProductIso X Y).hom = SSet.toTop.map A.ι ▷ SSet.toTop.obj Y := by
  have h : SSet.toTop.map (SSet.Subcomplex.unionProd.ι₂ A B) ≫
      SSet.toTop.map (A.unionProd B).ι ≫ (realizationProductIso X Y).hom =
      (realizationProductIso A.toSSet Y).hom ≫
        (SSet.toTop.map A.ι ▷ SSet.toTop.obj Y) := by
    rw [← Category.assoc, ← Functor.map_comp, SSet.Subcomplex.unionProd.ι₂_ι]
    simpa using realizationProductIso_naturality A.ι (𝟙 Y)
  change ((realizationProductIso A.toSSet Y).inv ≫ _) ≫ _ = _
  simp only [Category.assoc]
  rw [h]
  simp

/-- The native pushout-tensor arrow is the original realized union inclusion and comparison. -/
theorem realizedUnionProd_ι :
    (realizedUnionProd A B).ι =
      SSet.toTop.map (A.unionProd B).ι ≫ (realizationProductIso X Y).hom := by
  apply (realizedUnionProd A B).isPushout.hom_ext
  · rw [Functor.PushoutObjObj.inl_ι, realizedUnionProd_inl_comp]
    rfl
  · rw [Functor.PushoutObjObj.inr_ι, realizedUnionProd_inr_comp]
    rfl

/-- This actual ordinary-product pushout tensor is a native TopCat cofibration. -/
theorem realizedUnionProd_cofibration : Cofibration (realizedUnionProd A B).ι := by
  rw [realizedUnionProd_ι]
  have : Cofibration (SSet.toTop.map (A.unionProd B).ι) := realization_map_mono_cofibration _
  infer_instance

end

end DaggerOriginalRealizedPushoutTensorCofibrations
