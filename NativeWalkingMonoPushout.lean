import NativeWalkingRelativeGenerators
import NativeJoyalMappingWeakProperties

/-!
# Full native mono / original zero-endpoint pushout products are mapping weak

Transport the library's whole subcomplex union-product through the actual range
isomorphisms. Every choice of the original pushout tensor has the same weak map,
by the actual pushout comparison isomorphism. No candidate-class identification
or Joyal model is supplied.
-/
set_option autoImplicit false
open CategoryTheory Limits Simplicial MonoidalCategory
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerNativeBoundaryCategoricalCylinder
open DaggerNativeWalkingRelativeGenerators DaggerNativeJoyalMappingTest
universe u
namespace DaggerNativeWalkingMonoPushout
noncomputable section

theorem zeroInclusion_app (q : SimplexCategoryᵒᵖ) (x : (Δ[0] : SSet.{u}).obj q) :
    zeroInclusion.app q x = time q false := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

theorem range_zero : SSet.Subcomplex.range zeroInclusion.{u} = zeroSubcomplex.{u} := by
  ext q t
  change (∃ x, zeroInclusion.app q x = t) ↔ t = time q false
  constructor
  · rintro ⟨x, h⟩
    exact h.symm.trans (zeroInclusion_app q x)
  · intro h
    exact ⟨SSet.stdSimplex.const 0 0 q, h.symm⟩

def zeroIso : (Δ[0] : SSet.{u}) ≅ zeroSubcomplex.{u}.toSSet := by
  letI : Mono zeroInclusion.{u} :=
    { right_cancellation := fun g h _ ↦ SSet.stdSimplex.isTerminalObj₀.hom_ext g h }
  exact asIso (Subfunctor.toRange zeroInclusion.{u}) ≪≫ SSet.Subcomplex.isoOfEq range_zero

theorem zeroIso_hom_ι : zeroIso.{u}.hom ≫ zeroSubcomplex.ι = zeroInclusion := by
  rw [zeroIso, Iso.trans_hom, Category.assoc, SSet.Subcomplex.isoOfEq_hom_ι]
  exact Subfunctor.toRange_ι _

theorem zeroIso_inv_comp : zeroIso.{u}.inv ≫ zeroInclusion = zeroSubcomplex.ι := by
  rw [← zeroIso_hom_ι, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

def rangeIso {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    A ≅ (SSet.Subcomplex.range i).toSSet := asIso (Subfunctor.toRange i)

theorem rangeIso_hom_ι {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    (rangeIso i).hom ≫ (SSet.Subcomplex.range i).ι = i := Subfunctor.toRange_ι i

theorem rangeIso_inv_comp {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    (rangeIso i).inv ≫ i = (SSet.Subcomplex.range i).ι := by
  have h := congrArg (fun f ↦ (rangeIso i).inv ≫ f) (rangeIso_hom_ι i)
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using h.symm

def relativePushout {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    SSet.PushoutTensor i zeroInclusion.{u} where
  pt := (SSet.Subcomplex.range i).unionProd zeroSubcomplex
  inl := (B ◁ zeroIso.hom) ≫
    (SSet.PushoutTensor.unionProd (SSet.Subcomplex.range i) zeroSubcomplex).inl
  inr := ((rangeIso i).hom ▷ J) ≫
    (SSet.PushoutTensor.unionProd (SSet.Subcomplex.range i) zeroSubcomplex).inr
  isPushout := by
    let h := SSet.PushoutTensor.unionProd (SSet.Subcomplex.range i) zeroSubcomplex
    refine h.isPushout.of_iso ((rangeIso i).symm ⊗ᵢ zeroIso.symm)
      (Iso.refl B ⊗ᵢ zeroIso.symm) ((rangeIso i).symm ⊗ᵢ Iso.refl J)
      (Iso.refl _) ?_ ?_ ?_ ?_
    · apply NatTrans.ext
      funext q p
      change (p.1.val, zeroIso.inv.app q p.2) =
        (i.app q ((rangeIso i).inv.app q p.1), zeroIso.inv.app q p.2)
      exact Prod.ext (congrFun (NatTrans.congr_app (rangeIso_inv_comp i) q) p.1).symm rfl
    · apply NatTrans.ext
      funext q p
      change ((rangeIso i).inv.app q p.1, p.2.val) =
        ((rangeIso i).inv.app q p.1, zeroInclusion.app q (zeroIso.inv.app q p.2))
      exact Prod.ext rfl (congrFun (NatTrans.congr_app zeroIso_inv_comp q) p.2).symm
    · change h.inl ≫ 𝟙 _ = (B ◁ zeroIso.inv) ≫ (B ◁ zeroIso.hom) ≫ h.inl
      rw [Category.comp_id, ← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id,
        Category.id_comp]
    · change h.inr ≫ 𝟙 _ = ((rangeIso i).inv ▷ J) ≫ ((rangeIso i).hom ▷ J) ≫ h.inr
      rw [Category.comp_id, ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight,
        Category.id_comp]

theorem relativePushout_ι {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    (relativePushout i).ι = ((SSet.Subcomplex.range i).unionProd zeroSubcomplex).ι := by
  let h := SSet.PushoutTensor.unionProd (SSet.Subcomplex.range i) zeroSubcomplex
  apply (relativePushout i).isPushout.hom_ext
  · rw [(relativePushout i).inl_ι]
    change B ◁ zeroInclusion = ((B ◁ zeroIso.hom) ≫ h.inl) ≫
      ((SSet.Subcomplex.range i).unionProd zeroSubcomplex).ι
    rw [← SSet.PushoutTensor.ι_unionProd, Category.assoc, h.inl_ι]
    change B ◁ zeroInclusion = (B ◁ zeroIso.hom) ≫ (B ◁ zeroSubcomplex.ι)
    rw [← whiskerLeft_comp, zeroIso_hom_ι]
  · rw [(relativePushout i).inr_ι]
    change i ▷ J = (((rangeIso i).hom ▷ J) ≫ h.inr) ≫
      ((SSet.Subcomplex.range i).unionProd zeroSubcomplex).ι
    rw [← SSet.PushoutTensor.ι_unionProd, Category.assoc, h.inr_ι]
    change i ▷ J = ((rangeIso i).hom ▷ J) ≫ ((SSet.Subcomplex.range i).ι ▷ J)
    rw [← comp_whiskerRight, rangeIso_hom_ι]

def comparisonIso {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (sq : SSet.PushoutTensor i zeroInclusion.{u}) : (relativePushout i).pt ≅ sq.pt :=
  (relativePushout i).isPushout.isoIsPushout _ _ sq.isPushout

theorem comparison_comp {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (sq : SSet.PushoutTensor i zeroInclusion.{u}) :
    (comparisonIso i sq).hom ≫ sq.ι = (relativePushout i).ι := by
  apply (relativePushout i).isPushout.hom_ext
  · rw [comparisonIso, ← Category.assoc]
    rw [IsPushout.inl_isoIsPushout_hom, sq.inl_ι, (relativePushout i).inl_ι]
  · rw [comparisonIso, ← Category.assoc]
    rw [IsPushout.inr_isoIsPushout_hom, sq.inr_ι, (relativePushout i).inr_ι]

def comparisonArrowIso {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (sq : SSet.PushoutTensor i zeroInclusion.{u}) :
    Arrow.mk (relativePushout i).ι ≅ Arrow.mk sq.ι :=
  Arrow.isoMk (comparisonIso i sq) (Iso.refl _) (by
    change (comparisonIso i sq).hom ≫ sq.ι = (relativePushout i).ι ≫ 𝟙 _
    rw [Category.comp_id]
    exact comparison_comp i sq)

theorem pushout_zero_weak {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (sq : SSet.PushoutTensor i zeroInclusion.{u}) : weakCategoricalEquivalences sq.ι := by
  have hw : weakCategoricalEquivalences (relativePushout i).ι := by
    rw [relativePushout_ι]
    exact unionProd_zero_weak (SSet.Subcomplex.range i)
  exact weakCategoricalEquivalences.of_retract
    (Retract.ofIso (comparisonArrowIso i sq).symm) hw

theorem pushout_zero_mono_weak {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (sq : SSet.PushoutTensor i zeroInclusion.{u}) :
    (MorphismProperty.monomorphisms SSet ⊓ weakCategoricalEquivalences) sq.ι := by
  have hm : Mono (relativePushout i).ι := by rw [relativePushout_ι]; infer_instance
  exact ⟨(MorphismProperty.monomorphisms SSet).of_retract
    (Retract.ofIso (comparisonArrowIso i sq).symm) hm, pushout_zero_weak i sq⟩

end
end DaggerNativeWalkingMonoPushout
