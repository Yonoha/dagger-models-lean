import ActualOriginalNecklaceBeadSpine
import NativeFiniteSubcomplexWeakGluing

/-! Original bead intersections are the actual local spines, with their full inclusion arrows. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerNativeStandardSpineInner DaggerNativeInnerHornFactorization
open DaggerNativeJoyalMappingTest DaggerChosenRigidificationNecklace
open DaggerActualOriginalNecklaceBeadSpine
universe u
namespace DaggerActualOriginalNecklaceSpineAttachment
noncomputable section

variable {T : NecklaceCode} (b : T.Bead)

def intersectionMap : (spine.{u} b.length : SSet.{u}) ⟶
    ((b.face ⊓ spine T.len : (Δ[T.len] : SSet.{u}).Subcomplex) : SSet.{u}) :=
  SSet.Subcomplex.lift ((spine b.length).ι ≫ b.faceIso.hom ≫ b.face.ι) (by
    intro q z hz
    obtain ⟨c, rfl⟩ := hz
    constructor
    · exact (b.faceIso.hom.app q c.val).property
    · have hc : c.val ∈ ((spine T.len).preimage (b.faceIso.hom ≫ b.face.ι)).obj q := by
        rw [spine_preimage_bead]
        exact c.property
      exact hc)

theorem intersectionMap_isIso : IsIso (intersectionMap.{u} b) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro q
  apply (isIso_iff_bijective _).mpr
  constructor
  · intro c d he
    apply Subtype.ext
    have hf := congrArg Subtype.val he
    change (b.faceIso.hom ≫ b.face.ι).app q c.val =
      (b.faceIso.hom ≫ b.face.ι).app q d.val at hf
    have hm := (NatTrans.mono_iff_mono_app (b.faceIso.hom ≫ b.face.ι)).mp inferInstance q
    exact (CategoryTheory.mono_iff_injective _).mp hm hf
  · intro z
    let zF : (b.face : SSet.{u}).obj q := ⟨z.val, z.property.1⟩
    let c := b.faceIso.inv.app q zF
    have hc : (b.faceIso.hom ≫ b.face.ι).app q c = z.val :=
      congrArg Subtype.val (congrFun (NatTrans.congr_app b.faceIso.inv_hom_id q) zF)
    have hm : c ∈ (spine b.length).obj q := by
      rw [← spine_preimage_bead b]
      change (b.faceIso.hom ≫ b.face.ι).app q c ∈ (spine T.len).obj q
      rw [hc]
      exact z.property.2
    exact ⟨⟨c, hm⟩, Subtype.ext hc⟩

theorem intersection_innerAnodyne : innerAnodyne (SSet.Subcomplex.homOfLE
    (inf_le_left : NecklaceCode.Bead.face.{u} b ⊓ spine T.len ≤ b.face)) := by
  have : IsIso (intersectionMap.{u} b) := intersectionMap_isIso b
  let e : Arrow.mk (spine.{u} b.length).ι ≅ Arrow.mk
      (SSet.Subcomplex.homOfLE (inf_le_left : b.face ⊓ spine T.len ≤ b.face)) :=
    Arrow.isoMk (asIso (intersectionMap b)) b.faceIso (by
      apply (cancel_mono b.face.ι).mp
      change intersectionMap b ≫
        SSet.Subcomplex.homOfLE (inf_le_left : b.face ⊓ spine T.len ≤ b.face) ≫ b.face.ι =
          ((spine b.length).ι ≫ b.faceIso.hom) ≫ b.face.ι
      rw [Category.assoc, SSet.Subcomplex.homOfLE_ι]
      rfl)
  have : innerAnodyne.{u}.RespectsIso := by unfold innerAnodyne; infer_instance
  exact (innerAnodyne.arrow_mk_iso_iff e).mp (inclusion_innerAnodyne b.length)

theorem intersection_categorical_weak : weakCategoricalEquivalences
    (SSet.Subcomplex.homOfLE
      (inf_le_left : NecklaceCode.Bead.face.{u} b ⊓ spine T.len ≤ b.face)) :=
  DaggerNativeInnerJoyalMappingWeak.innerAnodyne_weak _ (intersection_innerAnodyne b)

end
end DaggerActualOriginalNecklaceSpineAttachment
