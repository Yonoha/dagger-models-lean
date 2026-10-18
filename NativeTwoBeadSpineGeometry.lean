import NativeStandardSpineGeometry
import OriginalCounitRightConeFunctor
import NativeOriginalWeakMonoPushout

/-! The original initial simplex and final edge form a categorically weak two-bead inclusion. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeStandardSpineInner DaggerNativeStandardSpineGeometry
open DaggerOriginalCounitRightCone DaggerNativeInnerHornFactorization
open DaggerNativeJoyalMappingTest
universe u
namespace DaggerNativeTwoBeadSpineGeometry
noncomputable section

def firstFace (n : ℕ) : (Δ[n + 1] : SSet.{u}).Subcomplex :=
  SSet.stdSimplex.face {Fin.last (n + 1)}ᶜ

def lastEdge (n : ℕ) : (Δ[n + 1] : SSet.{u}).Subcomplex :=
  SSet.stdSimplex.face {(Fin.last n).castSucc, (Fin.last n).succ}

def twoBead (n : ℕ) : (Δ[n + 1] : SSet.{u}).Subcomplex := firstFace n ⊔ lastEdge n

def firstFaceIso (n : ℕ) : (Δ[n] : SSet.{u}) ≅ (firstFace n : SSet.{u}) :=
  SSet.stdSimplex.faceSingletonComplIso (Fin.last (n + 1))

theorem firstFaceIso_hom (n : ℕ) : (firstFaceIso.{u} n).hom ≫ (firstFace n).ι = face n :=
  SSet.stdSimplex.faceSingletonComplIso_hom_ι _

theorem firstFaceIso_inv (n : ℕ) : (firstFaceIso.{u} n).inv ≫ face n = (firstFace n).ι := by
  rw [← firstFaceIso_hom, Iso.inv_hom_id_assoc]

theorem spine_preimage_face (n : ℕ) : (spine.{u} (n + 1)).preimage (face n) = spine n := by
  ext q c
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h d =>
      change (face n).app (op ⦋d⦌) c ∈ (spine (n + 1)).obj (op ⦋d⦌) ↔
        c ∈ (spine n).obj (op ⦋d⦌)
      rw [mem_spine_iff, mem_spine_iff]
      change ((Fin.last (n + 1)).succAbove (SSet.stdSimplex.asOrderHom c (Fin.last d))).val ≤
        ((Fin.last (n + 1)).succAbove (SSet.stdSimplex.asOrderHom c 0)).val + 1 ↔ _
      simp only [Fin.succAbove_last, Fin.val_castSucc]

def intersectionMap (n : ℕ) : (spine.{u} n : SSet.{u}) ⟶
    ((firstFace n ⊓ spine (n + 1) : (Δ[n + 1] : SSet.{u}).Subcomplex) : SSet.{u}) :=
  SSet.Subcomplex.lift ((spine n).ι ≫ face n) (by
    intro q z hz
    obtain ⟨c, rfl⟩ := hz
    constructor
    · have hr := SSet.stdSimplex.range_δ.{u} (Fin.last (n + 1))
      change SSet.Subcomplex.range (face n) = firstFace n at hr
      rw [← hr]
      exact ⟨c.val, rfl⟩
    · have hc : c.val ∈ ((spine (n + 1)).preimage (face n)).obj q := by
        rw [spine_preimage_face]
        exact c.property
      exact hc)

theorem intersectionMap_isIso (n : ℕ) : IsIso (intersectionMap.{u} n) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro q
  apply (isIso_iff_bijective _).mpr
  constructor
  · intro c d he
    apply Subtype.ext
    have hf := congrArg Subtype.val he
    change (face n).app q c.val = (face n).app q d.val at hf
    have hm : Mono (face.{u} n) := by
      rw [← firstFaceIso_hom]
      infer_instance
    have hq := (NatTrans.mono_iff_mono_app (face.{u} n)).mp hm q
    exact (CategoryTheory.mono_iff_injective ((face n).app q)).mp hq hf
  · intro z
    let zF : (firstFace n : SSet.{u}).obj q := ⟨z.val, z.property.1⟩
    let c := (firstFaceIso n).inv.app q zF
    have hc : (face n).app q c = z.val :=
      congrFun (NatTrans.congr_app (firstFaceIso_inv n) q) zF
    have hm : c ∈ (spine n).obj q := by
      rw [← spine_preimage_face]
      change (face n).app q c ∈ (spine (n + 1)).obj q
      rw [hc]
      exact z.property.2
    refine ⟨⟨c, hm⟩, ?_⟩
    exact Subtype.ext hc

theorem intersection_innerAnodyne (n : ℕ) :
    innerAnodyne (SSet.Subcomplex.homOfLE
      (inf_le_left : firstFace.{u} n ⊓ spine (n + 1) ≤ firstFace n)) := by
  have : IsIso (intersectionMap.{u} n) := intersectionMap_isIso n
  let e : Arrow.mk (spine.{u} n).ι ≅ Arrow.mk
      (SSet.Subcomplex.homOfLE
        (inf_le_left : firstFace.{u} n ⊓ spine (n + 1) ≤ firstFace n)) :=
    Arrow.isoMk (asIso (intersectionMap n)) (firstFaceIso n) (by
      apply (cancel_mono (firstFace n).ι).mp
      change intersectionMap n ≫
        SSet.Subcomplex.homOfLE (inf_le_left : firstFace n ⊓ spine (n + 1) ≤ firstFace n) ≫
          (firstFace n).ι = ((spine n).ι ≫ (firstFaceIso n).hom) ≫ (firstFace n).ι
      rw [SSet.Subcomplex.homOfLE_ι, Category.assoc, firstFaceIso_hom]
      rfl)
  have : innerAnodyne.{u}.RespectsIso := by unfold innerAnodyne; infer_instance
  exact (innerAnodyne.arrow_mk_iso_iff e).mp (inclusion_innerAnodyne n)

theorem spine_le_twoBead (n : ℕ) : spine.{u} (n + 1) ≤ twoBead n := by
  intro q c hc
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h d =>
      have hs := (mem_spine_iff c).mp hc
      let l := SSet.stdSimplex.asOrderHom c 0
      let r := SSet.stdSimplex.asOrderHom c (Fin.last d)
      have hb (j : Fin (d + 1)) : l ≤ SSet.stdSimplex.asOrderHom c j ∧
          SSet.stdSimplex.asOrderHom c j ≤ r :=
        ⟨(SSet.stdSimplex.asOrderHom c).monotone (Fin.zero_le j),
          (SSet.stdSimplex.asOrderHom c).monotone (Fin.le_last j)⟩
      by_cases hr : r.val ≤ n
      · apply Or.inl
        rw [firstFace, SSet.stdSimplex.mem_face_iff]
        intro j
        simp only [Finset.mem_compl, Finset.mem_singleton]
        intro he
        have hj := (hb j).2
        have hv : (SSet.stdSimplex.asOrderHom c j).val = n + 1 :=
          congrArg Fin.val he
        change (SSet.stdSimplex.asOrderHom c j).val ≤ r.val at hj
        omega
      · apply Or.inr
        rw [lastEdge, SSet.stdSimplex.mem_face_iff]
        intro j
        simp only [Finset.mem_insert, Finset.mem_singleton]
        have ht : r.val < n + 2 := r.isLt
        have hsmall : r.val ≤ l.val + 1 := hs
        have hj := hb j
        have hleft : l.val ≤ (SSet.stdSimplex.asOrderHom c j).val := hj.1
        have hright : (SSet.stdSimplex.asOrderHom c j).val ≤ r.val := hj.2
        by_cases he : (SSet.stdSimplex.asOrderHom c j).val = n
        · exact Or.inl (Fin.ext he)
        · apply Or.inr
          apply Fin.ext
          change (SSet.stdSimplex.asOrderHom c j).val = n + 1
          omega

theorem firstFace_sup_spine (n : ℕ) : firstFace.{u} n ⊔ spine (n + 1) = twoBead n := by
  apply le_antisymm
  · exact sup_le le_sup_left (spine_le_twoBead n)
  · exact sup_le le_sup_left
      (le_trans (edgeFace_le (Fin.last n)) le_sup_right)

theorem inclusion_categorical_weak (n : ℕ) : weakCategoricalEquivalences (twoBead.{u} n).ι := by
  rw [← firstFace_sup_spine]
  let F := firstFace.{u} n
  let S := spine.{u} (n + 1)
  have sq : SSet.Subcomplex.BicartSq (F ⊓ S) F S (F ⊔ S) := ⟨rfl, rfl⟩
  have hi : weakCategoricalEquivalences
      (SSet.Subcomplex.homOfLE (inf_le_left : F ⊓ S ≤ F)) :=
    DaggerNativeInnerJoyalMappingWeak.innerAnodyne_weak _ (intersection_innerAnodyne n)
  let j := SSet.Subcomplex.homOfLE (le_sup_right : S ≤ F ⊔ S)
  have hj : weakCategoricalEquivalences j :=
    DaggerNativeOriginalWeakMonoPushout.weak_of_isPushout sq.isPushout hi
  have hfac : j ≫ (F ⊔ S).ι = S.ι := SSet.Subcomplex.homOfLE_ι _
  exact weakCategoricalEquivalences.of_precomp j (F ⊔ S).ι hj
    (hfac.symm ▸ DaggerNativeStandardSpineInner.inclusion_categorical_weak (n + 1))

end
end DaggerNativeTwoBeadSpineGeometry
