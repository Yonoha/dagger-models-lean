import RigidificationCofOmitted

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.PathFacets

open SimplicialThickening

variable {J K : Type u} [LinearOrder J] [LinearOrder K]
variable (e : J ↪o K) (i j : J)

def imageHomInverse : hom (e i) (e j) ⟶ hom i j where
  app _ γ := preimageChain e γ
  naturality _ _ _ := by
    funext γ
    apply nerve.ext_of_isThin
    rfl

noncomputable def imageHomMap : hom i j ⟶ hom (e i) (e j) :=
  (SimplicialThickening.functor e.toOrderHom).map (.mk i) (.mk j)

theorem imageHomMap_inverse : imageHomMap e i j ≫ imageHomInverse e i j = 𝟙 _ := by
  apply NatTrans.ext
  funext q γ
  apply nerve.ext_of_isThin
  funext t
  apply Path.ext
  ext a
  exact e.injective.mem_set_image

theorem imageHomInverse_map
    (hc : ∀ x : K, e i ≤ x → x ≤ e j → x ∈ Set.range e) :
    imageHomInverse e i j ≫ imageHomMap e i j = 𝟙 _ := by
  apply NatTrans.ext
  funext q γ
  apply nerve.ext_of_isThin
  funext t
  apply Path.ext
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro ha
    obtain ⟨b, rfl⟩ := hc a ((γ.obj t).left_le a ha) ((γ.obj t).le_right a ha)
    exact ⟨b, ha, rfl⟩

/-- Convexity identifies the FULL original Path Hom, with both actual inverse maps. -/
noncomputable def convexHomIso
    (hc : ∀ x : K, e i ≤ x → x ≤ e j → x ∈ Set.range e) :
    hom i j ≅ hom (e i) (e j) where
  hom := imageHomMap e i j
  inv := imageHomInverse e i j
  hom_inv_id := imageHomMap_inverse e i j
  inv_hom_id := imageHomInverse_map e i j hc

end DaggerOrdinaryRigidificationCof.PathFacets
