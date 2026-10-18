import RigidificationCofFacets

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.PathFacets

open SimplicialThickening

variable {J K : Type u} [LinearOrder J] [LinearOrder K]

/-- Omitted vertices in the actual nerve of the original Path poset. -/
def omitted (i j k : K) : (hom i j).Subcomplex where
  obj _ := {γ | ∀ t, k ∉ (γ.obj t).I}
  map α _ h t := h (α.unop.toOrderHom t)

@[simp] theorem mem_omitted (i j k : K) (q : SimplexCategoryᵒᵖ)
    (γ : (hom i j).obj q) :
    γ ∈ (omitted i j k).obj q ↔ ∀ t, k ∉ (γ.obj t).I := Iff.rfl

variable (e : J ↪o K) (k : K) (he : Set.range e = {k}ᶜ)

include he in
theorem omitted_ne (a : J) : e a ≠ k := by
  have h : e a ∈ Set.range e := ⟨a, rfl⟩
  rw [he] at h
  exact h

def preimagePath {i j : J} (p : Path (e i) (e j)) : Path i j where
  I := e ⁻¹' p.I
  left := p.left
  right := p.right
  left_le a h := e.le_iff_le.mp (p.left_le (e a) h)
  le_right a h := e.le_iff_le.mp (p.le_right (e a) h)

def preimageChain {i j : J} {q : SimplexCategoryᵒᵖ}
    (γ : (hom (e i) (e j)).obj q) : (hom i j).obj q where
  obj t := preimagePath e (γ.obj t)
  map f := ⟨⟨⟨fun _ h => (γ.map f).1.1.1 h⟩⟩⟩

/-- Its underlying full map is exactly the original thickening functor map. -/
noncomputable def omittedMap (i j : J) : hom i j ⟶ (omitted (e i) (e j) k).toSSet where
  app q γ := ⟨(nerveMap (SimplicialThickening.functorMap e.toOrderHom
    (.mk i) (.mk j))).app q γ, by
      intro t hk
      obtain ⟨a, _, ha⟩ := hk
      exact omitted_ne e k he a ha⟩
  naturality _ _ _ := rfl

@[reassoc (attr := simp)] theorem omittedMap_ι (i j : J) :
    omittedMap e k he i j ≫ (omitted (e i) (e j) k).ι =
      (SimplicialThickening.functor e.toOrderHom).map (.mk i) (.mk j) := rfl

def omittedInverse (i j : J) : (omitted (e i) (e j) k).toSSet ⟶ hom i j where
  app _ γ := preimageChain e γ.val
  naturality _ _ _ := by
    funext γ
    apply nerve.ext_of_isThin
    rfl

theorem omittedMap_inverse (i j : J) :
    omittedMap e k he i j ≫ omittedInverse e k i j = 𝟙 _ := by
  apply NatTrans.ext
  funext q γ
  apply nerve.ext_of_isThin
  funext t
  apply Path.ext
  ext a
  change (e a ∈ e '' (γ.obj t).I) ↔ a ∈ (γ.obj t).I
  exact e.injective.mem_set_image

theorem omittedInverse_map (i j : J) :
    omittedInverse e k i j ≫ omittedMap e k he i j = 𝟙 _ := by
  apply NatTrans.ext
  funext q γ
  apply Subtype.ext
  apply nerve.ext_of_isThin
  funext t
  apply Path.ext
  ext a
  change (a ∈ e '' (e ⁻¹' (γ.val.obj t).I)) ↔ a ∈ (γ.val.obj t).I
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro ha
    have h : a ∈ Set.range e := by
      rw [he]
      exact fun hk => γ.property t (hk ▸ ha)
    obtain ⟨b, rfl⟩ := h
    exact ⟨b, ha, rfl⟩

/-- Full omit/preimage iso, retaining all original chain maps and operators. -/
noncomputable def omittedIso (i j : J) : hom i j ≅ (omitted (e i) (e j) k).toSSet where
  hom := omittedMap e k he i j
  inv := omittedInverse e k i j
  hom_inv_id := omittedMap_inverse e k he i j
  inv_hom_id := omittedInverse_map e k he i j

end DaggerOrdinaryRigidificationCof.PathFacets
