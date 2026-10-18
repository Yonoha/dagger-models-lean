import DaggerModels.OrdinaryRigidification
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.CategoryTheory.Subfunctor.Image

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof

namespace PathFacets

open SimplicialThickening

variable {J : Type u} [LinearOrder J]

abbrev hom (i j : J) : SSet.{u} := nerve (Path i j)

instance path_isThin (i j : J) : Quiver.IsThin (Path i j) := by
  intro p q
  exact ⟨fun f g => InducedCategory.Hom.ext (Subsingleton.elim _ _)⟩

/-- The original Path nerve cut, with the same cut vertex at every chain entry. -/
def cut (i j k : J) : (hom i j).Subcomplex where
  obj _ := {γ | ∀ t, k ∈ (γ.obj t).I}
  map α _ h t := h (α.unop.toOrderHom t)

@[simp] theorem mem_cut (i j k : J) (q : SimplexCategoryᵒᵖ)
    (γ : (hom i j).obj q) : γ ∈ (cut i j k).obj q ↔ ∀ t, k ∈ (γ.obj t).I := Iff.rfl

/-- Original enriched composition: it unions the two Path subsets in each entry. -/
def compose (i k j : J) : hom i k ⊗ hom k j ⟶ hom i j :=
  SimplicialThickening.SimplicialCategory.comp (.mk i) (.mk k) (.mk j)

@[simp] theorem compose_app_obj (i k j : J) (q : SimplexCategoryᵒᵖ)
    (γ : (hom i k).obj q) (δ : (hom k j).obj q) (t : Fin (q.unop.len + 1)) :
    (((compose i k j).app q (γ, δ)).obj t).I = (γ.obj t).I ∪ (δ.obj t).I := rfl

def splitLeft {i j k : J} (p : Path i j) (hk : k ∈ p.I) : Path i k where
  I := p.I ∩ Set.Iic k
  left := ⟨p.left, p.left_le k hk⟩
  right := ⟨hk, le_rfl⟩
  left_le t h := p.left_le t h.1
  le_right _ h := h.2

def splitRight {i j k : J} (p : Path i j) (hk : k ∈ p.I) : Path k j where
  I := p.I ∩ Set.Ici k
  left := ⟨hk, le_rfl⟩
  right := ⟨p.right, p.le_right k hk⟩
  left_le _ h := h.2
  le_right t h := p.le_right t h.1

def splitChainLeft {i j k : J} {q : SimplexCategoryᵒᵖ}
    (γ : (cut i j k).obj q) : (hom i k).obj q where
  obj t := splitLeft (γ.val.obj t) (γ.property t)
  map f := ⟨⟨⟨fun _ h =>
    ⟨(γ.val.map f).1.1.1 h.1, h.2⟩⟩⟩⟩

def splitChainRight {i j k : J} {q : SimplexCategoryᵒᵖ}
    (γ : (cut i j k).obj q) : (hom k j).obj q where
  obj t := splitRight (γ.val.obj t) (γ.property t)
  map f := ⟨⟨⟨fun _ h =>
    ⟨(γ.val.map f).1.1.1 h.1, h.2⟩⟩⟩⟩

def cutMap (i k j : J) : hom i k ⊗ hom k j ⟶ (cut i j k).toSSet where
  app q p := ⟨(compose i k j).app q p, fun t => Or.inl (p.1.obj t).right⟩
  naturality _ _ _ := rfl

@[reassoc (attr := simp)] theorem cutMap_ι (i k j : J) :
    cutMap i k j ≫ (cut i j k).ι = compose i k j := rfl

def cutInverse (i k j : J) : (cut i j k).toSSet ⟶ hom i k ⊗ hom k j where
  app _ γ := (splitChainLeft γ, splitChainRight γ)
  naturality _ _ _ := by
    funext γ
    apply Prod.ext
    · apply nerve.ext_of_isThin
      rfl
    · apply nerve.ext_of_isThin
      rfl

theorem cutMap_inverse (i k j : J) : cutMap i k j ≫ cutInverse i k j = 𝟙 _ := by
  apply NatTrans.ext
  funext q p
  apply Prod.ext
  · apply nerve.ext_of_isThin
    funext t
    apply Path.ext
    ext x
    constructor
    · rintro ⟨h | h, hx⟩
      · exact h
      · have h' := (p.2.obj t).left_le x h
        have : x = k := le_antisymm hx h'
        simpa [this] using (p.1.obj t).right
    · intro h
      exact ⟨Or.inl h, (p.1.obj t).le_right x h⟩
  · apply nerve.ext_of_isThin
    funext t
    apply Path.ext
    ext x
    constructor
    · rintro ⟨h | h, hx⟩
      · have h' := (p.1.obj t).le_right x h
        have : x = k := le_antisymm h' hx
        simpa [this] using (p.2.obj t).left
      · exact h
    · intro h
      exact ⟨Or.inr h, (p.2.obj t).left_le x h⟩

theorem cutInverse_map (i k j : J) : cutInverse i k j ≫ cutMap i k j = 𝟙 _ := by
  ext q γ
  apply Subtype.ext
  apply nerve.ext_of_isThin
  funext t
  apply Path.ext
  ext x
  constructor
  · rintro (h | h) <;> exact h.1
  · intro h
    rcases le_total x k with h' | h'
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h, h'⟩

/-- Full original cut iso; its hom is literally original composition into the cut. -/
def cutIso (i k j : J) : hom i k ⊗ hom k j ≅ (cut i j k).toSSet where
  hom := cutMap i k j
  inv := cutInverse i k j
  hom_inv_id := cutMap_inverse i k j
  inv_hom_id := cutInverse_map i k j

end PathFacets

end DaggerOrdinaryRigidificationCof
