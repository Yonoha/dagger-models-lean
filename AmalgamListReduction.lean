import AmalgamReduction
import ListReduction

/-! Full original color/endpoint/simplex labels in a list encoding of one-step reduction. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation

universe u

namespace DaggerAmalgamReduction

variable (B B' : SimplicialCat.{u, u}) (b : B.Obj) (b' : B'.Obj)
variable (q : SimplexCategoryᵒᵖ)

abbrev At (c : Bool) := SimplicialEnrichment.At (factor B B' c).Obj q

def tag (c : Bool) {x y : At B B' q c} (h : x ⟶ y) : Edge B B' q := ⟨c, x, y, h⟩

inductive IsIdentity : Edge B B' q → Prop
  | intro (c : Bool) (x : At B B' q c) : IsIdentity (tag B B' q c (𝟙 x))

inductive Merge : Edge B B' q → Edge B B' q → Edge B B' q → Prop
  | intro (c : Bool) {x y z : At B B' q c} (h : x ⟶ y) (k : y ⟶ z) :
      Merge (tag B B' q c h) (tag B B' q c k) (tag B B' q c (h ≫ k))

theorem merge_left_unit {a d e : Edge B B' q}
    (hi : IsIdentity B B' q a) (hm : Merge B B' q a d e) : e = d := by
  cases hi
  cases hm
  simp [tag]

theorem merge_right_unit {a d e : Edge B B' q}
    (hi : IsIdentity B B' q d) (hm : Merge B B' q a d e) : e = a := by
  cases hi
  cases hm
  simp [tag]

theorem merge_unique {a d e e' : Edge B B' q}
    (h : Merge B B' q a d e) (h' : Merge B B' q a d e') : e = e' := by
  cases h
  cases h'
  rfl

theorem merge_assoc {a d e f g : Edge B B' q}
    (h : Merge B B' q a d e) (h' : Merge B B' q d f g) :
    ∃ k, Merge B B' q e f k ∧ Merge B B' q a g k := by
  cases h
  cases h'
  refine ⟨_, Merge.intro _ _ _, ?_⟩
  simpa only [Category.assoc] using (Merge.intro _ _ _)

abbrev EncodedRed := ListRed (IsIdentity B B' q) (Merge B B' q)

theorem encoded_diamond {l l₁ l₂ : List (Edge B B' q)}
    (h₁ : EncodedRed B B' q l l₁) (h₂ : EncodedRed B B' q l l₂) :
    ∃ d, Relation.ReflGen (EncodedRed B B' q) l₁ d ∧
      Relation.ReflGen (EncodedRed B B' q) l₂ d :=
  listRed_diamond _ _ (merge_left_unit B B' q) (merge_right_unit B B' q)
    (merge_unique B B' q) (merge_assoc B B' q) h₁ h₂

/-- Snoc paths are encoded in reverse order; composition still uses original h ≫ k. -/
abbrev ReverseEncodedRed := ListRed (IsIdentity B B' q) (fun a d e ↦ Merge B B' q d a e)

theorem reverse_encoded_diamond {l l₁ l₂ : List (Edge B B' q)}
    (h₁ : ReverseEncodedRed B B' q l l₁) (h₂ : ReverseEncodedRed B B' q l l₂) :
    ∃ d, Relation.ReflGen (ReverseEncodedRed B B' q) l₁ d ∧
      Relation.ReflGen (ReverseEncodedRed B B' q) l₂ d := by
  apply listRed_diamond _ _ _ _ _ _ h₁ h₂
  · exact fun hi hm ↦ merge_right_unit B B' q hi hm
  · exact fun hi hm ↦ merge_left_unit B B' q hi hm
  · exact fun h h' ↦ merge_unique B B' q h h'
  · intro a d e f g h h'
    obtain ⟨k, hk, hk'⟩ := merge_assoc B B' q h' h
    exact ⟨k, hk', hk⟩

end DaggerAmalgamReduction
