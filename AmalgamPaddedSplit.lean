import AmalgamPaddedInteriorEncoding

/-! Recovering optional endpoint identities by their original color and full typed arrow. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem split_trimmed_head (q : SimplexCategoryᵒᵖ) (c : Bool) (a d : At C B q c)
    (h k : a ⟶ d) (l l' : List (Edge C B q))
    (hc : l.head?.map (fun e ↦ e.1) = some (!c))
    (hc' : l'.head?.map (fun e ↦ e.1) = some (!c))
    (he : trimmedTag C B q c h ++ l = trimmedTag C B q c k ++ l') : h = k ∧ l = l' := by
  classical
  by_cases hh : IsIdentity C B q (tag C B q c h)
  · by_cases hk : IsIdentity C B q (tag C B q c k)
    · exact ⟨trimmedTag_injective C B q c a d (by simp [trimmedTag, hh, hk]),
        by simpa only [trimmedTag, if_pos hh, if_pos hk, List.nil_append] using he⟩
    · have hl : l = tag C B q c k :: l' := by
        simpa only [trimmedTag, if_pos hh, if_neg hk, List.nil_append,
          List.singleton_append] using he
      rw [hl] at hc
      change some c = some (!c) at hc
      cases c <;> cases hc
  · by_cases hk : IsIdentity C B q (tag C B q c k)
    · have hl : tag C B q c h :: l = l' := by
        simpa only [trimmedTag, if_neg hh, if_pos hk, List.nil_append,
          List.singleton_append] using he
      rw [← hl] at hc'
      change some c = some (!c) at hc'
      cases c <;> cases hc'
    · have hs : tag C B q c h = tag C B q c k ∧ l = l' := by
        simpa only [trimmedTag, if_neg hh, if_neg hk, List.singleton_append,
          List.cons.injEq] using he
      exact ⟨tag_injective C B q c a d hs.1, hs.2⟩

theorem split_trimmed_tail (q : SimplexCategoryᵒᵖ) (c : Bool) (a d : At C B q c)
    (h k : a ⟶ d) (l l' : List (Edge C B q))
    (hc : firstColor C B l = some (!c)) (hc' : firstColor C B l' = some (!c))
    (he : l ++ trimmedTag C B q c h = l' ++ trimmedTag C B q c k) : h = k ∧ l = l' := by
  classical
  by_cases hh : IsIdentity C B q (tag C B q c h)
  · by_cases hk : IsIdentity C B q (tag C B q c k)
    · exact ⟨trimmedTag_injective C B q c a d (by simp [trimmedTag, hh, hk]),
        by simpa only [trimmedTag, if_pos hh, if_pos hk, List.append_nil] using he⟩
    · have hl : l = l' ++ [tag C B q c k] := by
        simpa only [trimmedTag, if_pos hh, if_neg hk, List.append_nil] using he
      rw [hl, firstColor_append_singleton] at hc
      change some c = some (!c) at hc
      cases c <;> cases hc
  · by_cases hk : IsIdentity C B q (tag C B q c k)
    · have hl : l ++ [tag C B q c h] = l' := by
        simpa only [trimmedTag, if_neg hh, if_pos hk, List.append_nil] using he
      rw [← hl, firstColor_append_singleton] at hc'
      change some c = some (!c) at hc'
      cases c <;> cases hc'
    · have hs : l = l' ∧ tag C B q c h = tag C B q c k :=
        List.append_singleton_inj.mp (by simpa only [trimmedTag, if_neg hh, if_neg hk] using he)
      exact ⟨tag_injective C B q c a d hs.2, hs.1⟩

theorem firstColor_B_zig {q : SimplexCategoryᵒᵖ} : ∀ (n : ℕ)
    (us : Fin n → (b ⟶[SSet] b).obj q) (vs : Fin n → (x ⟶[SSet] x).obj q)
    (h : (b ⟶[SSet] b).obj q),
    firstColor C B (tag C B q true h :: encode C B x b (zig C B x b q n us vs)) =
      some true := by
  intro n
  induction n with
  | zero => intro us vs h; rfl
  | succ n ih =>
    intro us vs h
    simpa only [zig, encode_comp, encode_factorPath, encode_bLoop,
      List.singleton_append, firstColor] using
        ih (fun i ↦ us i.castSucc) (fun i ↦ vs i.castSucc) (us (Fin.last n))

theorem firstColor_zig_positive {q : SimplexCategoryᵒᵖ} (n : ℕ)
    (us : Fin (n + 1) → (b ⟶[SSet] b).obj q)
    (vs : Fin (n + 1) → (x ⟶[SSet] x).obj q) :
    firstColor C B (encode C B x b (zig C B x b q (n + 1) us vs)) = some true := by
  simpa only [zig, encode_comp, encode_factorPath, encode_bLoop,
    List.singleton_append, firstColor] using
      firstColor_B_zig C B x b n (fun i ↦ us i.castSucc) (fun i ↦ vs i.castSucc)
        (us (Fin.last n))

end
end DaggerAmalgamPaddedClassifier
