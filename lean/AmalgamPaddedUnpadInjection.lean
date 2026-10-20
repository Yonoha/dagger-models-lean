import AmalgamPaddedSplit

/-! Injectivity of all four complete interior-to-normal-path maps.
Both endpoint arrows are recovered even when original identity padding disappears. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification DaggerAmalgamNormalForms

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

def unpadOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (h : InteriorOO C B x b q a d r) :
    NormalPath C B x b q (leftObj C B x b a) (leftObj C B x b d) :=
  normalize C B x b (decodeOO C B x b q a d r h.val)

def unpadON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (r : ℕ)
    (h : InteriorON C B x b q a w r) :
    NormalPath C B x b q (leftObj C B x b a) (rightObj C B x b w) :=
  normalize C B x b (decodeON C B x b q a w r h.val)

def unpadNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (r : ℕ)
    (h : InteriorNO C B x b q z d r) :
    NormalPath C B x b q (rightObj C B x b z) (leftObj C B x b d) :=
  normalize C B x b (decodeNO C B x b q z d r h.val)

def unpadNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (r : ℕ)
    (h : InteriorNN C B x b q z w r) :
    NormalPath C B x b q (rightObj C B x b z) (rightObj C B x b w) :=
  normalize C B x b (decodeNN C B x b q z w r h.val)

theorem unpadOO_injective (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ) :
    Function.Injective (unpadOO C B x b q a d r) := by
  intro h k he
  apply Subtype.ext
  have hec := congrArg (fun p ↦ encode C B x b p.val) he
  dsimp only [unpadOO] at hec
  cases r with
  | zero =>
    change encode C B x b (normalize C B x b (factorPath C B x b false q h.val)).val =
      encode C B x b (normalize C B x b (factorPath C B x b false q k.val)).val at hec
    rw [normalize_factor_encode, normalize_factor_encode] at hec
    exact trimmedTag_injective C B q false a d hec
  | succ n =>
    rcases h with ⟨⟨h0, us, vs, h1⟩, hh⟩
    rcases k with ⟨⟨k0, us', vs', k1⟩, hk⟩
    rw [normalize_decodeOO_encode C B x b q a d n _ hh,
      normalize_decodeOO_encode C B x b q a d n _ hk] at hec
    let l := tag C B q true (us (Fin.last n)) ::
      encode C B x b (zig C B x b q n (fun i ↦ us i.castSucc) vs)
    let l' := tag C B q true (us' (Fin.last n)) ::
      encode C B x b (zig C B x b q n (fun i ↦ us' i.castSucc) vs')
    obtain ⟨h1e, hl⟩ := split_trimmed_head C B q false x d h1 k1
      (l ++ trimmedTag C B q false h0) (l' ++ trimmedTag C B q false k0)
      (by simp [l, tag]) (by simp [l', tag]) (by simpa only [List.append_assoc] using hec)
    obtain ⟨h0e, hm⟩ := split_trimmed_tail C B q false a x h0 k0 l l'
      (firstColor_B_zig C B x b n _ _ _) (firstColor_B_zig C B x b n _ _ _) hl
    have hme : tag C B q true (us (Fin.last n)) = tag C B q true (us' (Fin.last n)) ∧
        encode C B x b (zig C B x b q n (fun i ↦ us i.castSucc) vs) =
          encode C B x b (zig C B x b q n (fun i ↦ us' i.castSucc) vs') := List.cons.inj hm
    obtain ⟨hu, hv⟩ := encode_zig_injective C B x b q n _ _ _ _ hme.2
    have hu' : us = us' := by
      funext i
      exact Fin.lastCases (tag_injective C B q true b b hme.1) (fun j ↦ congrFun hu j) i
    cases h1e
    cases h0e
    cases hu'
    cases hv
    rfl

theorem unpadON_injective (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj)
    (hw : w ≠ b) (r : ℕ) : Function.Injective (unpadON C B x b q a w r) := by
  rintro ⟨⟨h0, us, vs, h1⟩, hh⟩ ⟨⟨k0, us', vs', k1⟩, hk⟩ he
  apply Subtype.ext
  have hec := congrArg (fun p ↦ encode C B x b p.val) he
  dsimp only [unpadON] at hec
  rw [normalize_decodeON_encode C B x b q a w hw r _ hh,
    normalize_decodeON_encode C B x b q a w hw r _ hk] at hec
  have hs : tag C B q true h1 = tag C B q true k1 ∧
      encode C B x b (zig C B x b q r us vs) ++ trimmedTag C B q false h0 =
        encode C B x b (zig C B x b q r us' vs') ++ trimmedTag C B q false k0 := List.cons.inj hec
  have h1e := tag_injective C B q true b w hs.1
  cases r with
  | zero =>
    have h0e : h0 = k0 := trimmedTag_injective C B q false a x
      (by simpa only [zig, encode, List.nil_append] using hs.2)
    have hu : us = us' := Subsingleton.elim _ _
    have hv : vs = vs' := Subsingleton.elim _ _
    cases h0e
    cases h1e
    cases hu
    cases hv
    rfl
  | succ n =>
    obtain ⟨h0e, hm⟩ := split_trimmed_tail C B q false a x h0 k0 _ _
      (firstColor_zig_positive C B x b n us vs)
      (firstColor_zig_positive C B x b n us' vs') hs.2
    obtain ⟨hu, hv⟩ := encode_zig_injective C B x b q (n + 1) _ _ _ _ hm
    cases h0e
    cases h1e
    cases hu
    cases hv
    rfl

theorem unpadNO_injective (q : SimplexCategoryᵒᵖ) (z : B.Obj) (hz : z ≠ b)
    (d : C.Obj) (r : ℕ) : Function.Injective (unpadNO C B x b q z d r) := by
  rintro ⟨⟨h0, vs, us, h1⟩, hh⟩ ⟨⟨k0, vs', us', k1⟩, hk⟩ he
  apply Subtype.ext
  have hec := congrArg (fun p ↦ encode C B x b p.val) he
  dsimp only [unpadNO] at hec
  rw [normalize_decodeNO_encode C B x b q z hz d r _ hh,
    normalize_decodeNO_encode C B x b q z hz d r _ hk] at hec
  obtain ⟨h1e, hl⟩ := split_trimmed_head C B q false x d h1 k1 _ _
    (headColor_zag_B C B x b r vs us h0) (headColor_zag_B C B x b r vs' us' k0) hec
  obtain ⟨hm, h0t⟩ := List.append_singleton_inj.mp hl
  have h0e := tag_injective C B q true z b h0t
  obtain ⟨hv, hu⟩ := encode_zag_injective C B x b q r _ _ _ _ hm
  cases h1e
  cases h0e
  cases hv
  cases hu
  rfl

theorem unpadNN_injective (q : SimplexCategoryᵒᵖ) (z w : B.Obj)
    (hz : z ≠ b) (hw : w ≠ b) (r : ℕ) : Function.Injective (unpadNN C B x b q z w r) := by
  intro h k he
  apply Subtype.ext
  have hec := congrArg (fun p ↦ encode C B x b p.val) he
  dsimp only [unpadNN] at hec
  cases r with
  | zero =>
    change encode C B x b (normalize C B x b (factorPath C B x b true q h.val)).val =
      encode C B x b (normalize C B x b (factorPath C B x b true q k.val)).val at hec
    rw [normalize_factor_encode, normalize_factor_encode] at hec
    exact trimmedTag_injective C B q true z w hec
  | succ n =>
    rw [normalize_decodeNN_encode C B x b q z w hz hw n _ h.property,
      normalize_decodeNN_encode C B x b q z w hz hw n _ k.property] at hec
    exact decodeNN_injective C B x b q z w (n + 1) (encode_injective C B x b hec)

end
end DaggerAmalgamPaddedClassifier
