import AmalgamPaddedAppend

/-! Injection of the complete raw data into the original dependent paths.
Every original endpoint arrow and every Fin coordinate is recovered. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem encode_zig_injective (q : SimplexCategoryᵒᵖ) : ∀ (n : ℕ)
    (us us' : Fin n → (b ⟶[SSet] b).obj q) (vs vs' : Fin n → (x ⟶[SSet] x).obj q),
    encode C B x b (zig C B x b q n us vs) =
      encode C B x b (zig C B x b q n us' vs') → us = us' ∧ vs = vs' := by
  intro n
  induction n with
  | zero => intro us us' vs vs' _; exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  | succ n ih =>
    intro us us' vs vs' he
    have hs : tag C B q false (vs (Fin.last n)) = tag C B q false (vs' (Fin.last n)) ∧
        tag C B q true (us (Fin.last n)) = tag C B q true (us' (Fin.last n)) ∧
        encode C B x b (zig C B x b q n (fun i ↦ us i.castSucc) (fun i ↦ vs i.castSucc)) =
          encode C B x b (zig C B x b q n (fun i ↦ us' i.castSucc)
            (fun i ↦ vs' i.castSucc)) := by
      simpa [zig, encode_comp, encode_bLoop] using he
    obtain ⟨hu, hv⟩ := ih _ _ _ _ hs.2.2
    refine ⟨?_, ?_⟩
    · funext i
      exact Fin.lastCases (tag_injective C B q true b b hs.2.1)
        (fun j ↦ congrFun hu j) i
    · funext i
      exact Fin.lastCases (tag_injective C B q false x x hs.1)
        (fun j ↦ congrFun hv j) i

theorem encode_zag_injective (q : SimplexCategoryᵒᵖ) : ∀ (n : ℕ)
    (vs vs' : Fin n → (x ⟶[SSet] x).obj q) (us us' : Fin n → (b ⟶[SSet] b).obj q),
    encode C B x b (zag C B x b q n vs us) =
      encode C B x b (zag C B x b q n vs' us') → vs = vs' ∧ us = us' := by
  intro n
  induction n with
  | zero => intro vs vs' us us' _; exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  | succ n ih =>
    intro vs vs' us us' he
    have hs : tag C B q true (us (Fin.last n)) = tag C B q true (us' (Fin.last n)) ∧
        tag C B q false (vs (Fin.last n)) = tag C B q false (vs' (Fin.last n)) ∧
        encode C B x b (zag C B x b q n (fun i ↦ vs i.castSucc) (fun i ↦ us i.castSucc)) =
          encode C B x b (zag C B x b q n (fun i ↦ vs' i.castSucc)
            (fun i ↦ us' i.castSucc)) := by
      simpa [zag, encode_comp, encode_bLoop] using he
    obtain ⟨hv, hu⟩ := ih _ _ _ _ hs.2.2
    refine ⟨?_, ?_⟩
    · funext i
      exact Fin.lastCases (tag_injective C B q false x x hs.2.1)
        (fun j ↦ congrFun hv j) i
    · funext i
      exact Fin.lastCases (tag_injective C B q true b b hs.1)
        (fun j ↦ congrFun hu j) i

theorem decodeOO_injective (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ) :
    Function.Injective (decodeOO C B x b q a d r) := by
  intro h k hp
  have he := congrArg (encode C B x b) hp
  cases r with
  | zero => exact tag_injective C B q false a d (List.singleton_inj.mp he)
  | succ n =>
    rcases h with ⟨h0, us, vs, h1⟩
    rcases k with ⟨k0, us', vs', k1⟩
    have hs : tag C B q false h1 = tag C B q false k1 ∧
        tag C B q true (us (Fin.last n)) = tag C B q true (us' (Fin.last n)) ∧
        encode C B x b (zig C B x b q n (fun i ↦ us i.castSucc) vs) ++
          [tag C B q false h0] =
        encode C B x b (zig C B x b q n (fun i ↦ us' i.castSucc) vs') ++
          [tag C B q false k0] := by
      simpa [decodeOO, encode_comp, encode_bLoop] using he
    obtain ⟨hm, h0e⟩ := List.append_singleton_inj.mp hs.2.2
    obtain ⟨hu, hv⟩ := encode_zig_injective C B x b q n _ _ _ _ hm
    have hu' : us = us' := by
      funext i
      exact Fin.lastCases (tag_injective C B q true b b hs.2.1)
        (fun j ↦ congrFun hu j) i
    cases hu'
    cases hv
    cases tag_injective C B q false a x h0e
    cases tag_injective C B q false x d hs.1
    rfl

theorem decodeON_injective (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (r : ℕ) :
    Function.Injective (decodeON C B x b q a w r) := by
  rintro ⟨h0, us, vs, h1⟩ ⟨k0, us', vs', k1⟩ hp
  have he := congrArg (encode C B x b) hp
  have hs : tag C B q true h1 = tag C B q true k1 ∧
      encode C B x b (zig C B x b q r us vs) ++ [tag C B q false h0] =
        encode C B x b (zig C B x b q r us' vs') ++ [tag C B q false k0] := by
    simpa [decodeON, encode_comp, encode_bEnd] using he
  obtain ⟨hm, h0e⟩ := List.append_singleton_inj.mp hs.2
  obtain ⟨hu, hv⟩ := encode_zig_injective C B x b q r _ _ _ _ hm
  cases hu
  cases hv
  cases tag_injective C B q false a x h0e
  cases tag_injective C B q true b w hs.1
  rfl

theorem decodeNO_injective (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (r : ℕ) :
    Function.Injective (decodeNO C B x b q z d r) := by
  rintro ⟨h0, vs, us, h1⟩ ⟨k0, vs', us', k1⟩ hp
  have he := congrArg (encode C B x b) hp
  have hs : tag C B q false h1 = tag C B q false k1 ∧
      encode C B x b (zag C B x b q r vs us) ++ [tag C B q true h0] =
        encode C B x b (zag C B x b q r vs' us') ++ [tag C B q true k0] := by
    simpa [decodeNO, encode_comp, encode_bStart] using he
  obtain ⟨hm, h0e⟩ := List.append_singleton_inj.mp hs.2
  obtain ⟨hv, hu⟩ := encode_zag_injective C B x b q r _ _ _ _ hm
  cases hv
  cases hu
  cases tag_injective C B q true z b h0e
  cases tag_injective C B q false x d hs.1
  rfl

theorem decodeNN_injective (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (r : ℕ) :
    Function.Injective (decodeNN C B x b q z w r) := by
  intro h k hp
  have he := congrArg (encode C B x b) hp
  cases r with
  | zero => exact tag_injective C B q true z w (List.singleton_inj.mp he)
  | succ n =>
    rcases h with ⟨h0, vs, us, h1⟩
    rcases k with ⟨k0, vs', us', k1⟩
    have hs : tag C B q true h1 = tag C B q true k1 ∧
        tag C B q false (vs (Fin.last n)) = tag C B q false (vs' (Fin.last n)) ∧
        encode C B x b (zag C B x b q n (fun i ↦ vs i.castSucc) us) ++
          [tag C B q true h0] =
        encode C B x b (zag C B x b q n (fun i ↦ vs' i.castSucc) us') ++
          [tag C B q true k0] := by
      simpa [decodeNN, encode_comp, encode_bEnd, encode_bStart] using he
    obtain ⟨hm, h0e⟩ := List.append_singleton_inj.mp hs.2.2
    obtain ⟨hv, hu⟩ := encode_zag_injective C B x b q n _ _ _ _ hm
    have hv' : vs = vs' := by
      funext i
      exact Fin.lastCases (tag_injective C B q false x x hs.2.1)
        (fun j ↦ congrFun hv j) i
    cases hv'
    cases hu
    cases tag_injective C B q true z b h0e
    cases tag_injective C B q true b w hs.1
    rfl

end
end DaggerAmalgamPaddedClassifier
