import AmalgamPaddedTrimNormal

/-! The full original critical union is exactly failure of the interior identity-free condition. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem identity_Bloop_iff (q : SimplexCategoryᵒᵖ) (h : (b ⟶[SSet] b).obj q) :
    IsIdentity C B q (tag C B q true h) ↔ h = (eId SSet b).app q PUnit.unit :=
  isIdentity_loop_iff C B q true b h

theorem identity_Cloop_iff (q : SimplexCategoryᵒᵖ) (h : (x ⟶[SSet] x).obj q) :
    IsIdentity C B q (tag C B q false h) ↔ h = (eId SSet x).app q PUnit.unit :=
  isIdentity_loop_iff C B q false x h

theorem identityFree_zig_iff (q : SimplexCategoryᵒᵖ) : ∀ (n : ℕ)
    (us : Fin n → (b ⟶[SSet] b).obj q) (vs : Fin n → (x ⟶[SSet] x).obj q),
    IdentityFree C B q (encode C B x b (zig C B x b q n us vs)) ↔
      (∀ i, us i ≠ (eId SSet b).app q PUnit.unit) ∧
        ∀ i, vs i ≠ (eId SSet x).app q PUnit.unit := by
  intro n
  induction n with
  | zero => intro us vs; simp [zig, IdentityFree]
  | succ n ih =>
    intro us vs
    have hs : IdentityFree C B q (encode C B x b (zig C B x b q (n + 1) us vs)) ↔
        vs (Fin.last n) ≠ (eId SSet x).app q PUnit.unit ∧
        us (Fin.last n) ≠ (eId SSet b).app q PUnit.unit ∧
        IdentityFree C B q (encode C B x b (zig C B x b q n
          (fun i ↦ us i.castSucc) (fun i ↦ vs i.castSucc))) := by
      simp only [zig, encode_comp, encode_factorPath, encode_bLoop,
        List.singleton_append, identityFree_cons_iff, identity_Bloop_iff, identity_Cloop_iff]
    rw [hs, ih]
    constructor
    · rintro ⟨hv, hu, hu', hv'⟩
      exact ⟨fun i ↦ Fin.lastCases hu hu' i, fun i ↦ Fin.lastCases hv hv' i⟩
    · rintro ⟨hu, hv⟩
      exact ⟨hv _, hu _, (fun i ↦ hu i.castSucc), fun i ↦ hv i.castSucc⟩

theorem identityFree_zag_iff (q : SimplexCategoryᵒᵖ) : ∀ (n : ℕ)
    (vs : Fin n → (x ⟶[SSet] x).obj q) (us : Fin n → (b ⟶[SSet] b).obj q),
    IdentityFree C B q (encode C B x b (zag C B x b q n vs us)) ↔
      (∀ i, vs i ≠ (eId SSet x).app q PUnit.unit) ∧
        ∀ i, us i ≠ (eId SSet b).app q PUnit.unit := by
  intro n
  induction n with
  | zero => intro vs us; simp [zag, IdentityFree]
  | succ n ih =>
    intro vs us
    have hs : IdentityFree C B q (encode C B x b (zag C B x b q (n + 1) vs us)) ↔
        us (Fin.last n) ≠ (eId SSet b).app q PUnit.unit ∧
        vs (Fin.last n) ≠ (eId SSet x).app q PUnit.unit ∧
        IdentityFree C B q (encode C B x b (zag C B x b q n
          (fun i ↦ vs i.castSucc) (fun i ↦ us i.castSucc))) := by
      simp only [zag, encode_comp, encode_factorPath, encode_bLoop,
        List.singleton_append, identityFree_cons_iff, identity_Bloop_iff, identity_Cloop_iff]
    rw [hs, ih]
    constructor
    · rintro ⟨hu, hv, hv', hu'⟩
      exact ⟨fun i ↦ Fin.lastCases hv hv' i, fun i ↦ Fin.lastCases hu hu' i⟩
    · rintro ⟨hv, hu⟩
      exact ⟨hu _, hv _, (fun i ↦ hv i.castSucc), fun i ↦ hu i.castSucc⟩

theorem middleFree_decodeOO_iff (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (h : RawOO C B x b q a d r) :
    MiddleFree C B (encode C B x b (decodeOO C B x b q a d r h)) ↔
      ¬ criticalOO C B x b q a d r h := by
  cases r with
  | zero => simp [MiddleFree, PrefixFree, decodeOO, criticalOO]
  | succ n =>
    have hs : MiddleFree C B (encode C B x b (decodeOO C B x b q a d (n + 1) h)) ↔
        h.2.1 (Fin.last n) ≠ (eId SSet b).app q PUnit.unit ∧
        IdentityFree C B q (encode C B x b (zig C B x b q n
          (fun i ↦ h.2.1 i.castSucc) h.2.2.1)) := by
      simp only [MiddleFree, decodeOO, encode_comp, encode_factorPath, encode_bLoop,
        List.cons_append, List.nil_append, List.tail_cons]
      change PrefixFree C B
        ((tag C B q true (h.2.1 (Fin.last n)) :: encode C B x b
          (zig C B x b q n (fun i ↦ h.2.1 i.castSucc) h.2.2.1)) ++
          [tag C B q false h.1]) ↔ _
      rw [prefixFree_append_singleton, identityFree_cons_iff, identity_Bloop_iff]
    rw [hs, identityFree_zig_iff]
    simp only [criticalOO, not_or, not_exists]
    constructor
    · rintro ⟨hl, hu, hv⟩
      exact ⟨fun i ↦ Fin.lastCases hl hu i, hv⟩
    · rintro ⟨hu, hv⟩
      exact ⟨hu _, (fun i ↦ hu i.castSucc), hv⟩

theorem middleFree_decodeON_iff (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (r : ℕ)
    (h : RawON C B x b q a w r) :
    MiddleFree C B (encode C B x b (decodeON C B x b q a w r h)) ↔
      ¬ criticalON C B x b q a w r h := by
  simp only [MiddleFree, decodeON, encode_comp, encode_factorPath, encode_bEnd,
    List.singleton_append, List.tail_cons]
  rw [prefixFree_append_singleton, identityFree_zig_iff]
  simp [criticalON]

theorem middleFree_decodeNO_iff (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (r : ℕ)
    (h : RawNO C B x b q z d r) :
    MiddleFree C B (encode C B x b (decodeNO C B x b q z d r h)) ↔
      ¬ criticalNO C B x b q z d r h := by
  simp only [MiddleFree, decodeNO, encode_comp, encode_factorPath, encode_bStart,
    List.singleton_append, List.tail_cons]
  rw [prefixFree_append_singleton, identityFree_zag_iff]
  simp [criticalNO]

theorem middleFree_decodeNN_iff (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (r : ℕ)
    (h : RawNN C B x b q z w r) :
    MiddleFree C B (encode C B x b (decodeNN C B x b q z w r h)) ↔
      ¬ criticalNN C B x b q z w r h := by
  cases r with
  | zero => simp [MiddleFree, PrefixFree, decodeNN, criticalNN]
  | succ n =>
    have hs : MiddleFree C B (encode C B x b (decodeNN C B x b q z w (n + 1) h)) ↔
        h.2.1 (Fin.last n) ≠ (eId SSet x).app q PUnit.unit ∧
        IdentityFree C B q (encode C B x b (zag C B x b q n
          (fun i ↦ h.2.1 i.castSucc) h.2.2.1)) := by
      simp only [MiddleFree, decodeNN, encode_comp, encode_factorPath,
        encode_bStart, encode_bEnd, List.cons_append, List.nil_append, List.tail_cons]
      change PrefixFree C B
        ((tag C B q false (h.2.1 (Fin.last n)) :: encode C B x b
          (zag C B x b q n (fun i ↦ h.2.1 i.castSucc) h.2.2.1)) ++
          [tag C B q true h.1]) ↔ _
      rw [prefixFree_append_singleton, identityFree_cons_iff, identity_Cloop_iff]
    rw [hs, identityFree_zag_iff]
    simp only [criticalNN, not_or, not_exists]
    constructor
    · rintro ⟨hl, hv, hu⟩
      exact ⟨fun i ↦ Fin.lastCases hl hv i, hu⟩
    · rintro ⟨hv, hu⟩
      exact ⟨hv _, (fun i ↦ hv i.castSucc), hu⟩

end
end DaggerAmalgamPaddedClassifier
