import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! The two-copy pushout replacement used by Part I `bg.lem.reduction`.
This is a universal-property statement in an arbitrary category. -/

open CategoryTheory Limits

universe v u

namespace DaggerModels.TwoCopyPushoutReduction

noncomputable section

variable {D : Type u} [Category.{v} D]
  {S A₀ A₁ A B₀ B₁ B C Q R : D}
  {s₀ : S ⟶ A₀} {s₁ : S ⟶ A₁} {t₀ : S ⟶ B₀} {t₁ : S ⟶ B₁}
  {k₀ : A₀ ⟶ A} {k₁ : A₁ ⟶ A} {j₀ : B₀ ⟶ B} {j₁ : B₁ ⟶ B}
  {i₀ : A₀ ⟶ B₀} {i₁ : A₁ ⟶ B₁} {d : A ⟶ B} {a : A ⟶ C}
  {b₀ : B₀ ⟶ Q} {c₀ : C ⟶ Q} {b₁ : B₁ ⟶ R} {c₁ : Q ⟶ R}
  (hA : IsPushout s₀ s₁ k₀ k₁) (hB : IsPushout t₀ t₁ j₀ j₁)
  (hs₀ : s₀ ≫ i₀ = t₀) (hs₁ : s₁ ≫ i₁ = t₁)
  (hd₀ : k₀ ≫ d = i₀ ≫ j₀) (hd₁ : k₁ ≫ d = i₁ ≫ j₁)
  (hQ : IsPushout i₀ (k₀ ≫ a) b₀ c₀)
  (hR : IsPushout i₁ (k₁ ≫ a ≫ c₀) b₁ c₁)

include hA hs₀ hs₁ hQ hR in
lemma copyCondition : t₀ ≫ (b₀ ≫ c₁) = t₁ ≫ b₁ := by
  rw [← hs₀, ← hs₁]
  calc
    (s₀ ≫ i₀) ≫ (b₀ ≫ c₁) = s₀ ≫ (k₀ ≫ a) ≫ c₀ ≫ c₁ := by
      simpa only [Category.assoc] using congrArg (fun f ↦ s₀ ≫ f ≫ c₁) hQ.w
    _ = s₁ ≫ k₁ ≫ a ≫ c₀ ≫ c₁ := by
      simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ a ≫ c₀ ≫ c₁) hA.w
    _ = (s₁ ≫ i₁) ≫ b₁ := by
      simpa only [Category.assoc] using (congrArg (fun f ↦ s₁ ≫ f) hR.w).symm

/-- The two ordinary copies supply the lower leg of the resulting pushout. -/
def combined : B ⟶ R :=
  hB.desc (b₀ ≫ c₁) b₁ (copyCondition hA hs₀ hs₁ hQ hR)

@[reassoc (attr := simp)]
lemma combined_inl : j₀ ≫ combined hA hB hs₀ hs₁ hQ hR = b₀ ≫ c₁ := by
  apply IsPushout.inl_desc

@[reassoc (attr := simp)]
lemma combined_inr : j₁ ≫ combined hA hB hs₀ hs₁ hQ hR = b₁ := by
  apply IsPushout.inr_desc

include hd₀ hd₁ in
lemma outerCondition : d ≫ combined hA hB hs₀ hs₁ hQ hR = a ≫ c₀ ≫ c₁ := by
  apply hA.hom_ext
  · rw [← Category.assoc, hd₀]
    simp only [Category.assoc, combined_inl]
    simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ c₁) hQ.w
  · rw [← Category.assoc, hd₁]
    simp only [Category.assoc, combined_inr]
    simpa only [Category.assoc] using hR.w

include hd₀ hd₁ in
/-- Replacing a pushout of two copies by the two successive attachments preserves the full UP. -/
theorem isPushout : IsPushout d a (combined hA hB hs₀ hs₁ hQ hR) (c₀ ≫ c₁) := by
  let w := outerCondition hA hB hs₀ hs₁ hd₀ hd₁ hQ hR
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ w)
  let first (s : PushoutCocone d a) : Q ⟶ s.pt :=
    hQ.desc (j₀ ≫ s.inl) s.inr (by
      rw [← Category.assoc, ← hd₀, Category.assoc, s.condition]
      simp only [Category.assoc])
  let second (s : PushoutCocone d a) : R ⟶ s.pt :=
    hR.desc (j₁ ≫ s.inl) (first s) (by
      rw [← Category.assoc, ← hd₁, Category.assoc, s.condition]
      simp only [Category.assoc, first, IsPushout.inr_desc])
  have facB (s : PushoutCocone d a) :
      combined hA hB hs₀ hs₁ hQ hR ≫ second s = s.inl := by
    apply hB.hom_ext
    · simp only [← Category.assoc, combined_inl]
      simp only [Category.assoc, second, IsPushout.inr_desc, first, IsPushout.inl_desc]
    · simp only [← Category.assoc, combined_inr, second, IsPushout.inl_desc]
  have facC (s : PushoutCocone d a) : (c₀ ≫ c₁) ≫ second s = s.inr := by
    simp only [Category.assoc, second, IsPushout.inr_desc, first, IsPushout.inr_desc]
  refine PushoutCocone.IsColimit.mk w second facB facC ?_
  intro s m hmB hmC
  apply hR.hom_ext
  · have e := congrArg (fun f ↦ j₁ ≫ f) hmB
    simpa only [← Category.assoc, combined_inr, second, IsPushout.inl_desc] using e
  · apply hQ.hom_ext
    · have e := congrArg (fun f ↦ j₀ ≫ f) hmB
      have e' : (b₀ ≫ c₁) ≫ m = j₀ ≫ s.inl := by
        simpa only [← Category.assoc, combined_inl] using e
      simpa only [Category.assoc, second, IsPushout.inr_desc, first,
        IsPushout.inl_desc] using e'
    · simpa only [Category.assoc, second, IsPushout.inr_desc, first,
        IsPushout.inr_desc] using hmC

end
end DaggerModels.TwoCopyPushoutReduction
