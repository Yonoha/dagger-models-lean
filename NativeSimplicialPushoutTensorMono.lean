import OriginalSimplicialCotensorRestriction

/-! Reuse Mathlib's TYPE pushout/pullback mono criterion, degree by degree,
to prove monomorphy of EVERY original simplicial pushout-tensor of TWO monos.
-/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory
universe u
namespace DaggerNativeSimplicialPushoutTensorMono
noncomputable section

theorem mono_ι {A B K L : SSet.{u}} (j : A ⟶ B) (f : K ⟶ L) [Mono j] [Mono f]
    (t : SSet.PushoutTensor j f) : Mono t.ι := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro q
  have hj : Function.Injective (j.app q) := (mono_iff_injective _).mp inferInstance
  have hf : Function.Injective (f.app q) := (mono_iff_injective _).mp inferInstance
  have hpo := IsPushout.map (SSet.evaluation.obj q) t.isPushout
  have hpb : IsPullback ((j ▷ K).app q) ((A ◁ f).app q)
      ((B ◁ f).app q) ((j ▷ L).app q) := by
    apply IsPullback.of_isLimit
      (c := PullbackCone.mk ((j ▷ K).app q) ((A ◁ f).app q) (by funext z; rfl))
    refine PullbackCone.IsLimit.mk _
      (fun s ↦ fun w ↦ ((s.snd w).1, (s.fst w).2)) ?_ ?_ ?_
    · intro s
      funext w
      apply Prod.ext
      · exact (congrArg (fun z : B.obj q × L.obj q ↦ z.1)
          (congrFun s.condition w)).symm
      · rfl
    · intro s
      funext w
      apply Prod.ext
      · rfl
      · exact congrArg (fun z : B.obj q × L.obj q ↦ z.2) (congrFun s.condition w)
    · intro s m hm hn
      funext w
      exact Prod.ext (congrArg (fun z : A.obj q × L.obj q ↦ z.1) (congrFun hn w))
        (congrArg (fun z : B.obj q × K.obj q ↦ z.2) (congrFun hm w))
  have hr : Mono ((B ◁ f).app q) := (mono_iff_injective _).mpr (by
    intro a b h
    exact Prod.ext (congrArg (fun z : B.obj q × L.obj q ↦ z.1) h)
      (hf (congrArg (fun z : B.obj q × L.obj q ↦ z.2) h)))
  have hb : Function.Injective ((j ▷ L).app q) := by
    intro a b h
    exact Prod.ext (hj (congrArg (fun z : B.obj q × L.obj q ↦ z.1) h))
      (congrArg (fun z : B.obj q × L.obj q ↦ z.2) h)
  have h₁ : t.inl.app q ≫ t.ι.app q = (B ◁ f).app q :=
    congrArg (fun g ↦ g.app q) t.inl_ι
  have h₂ : t.inr.app q ≫ t.ι.app q = (j ▷ L).app q :=
    congrArg (fun g ↦ g.app q) t.inr_ι
  exact Types.mono_of_isPushout_of_isPullback hpo hpb h₁ h₂
    (fun a b _ _ h ↦ hb h)

end
end DaggerNativeSimplicialPushoutTensorMono
