import TopCatModelCategory.SSet.Boundary

/-! Attach an actual monomorphic simplex or subobject to an existing native subcomplex. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite
universe u
namespace DaggerNativeSubcomplexAttachmentPushout
noncomputable section

theorem attachment_isPushout {X K : SSet.{u}} (H D : X.Subcomplex) (b : K ⟶ X)
    [Mono b] (hH : H ≤ D) (hb : SSet.Subcomplex.range b ≤ D)
    (hcover : H ⊔ SSet.Subcomplex.range b = D) :
    IsPushout (H.fromPreimage b) (H.preimage b).ι
      (SSet.Subcomplex.homOfLE hH) (SSet.Subcomplex.lift b hb) := by
  apply IsPushout.of_isColimit
    (c := PushoutCocone.mk (SSet.Subcomplex.homOfLE hH)
      (SSet.Subcomplex.lift b hb) (by rfl))
  apply evaluationJointlyReflectsColimits _
  intro k
  apply (PushoutCocone.isColimitMapCoconeEquiv _ _).2
  apply IsPushout.isColimit
  dsimp
  refine Types.isPushout_of_isPullback_of_mono (X₅ := X.obj k) (k := Subtype.val)
    (r' := Subtype.val) (b' := b.app k) ?_ rfl rfl ?_ ?_
  · exact Types.isPullback_of_eq_setPreimage (b.app k) (H.obj k) rfl
  · apply Set.eq_univ_of_forall
    rintro ⟨x, hx⟩
    have hc : x ∈ (H ⊔ SSet.Subcomplex.range b).obj k := by
      rw [hcover]
      exact hx
    rcases hc with hh | ⟨y, hy⟩
    · exact Or.inl ⟨⟨x, hh⟩, rfl⟩
    · exact Or.inr ⟨y, Subtype.ext hy⟩
  · intro x y _ _ h
    exact ((CategoryTheory.mono_iff_injective (b.app k)).mp
      ((NatTrans.mono_iff_mono_app b).mp inferInstance k)) h

end
end DaggerNativeSubcomplexAttachmentPushout
