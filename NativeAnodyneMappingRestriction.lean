import TopCatModelCategory.ModelCategorySSet
import TopCatModelCategory.SSet.Fibrations

/-! Native anodyne parameter restriction into a Kan target is a genuine trivial fibration. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MonoidalClosed HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeAnodyneMappingRestriction
noncomputable section

theorem pushout_product_anodyne {A B K L : SSet.{u}} (i : A ⟶ B) (f : K ⟶ L)
    [Mono f] (hi : SSet.anodyneExtensions i) :
    SSet.anodyneExtensions (SSet.fromPushoutProduct i f) := by
  let t : SSet.PushoutTensor i f :=
    { pt := pushout (i ▷ K) (A ◁ f)
      inl := pushout.inl _ _
      inr := pushout.inr _ _
      isPushout := IsPushout.of_hasPushout _ _ }
  have ht : t.ι = SSet.fromPushoutProduct i f := by
    apply pushout.hom_ext
    · simpa only [t, SSet.fromPushoutProduct, pushout.inl_desc] using t.inl_ι
    · simpa only [t, SSet.fromPushoutProduct, pushout.inr_desc] using t.inr_ι
  rw [← ht]
  exact SSet.anodyneExtensions.pushoutTensorι₁ t hi

theorem anodyne_restriction_trivialFibration {A B : SSet.{u}} (i : A ⟶ B)
    (hi : SSet.anodyneExtensions i) (Z : SSet.{u}) [IsFibrant Z] :
    trivialFibrations SSet.{u} ((MonoidalClosed.pre i).app Z) := by
  have hp : Fibration (C := SSet.{u}) (terminal.from Z : Z ⟶ ⊤_ SSet.{u}) :=
    (isFibrant_iff_of_isTerminal (C := SSet.{u}) _ terminalIsTerminal).1 inferInstance
  apply ((trivialFibrations SSet.{u}).arrow_mk_iso_iff
    (SSet.ihomToPullbackTerminalFromArrowIso i Z)).mp
  rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
  intro K L f hf
  obtain ⟨n⟩ := hf
  rw [SSet.hasLiftingProperty_iHomToPullback_iff]
  exact @SSet.anodyneExtensions.hasLeftLiftingProperty _ _ _
    (pushout_product_anodyne i (SSet.boundary n).ι hi) Z (⊤_ SSet.{u})
    (terminal.from Z) hp

end
end DaggerNativeAnodyneMappingRestriction
