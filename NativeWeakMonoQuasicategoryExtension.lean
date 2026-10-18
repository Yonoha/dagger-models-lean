import NativeWalkingHomotopySectionCorrection
import NativeIhomHoObjects

/-! Every map from the original domain of a weak mono to a quasi-category extends exactly. -/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerNativeWalkingHomotopySectionCorrection DaggerNativeIhomHoObjects
open DaggerNativeJoyalMappingTest DaggerNativeWalkingRetractionMappingEquivalence
universe u
namespace DaggerNativeWeakMonoQuasicategoryExtension
noncomputable section

theorem extension_of_restriction_section {A B Z : SSet.{u}} (i : A ⟶ B)
    (s : (ihom A).obj Z ⟶ (ihom B).obj Z)
    (hs : s ≫ (MonoidalClosed.pre i).app Z = 𝟙 _) (a : A ⟶ Z) :
    ∃ b : B ⟶ Z, i ≫ b = a := by
  let b := (homObjectEquiv B Z).symm ((SSet.hoFunctor.map s).toFunctor.obj (homObject a))
  have hb : homObject b = (SSet.hoFunctor.map s).toFunctor.obj (homObject a) :=
    (homObjectEquiv B Z).apply_symm_apply _
  have hfun : (SSet.hoFunctor.map s).toFunctor ⋙ (preHoFunctor i Z) = 𝟭 _ := by
    change (SSet.hoFunctor.map s).toFunctor ⋙
      (SSet.hoFunctor.map ((MonoidalClosed.pre i).app Z)).toFunctor = 𝟭 _
    rw [← Cat.Hom.comp_toFunctor, ← SSet.hoFunctor.map_comp, hs, SSet.hoFunctor.map_id]
    rfl
  refine ⟨b, ?_⟩
  apply (homObjectEquiv A Z).injective
  change homObject (i ≫ b) = homObject a
  rw [← pre_obj, hb]
  exact congrArg (fun F ↦ F.obj (homObject a)) hfun

theorem weak_mono_extension {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (hi : weakCategoricalEquivalences i) (Z : SSet.{u}) [Z.Quasicategory] (a : A ⟶ Z) :
    ∃ b : B ⟶ Z, i ≫ b = a := by
  obtain ⟨s, hs⟩ := weak_mono_restriction_section i hi Z
  exact extension_of_restriction_section i s hs a

theorem weak_mono_terminal_lifting {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (hi : weakCategoricalEquivalences i) (Z : SSet.{u}) [Z.Quasicategory] :
    HasLiftingProperty i (terminal.from Z) := by
  constructor
  intro a b sq
  obtain ⟨l, hl⟩ := weak_mono_extension i hi Z a
  exact ⟨l, hl, terminalIsTerminal.hom_ext _ _⟩

end
end DaggerNativeWeakMonoQuasicategoryExtension
