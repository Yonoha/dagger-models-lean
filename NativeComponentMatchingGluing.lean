import NativeComponentPartialMatchingComparison
import NativeHorizontalPushoutComponents
import NativeHorizontalPiParameterIso

/-! The canonical component comparison glues over actual pushouts and transports by isomorphisms. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeComponentPartialMatchingComparison
open DaggerNativeHorizontalPushoutComponents DaggerNativeHorizontalPiParameterIso
open DaggerNativePartialFaceUnionGeometry
universe u
namespace DaggerNativeComponentMatchingGluing
noncomputable section

theorem componentComparison_bijective_of_pushout {K₀ K₁ K₂ K₃ : SSet.{u}}
    {i : K₀ ⟶ K₁} {j : K₀ ⟶ K₂} {a : K₁ ⟶ K₃} {b : K₂ ⟶ K₃}
    (h : IsPushout i j a b) (X : BiSSet.{u})
    (h₀ : Function.Injective (componentComparison K₀ X))
    (h₁ : Function.Bijective (componentComparison K₁ X))
    (h₂ : Function.Bijective (componentComparison K₂ X))
    (hP : Function.Bijective (mappingComponentsComparison h X)) :
    Function.Bijective (componentComparison K₃ X) := by
  constructor
  · intro s r he
    apply hP.1
    apply Subtype.ext
    apply Prod.ext
    · apply h₁.1
      exact (componentComparison_restrict a X s).trans
        ((congrArg (fun f ↦ a ≫ f) he).trans (componentComparison_restrict a X r).symm)
    · apply h₂.1
      exact (componentComparison_restrict b X s).trans
        ((congrArg (fun f ↦ b ≫ f) he).trans (componentComparison_restrict b X r).symm)
  · intro r
    obtain ⟨s₁, hs₁⟩ := h₁.2 (a ≫ r)
    obtain ⟨s₂, hs₂⟩ := h₂.2 (b ≫ r)
    have hc : SSet.mapπ₀ (horizontalPre i X) s₁ = SSet.mapπ₀ (horizontalPre j X) s₂ := by
      apply h₀
      rw [componentComparison_restrict, componentComparison_restrict, hs₁, hs₂,
        ← Category.assoc, ← Category.assoc, h.w]
    obtain ⟨z, hz⟩ := hP.2 ⟨⟨s₁, s₂⟩, hc⟩
    have hz₁ := congrArg (fun w ↦ w.val.1) hz
    have hz₂ := congrArg (fun w ↦ w.val.2) hz
    simp only [mappingComponentsComparison] at hz₁ hz₂
    refine ⟨z, h.hom_ext ?_ ?_⟩
    · exact (componentComparison_restrict a X z).symm.trans
        ((congrArg (componentComparison K₁ X) hz₁).trans hs₁)
    · exact (componentComparison_restrict b X z).symm.trans
        ((congrArg (componentComparison K₂ X) hz₂).trans hs₂)

theorem componentComparison_bijective_of_parameter_iso {K L : SSet.{u}} (e : K ≅ L)
    (X : BiSSet.{u}) (hK : Function.Bijective (componentComparison K X)) :
    Function.Bijective (componentComparison L X) := by
  let E := (SSet.π₀Functor.mapIso (parameterIso e X)).toEquiv
  constructor
  · intro s r he
    apply E.injective
    apply hK.1
    exact (componentComparison_restrict e.hom X s).trans
      ((congrArg (fun f ↦ e.hom ≫ f) he).trans
        (componentComparison_restrict e.hom X r).symm)
  · intro r
    obtain ⟨s, hs⟩ := hK.2 (e.hom ≫ r)
    obtain ⟨z, hz⟩ := E.surjective s
    refine ⟨z, (cancel_epi e.hom).1 ?_⟩
    exact (componentComparison_restrict e.hom X z).symm.trans
      ((congrArg (componentComparison K X) hz).trans hs)

theorem singletonFace_componentComparison_bijective (n : ℕ) (i : Fin (n + 2))
    (X : BiSSet.{u}) : Function.Bijective (componentComparison (faceUnion.{u} {i}) X) :=
  componentComparison_bijective_of_parameter_iso (singletonFaceIso n i) X
    (simplex_componentComparison_bijective X n)

end
end DaggerNativeComponentMatchingGluing
