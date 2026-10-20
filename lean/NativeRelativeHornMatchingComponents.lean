import NativeComponentPartialMatchingPi
import NativeComponentMatchingNaturality
import NativePullbackComponentsRightFibration
import NativePositiveHornMatchingPi

/-! Relative horn matching is component-surjective from the actual pi0 fibration. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite SSet.KanComplex
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeHorizontalPiSections
open DaggerNativeReedyFibrantHorizontalMapping DaggerNativeComponentPartialMatchingComparison
open DaggerNativeComponentPartialMatchingPi DaggerNativeComponentMatchingNaturality
open DaggerNativePullbackComponentsPiOneSurjective DaggerNativePullbackComponentsRightFibration
open DaggerNativePositiveHornMatchingPi
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeRelativeHornMatchingComponents
noncomputable section

theorem relativeTarget_componentComparison_bijective {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (hX : ReedyFibrant X) (hY : ReedyFibrant Y)
    (hπY : ∀ q : ℕ, Fibration (C := SSet.{u}) (rowProjection Y (q + 1)))
    (m : ℕ) (k : Fin (m + 2)) : Function.Bijective
      (componentsComparison (horizontalMap (SSet.horn.{u} (m + 1) k) f)
        (horizontalPre (SSet.horn.{u} (m + 1) k).ι Y)) := by
  have : Fibration (horizontalPre (SSet.horn.{u} (m + 1) k).ι Y) :=
    DaggerNativeReedyFibrantHorizontalMapping.restriction_fibration Y hY _
  have : IsFibrant (horizontalMapping (SSet.horn.{u} (m + 1) k) Y) :=
    mapping_isFibrant Y hY _
  have : IsFibrant (horizontalMapping (SSet.horn.{u} (m + 1) k) X) :=
    mapping_isFibrant X hX _
  exact componentsComparison_bijective_of_right_fibration _ _
    (horn_restriction_mapπ_surjective_rebased Y hY hπY m k 0)

theorem relative_horn_matching_components_surjective {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (hX : ReedyFibrant X) (hY : ReedyFibrant Y)
    (hπX : ∀ q : ℕ, Fibration (C := SSet.{u}) (rowProjection X (q + 1)))
    (hπY : ∀ q : ℕ, Fibration (C := SSet.{u}) (rowProjection Y (q + 1)))
    [Fibration (C := SSet.{u}) (componentMap f)] (m : ℕ) (k : Fin (m + 2)) :
    Function.Surjective (SSet.mapπ₀ (relativeRestriction (SSet.horn.{u} (m + 1) k).ι f)) := by
  let H := (SSet.horn.{u} (m + 1) k : SSet.{u})
  let i := (SSet.horn.{u} (m + 1) k).ι
  let p := horizontalMap H f
  let q := horizontalPre i Y
  let r := relativeRestriction i f
  intro z
  let a := SSet.mapπ₀ (pullback.fst p q) z
  let b := SSet.mapπ₀ (pullback.snd p q) z
  have hc : SSet.mapπ₀ p a = SSet.mapπ₀ q b := by
    dsimp only [a, b]
    rw [← SSet.mapπ₀_comp_apply, pullback.condition, SSet.mapπ₀_comp_apply]
  have hs : componentComparison H X a ≫ componentMap f =
      i ≫ componentComparison (Δ[m + 1] : SSet.{u}) Y b := by
    calc
      _ = componentComparison H Y (SSet.mapπ₀ p a) :=
        (componentComparison_natural H f a).symm
      _ = componentComparison H Y (SSet.mapπ₀ q b) := congrArg _ hc
      _ = _ := componentComparison_restrict i Y b
  let sq : CommSq (componentComparison H X a) i (componentMap f)
      (componentComparison (Δ[m + 1] : SSet.{u}) Y b) := ⟨hs⟩
  have hl : HasLiftingProperty i (componentMap f) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance i
      (SSet.modelCategoryQuillen.horn_ι_mem_J m k)
  have : sq.HasLift := hl.sq_hasLift sq
  obtain ⟨w, hw⟩ := (simplex_componentComparison_bijective X (m + 1)).2 sq.lift
  refine ⟨w, (relativeTarget_componentComparison_bijective f hX hY hπY m k).1 ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change SSet.mapπ₀ (pullback.fst p q) (SSet.mapπ₀ r w) = a
    have he : SSet.mapπ₀ (pullback.fst p q) (SSet.mapπ₀ r w) =
        SSet.mapπ₀ (horizontalPre i X) w :=
      (SSet.mapπ₀_comp_apply r (pullback.fst p q) w).symm.trans
        (congrArg (fun g ↦ SSet.mapπ₀ g w) (relativeRestriction_fst i f))
    apply (horn_componentComparison_bijective X hX hπX m k).1
    rw [he]
    exact (componentComparison_restrict i X w).trans
      ((congrArg (fun g ↦ i ≫ g) hw).trans sq.fac_left)
  · change SSet.mapπ₀ (pullback.snd p q) (SSet.mapπ₀ r w) = b
    have he : SSet.mapπ₀ (pullback.snd p q) (SSet.mapπ₀ r w) =
        SSet.mapπ₀ (horizontalMap (Δ[m + 1] : SSet.{u}) f) w :=
      (SSet.mapπ₀_comp_apply r (pullback.snd p q) w).symm.trans
        (congrArg (fun g ↦ SSet.mapπ₀ g w) (relativeRestriction_snd i f))
    apply (simplex_componentComparison_bijective Y (m + 1)).1
    rw [he]
    exact (componentComparison_natural (Δ[m + 1] : SSet.{u}) f w).trans
      ((congrArg (fun g ↦ g ≫ componentMap f) hw).trans sq.fac_right)

end
end DaggerNativeRelativeHornMatchingComponents
