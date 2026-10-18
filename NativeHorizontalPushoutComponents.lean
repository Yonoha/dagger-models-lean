import NativeHorizontalMappingPushout
import NativePullbackComponentsPiOneSurjective

/-! The exact component formula for horizontal pushout mapping under pi-one surjectivity. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open SSet SSet.KanComplex DaggerNativeBisimplicialHorizontalMapping
open DaggerNativeHorizontalMappingPushout DaggerNativePullbackComponentsPiOneSurjective
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeHorizontalPushoutComponents
noncomputable section

def mappingComponentsComparison {K₀ K₁ K₂ K₃ : SSet.{u}}
    {i : K₀ ⟶ K₁} {j : K₀ ⟶ K₂} {a : K₁ ⟶ K₃} {b : K₂ ⟶ K₃}
    (h : IsPushout i j a b) (X : BiSSet.{u}) : (horizontalMapping K₃ X).π₀ →
    {z : (horizontalMapping K₁ X).π₀ × (horizontalMapping K₂ X).π₀ //
      mapπ₀ (horizontalPre i X) z.1 = mapπ₀ (horizontalPre j X) z.2} :=
  fun s ↦ ⟨(mapπ₀ (horizontalPre a X) s, mapπ₀ (horizontalPre b X) s), by
    rw [← mapπ₀_comp_apply, mapping_square h X, mapπ₀_comp_apply]⟩

theorem mappingComponentsComparison_factor {K₀ K₁ K₂ K₃ : SSet.{u}}
    {i : K₀ ⟶ K₁} {j : K₀ ⟶ K₂} {a : K₁ ⟶ K₃} {b : K₂ ⟶ K₃}
    (h : IsPushout i j a b) (X : BiSSet.{u}) : mappingComponentsComparison h X =
    (componentsComparison (horizontalPre i X) (horizontalPre j X)) ∘
      mapπ₀ (mappingComparison h X) := by
  funext s
  apply Subtype.ext
  apply Prod.ext
  · change mapπ₀ (horizontalPre a X) s =
      mapπ₀ (pullback.fst _ _) (mapπ₀ (mappingComparison h X) s)
    rw [← mapπ₀_comp_apply, mappingComparison_fst]
  · change mapπ₀ (horizontalPre b X) s =
      mapπ₀ (pullback.snd _ _) (mapπ₀ (mappingComparison h X) s)
    rw [← mapπ₀_comp_apply, mappingComparison_snd]

theorem mappingComponentsComparison_bijective {K₀ K₁ K₂ K₃ : SSet.{u}}
    {i : K₀ ⟶ K₁} {j : K₀ ⟶ K₂} {a : K₁ ⟶ K₃} {b : K₂ ⟶ K₃}
    (h : IsPushout i j a b) (X : BiSSet.{u})
    [Fibration (horizontalPre i X)] [IsFibrant (horizontalMapping K₀ X)]
    [IsFibrant (horizontalMapping K₂ X)]
    (hp : ∀ (e : (horizontalMapping K₁ X) _⦋0⦌)
      (d : (horizontalMapping K₀ X) _⦋0⦌) (he : (horizontalPre i X).app _ e = d),
      Function.Surjective (mapπ (horizontalPre i X) 1 e d he)) :
    Function.Bijective (mappingComponentsComparison h X) := by
  rw [mappingComponentsComparison_factor]
  apply Function.Bijective.comp (componentsComparison_bijective _ _ hp)
  exact (SSet.π₀Functor.mapIso (mappingPushoutIso h X)).toEquiv.bijective

end
end DaggerNativeHorizontalPushoutComponents
