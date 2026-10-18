import NativeHorizontalMappingPushout
import NativePullbackPositivePiRebase

/-! Canonical positive homotopy classes of horizontal pushout mapping, at actual vertices. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open SSet SSet.KanComplex DaggerNativeBisimplicialHorizontalMapping
open DaggerNativeHorizontalMappingPushout DaggerNativePullbackPositivePiRebase
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeHorizontalPushoutPositivePi
noncomputable section

theorem restrictionEquation {K₀ K₁ K₂ K₃ : SSet.{u}}
    {i : K₀ ⟶ K₁} {j : K₀ ⟶ K₂} {a : K₁ ⟶ K₃} {b : K₂ ⟶ K₃}
    (h : IsPushout i j a b) (X : BiSSet.{u}) (s : (horizontalMapping K₃ X) _⦋0⦌) :
    (horizontalPre i X).app _ ((horizontalPre a X).app _ s) =
      (horizontalPre j X).app _ ((horizontalPre b X).app _ s) :=
  congrFun (NatTrans.congr_app (mapping_square h X) _) s

def comparison {K₀ K₁ K₂ K₃ : SSet.{u}}
    {i : K₀ ⟶ K₁} {j : K₀ ⟶ K₂} {a : K₁ ⟶ K₃} {b : K₂ ⟶ K₃}
    (h : IsPushout i j a b) (X : BiSSet.{u}) (s : (horizontalMapping K₃ X) _⦋0⦌) (n : ℕ) :
    π (n + 1) (horizontalMapping K₃ X) s →
    {z : π (n + 1) (horizontalMapping K₁ X) ((horizontalPre a X).app _ s) ×
      π (n + 1) (horizontalMapping K₂ X) ((horizontalPre b X).app _ s) //
      mapπ (horizontalPre i X) (n + 1) _ _ (restrictionEquation h X s) z.1 =
        mapπ (horizontalPre j X) (n + 1) _ _ rfl z.2} :=
  fun z ↦ ⟨(mapπ (horizontalPre a X) (n + 1) s _ rfl z,
      mapπ (horizontalPre b X) (n + 1) s _ rfl z), by
    simp only [mapπ_mapπ, mapping_square h X]⟩

theorem comparison_factor {K₀ K₁ K₂ K₃ : SSet.{u}}
    {i : K₀ ⟶ K₁} {j : K₀ ⟶ K₂} {a : K₁ ⟶ K₃} {b : K₂ ⟶ K₃}
    (h : IsPushout i j a b) (X : BiSSet.{u}) (s : (horizontalMapping K₃ X) _⦋0⦌)
    (n : ℕ) : comparison h X s n =
    let w := (mappingComparison h X).app _ s
    let he := congrFun (NatTrans.congr_app (mappingComparison_fst h X) _) s
    let hc := congrFun (NatTrans.congr_app (mappingComparison_snd h X) _) s
    (rebasedComparison (horizontalPre i X) (horizontalPre j X) w
      ((horizontalPre a X).app _ s) ((horizontalPre b X).app _ s) he hc n) ∘
        mapπ (mappingComparison h X) (n + 1) s w rfl := by
  funext z
  apply Subtype.ext
  apply Prod.ext
  · simp only [comparison, Function.comp_apply, rebasedComparison, mapπ_mapπ,
      mappingComparison_fst]
  · simp only [comparison, Function.comp_apply, rebasedComparison, mapπ_mapπ,
      mappingComparison_snd]

theorem comparison_surjective {K₀ K₁ K₂ K₃ : SSet.{u}}
    {i : K₀ ⟶ K₁} {j : K₀ ⟶ K₂} {a : K₁ ⟶ K₃} {b : K₂ ⟶ K₃}
    (h : IsPushout i j a b) (X : BiSSet.{u})
    [Fibration (horizontalPre i X)] [IsFibrant (horizontalMapping K₀ X)]
    [IsFibrant (horizontalMapping K₂ X)] (s : (horizontalMapping K₃ X) _⦋0⦌) (n : ℕ) :
    Function.Surjective (comparison h X s n) := by
  rw [comparison_factor]
  apply Function.Surjective.comp (rebasedComparison_surjective _ _ _ _ _ _ _ n)
  exact (mapπEquivOfIso (mappingPushoutIso h X) (n + 1) s _ rfl).surjective

theorem comparison_bijective {K₀ K₁ K₂ K₃ : SSet.{u}}
    {i : K₀ ⟶ K₁} {j : K₀ ⟶ K₂} {a : K₁ ⟶ K₃} {b : K₂ ⟶ K₃}
    (h : IsPushout i j a b) (X : BiSSet.{u})
    [Fibration (horizontalPre i X)] [IsFibrant (horizontalMapping K₀ X)]
    [IsFibrant (horizontalMapping K₂ X)] (s : (horizontalMapping K₃ X) _⦋0⦌) (n : ℕ)
    (hp : Function.Surjective
      (mapπ (horizontalPre i X) (n + 2) _ _ (restrictionEquation h X s))) :
    Function.Bijective (comparison h X s n) := by
  rw [comparison_factor]
  apply Function.Bijective.comp (rebasedComparison_bijective _ _ _ _ _ _ _ n hp)
  exact (mapπEquivOfIso (mappingPushoutIso h X) (n + 1) s _ rfl).bijective

end
end DaggerNativeHorizontalPushoutPositivePi
