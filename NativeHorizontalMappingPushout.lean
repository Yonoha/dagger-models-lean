import NativeBisimplicialHorizontalMapping

/-! A genuine horizontal pushout induces the actual pullback of native mapping simplicial sets. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping
universe u
namespace DaggerNativeHorizontalMappingPushout
noncomputable section

theorem mapping_square {K₀ K₁ K₂ K₃ : SSet.{u}} {i : K₀ ⟶ K₁} {j : K₀ ⟶ K₂}
    {a : K₁ ⟶ K₃} {b : K₂ ⟶ K₃} (h : IsPushout i j a b) (X : BiSSet.{u}) :
    horizontalPre a X ≫ horizontalPre i X = horizontalPre b X ≫ horizontalPre j X := by
  rw [← horizontalPre_comp, ← horizontalPre_comp, h.w]

def mappingComparison {K₀ K₁ K₂ K₃ : SSet.{u}} {i : K₀ ⟶ K₁} {j : K₀ ⟶ K₂}
    {a : K₁ ⟶ K₃} {b : K₂ ⟶ K₃} (h : IsPushout i j a b) (X : BiSSet.{u}) :
    horizontalMapping K₃ X ⟶ pullback (horizontalPre i X) (horizontalPre j X) :=
  pullback.lift (horizontalPre a X) (horizontalPre b X) (mapping_square h X)

theorem mappingComparison_fst {K₀ K₁ K₂ K₃ : SSet.{u}} {i : K₀ ⟶ K₁} {j : K₀ ⟶ K₂}
    {a : K₁ ⟶ K₃} {b : K₂ ⟶ K₃} (h : IsPushout i j a b) (X : BiSSet.{u}) :
    mappingComparison h X ≫ pullback.fst (horizontalPre i X) (horizontalPre j X) =
      horizontalPre a X := by
  simp only [mappingComparison, pullback.lift_fst]

theorem mappingComparison_snd {K₀ K₁ K₂ K₃ : SSet.{u}} {i : K₀ ⟶ K₁} {j : K₀ ⟶ K₂}
    {a : K₁ ⟶ K₃} {b : K₂ ⟶ K₃} (h : IsPushout i j a b) (X : BiSSet.{u}) :
    mappingComparison h X ≫ pullback.snd (horizontalPre i X) (horizontalPre j X) =
      horizontalPre b X := by
  simp only [mappingComparison, pullback.lift_snd]

theorem mappingComparison_app_bijective {K₀ K₁ K₂ K₃ : SSet.{u}}
    {i : K₀ ⟶ K₁} {j : K₀ ⟶ K₂} {a : K₁ ⟶ K₃} {b : K₂ ⟶ K₃}
    (h : IsPushout i j a b) (X : BiSSet.{u}) (v : SimplexCategoryᵒᵖ) :
    Function.Bijective ((mappingComparison h X).app v) := by
  let p := horizontalPre i X
  let q := horizontalPre j X
  constructor
  · intro f g he
    have ha := congrArg (fun w ↦ (pullback.fst p q).app v w) he
    have hb := congrArg (fun w ↦ (pullback.snd p q).app v w) he
    change (mappingComparison h X ≫ pullback.fst p q).app v f =
      (mappingComparison h X ≫ pullback.fst p q).app v g at ha
    change (mappingComparison h X ≫ pullback.snd p q).app v f =
      (mappingComparison h X ≫ pullback.snd p q).app v g at hb
    rw [mappingComparison_fst] at ha
    rw [mappingComparison_snd] at hb
    exact h.hom_ext ha hb
  · intro w
    let f := (pullback.fst p q).app v w
    let g := (pullback.snd p q).app v w
    have hc : i ≫ f = j ≫ g := by
      exact congrFun (NatTrans.congr_app (pullback.condition (f := p) (g := q)) v) w
    obtain ⟨t, ht₁, ht₂⟩ := h.exists_desc f g hc
    refine ⟨t, FunctorToTypes.pullback_ext.mpr ⟨?_, ?_⟩⟩
    · change (mappingComparison h X ≫ pullback.fst p q).app v t = f
      rw [mappingComparison_fst]
      exact ht₁
    · change (mappingComparison h X ≫ pullback.snd p q).app v t = g
      rw [mappingComparison_snd]
      exact ht₂

instance mappingComparison_isIso {K₀ K₁ K₂ K₃ : SSet.{u}} {i : K₀ ⟶ K₁} {j : K₀ ⟶ K₂}
    {a : K₁ ⟶ K₃} {b : K₂ ⟶ K₃} (h : IsPushout i j a b) (X : BiSSet.{u}) :
    IsIso (mappingComparison h X) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro v
  exact (isIso_iff_bijective _).mpr (mappingComparison_app_bijective h X v)

def mappingPushoutIso {K₀ K₁ K₂ K₃ : SSet.{u}} {i : K₀ ⟶ K₁} {j : K₀ ⟶ K₂}
    {a : K₁ ⟶ K₃} {b : K₂ ⟶ K₃} (h : IsPushout i j a b) (X : BiSSet.{u}) :
    horizontalMapping K₃ X ≅ pullback (horizontalPre i X) (horizontalPre j X) :=
  asIso (mappingComparison h X)

end
end DaggerNativeHorizontalMappingPushout
