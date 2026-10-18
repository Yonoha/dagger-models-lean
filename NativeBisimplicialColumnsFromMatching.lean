import NativeBisimplicialReedyRestrictions
import NativeFibrationSurjectiveComponents

/-! The component-surjective horn matching criterion gives actual native column fibrations. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialRelativeLifting
open DaggerNativeBisimplicialReedyRestrictions DaggerNativeFibrationSurjectiveComponents
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeBisimplicialColumnsFromMatching
noncomputable section

theorem columns_fibration_of_horn_matching_components {F G : BiSSet.{u}} (f : F ⟶ G)
    (hf : ReedyFibration f)
    (hπ : ∀ (n : ℕ) (k : Fin (n + 2)), Function.Surjective
      (SSet.mapπ₀ (relativeRestriction (SSet.horn (n + 1) k).ι f)))
    (v : SimplexCategoryᵒᵖ) : Fibration (C := SSet.{u}) ((flipMap f).app v) := by
  obtain ⟨v⟩ := v
  induction v using SimplexCategory.rec with | _ q =>
    apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
    intro K L i hi
    simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
    obtain ⟨n, ⟨k⟩⟩ := hi
    have hr : Fibration (relativeRestriction (SSet.horn (n + 1) k).ι f) :=
      horn_matching_fibration f hf _ _
    constructor
    intro a b sq
    let aa : (Δ[q] : SSet.{u}) ⟶ horizontalMapping (SSet.horn (n + 1) k : SSet.{u}) F :=
      SSet.yonedaEquiv.symm a
    let bb : (Δ[q] : SSet.{u}) ⟶ horizontalMapping (Δ[n + 1] : SSet.{u}) G :=
      SSet.yonedaEquiv.symm b
    let r := relativeRestriction (SSet.horn (n + 1) k).ι f
    let s := horizontalMap (SSet.horn (n + 1) k : SSet.{u}) f
    let t := horizontalPre (SSet.horn (n + 1) k).ι G
    have h : aa ≫ s = bb ≫ t := by
      apply SSet.yonedaEquiv.injective
      simpa only [SSet.yonedaEquiv_comp, aa, bb, Equiv.apply_symm_apply] using sq.w
    let w := SSet.yonedaEquiv (pullback.lift aa bb h)
    have hw₁ : (pullback.fst s t).app (op ⦋q⦌) w = a := by
      rw [← SSet.yonedaEquiv_comp, pullback.lift_fst]
      exact Equiv.apply_symm_apply _ a
    have hw₂ : (pullback.snd s t).app (op ⦋q⦌) w = b := by
      rw [← SSet.yonedaEquiv_comp, pullback.lift_snd]
      exact Equiv.apply_symm_apply _ b
    obtain ⟨l, hl⟩ := degree_surjective_of_components r (hπ n k) q w
    refine ⟨l, ?_, ?_⟩
    · have hh := congrArg (fun z ↦ (pullback.fst s t).app (op ⦋q⦌) z) hl
      change (r ≫ pullback.fst s t).app (op ⦋q⦌) l = _ at hh
      rw [relativeRestriction_fst] at hh
      exact hh.trans hw₁
    · have hh := congrArg (fun z ↦ (pullback.snd s t).app (op ⦋q⦌) z) hl
      change (r ≫ pullback.snd s t).app (op ⦋q⦌) l = _ at hh
      rw [relativeRestriction_snd] at hh
      exact hh.trans hw₂

end
end DaggerNativeBisimplicialColumnsFromMatching
