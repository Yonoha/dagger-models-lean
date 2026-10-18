import OriginalJoinedOneHornGluing

/-!
# Actual one-dimensional relative lifts for joined boundary restriction

Construct the joined horn from the input commuting square, fill the actual
inner horn, and retain both the prescribed boundary and the specified source
vertex. The result is the literal relative (1,0)-horn lifting property, for
arbitrary prefix dimension and universe. Higher relative horns remain open.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers
open DaggerOriginalOrdinalJoinLeft
open DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedHornPrefix
open DaggerOriginalJoinedCofaces
open DaggerOriginalJoinedPrefixBoundaryFunctor
open DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalJoinedOneHornGluing

universe u

namespace DaggerOriginalJoinedOneHornLifting

noncomputable section

/-- The actual joined simplex extends the given boundary and specified joined coface. -/
theorem one_horn_joined_extension {X : SSet.{u}} (hX : innerHornFillers X) (k : ℕ)
    (φ : (Λ[1, 0] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X)
    (β : (Δ[1] : SSet.{u}) ⟶ boundaryJoinedPresheaf k X)
    (w : φ ≫ joinedBoundaryRestriction k X = Λ[1, 0].ι ≫ β) :
    ∃ μ : (Δ[k + 2] : SSet.{u}) ⟶ X,
      (prefixBoundary k 1).ι ≫ μ = SSet.yonedaEquiv β ∧
      SSet.stdSimplex.δ (suffixIndex k 1 1) ≫ μ =
        (SSet.yonedaEquiv (X := X) (n := ⦋k + 1⦌)).symm
          ((SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋0⦌))
            (SSet.horn.ι (n := 0) 0 1 (by decide) ≫ φ)) := by
  obtain ⟨Γ, hΓleft, hΓright⟩ := glue_one_horn k φ β w
  have hf := joined_leftHorn_filling X hX k 1 0 (by decide)
  rw [suffix_one_horn_eq_face] at hf
  obtain ⟨μ, hμ⟩ := hf Γ
  refine ⟨μ, ?_, ?_⟩
  · simpa only [hμ, SSet.Subcomplex.homOfLE_ι_assoc] using hΓleft
  · simpa only [hμ, SSet.Subcomplex.homOfLE_ι_assoc,
      SSet.stdSimplex.faceSingletonComplIso_hom_ι_assoc] using hΓright

/-- The original boundary restriction has the literal relative (1,0)-horn lifting property. -/
theorem joinedBoundaryRestriction_one_horn_lift {X : SSet.{u}}
    (hX : innerHornFillers X) (k : ℕ)
    (φ : (Λ[1, 0] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X)
    (β : (Δ[1] : SSet.{u}) ⟶ boundaryJoinedPresheaf k X)
    (w : φ ≫ joinedBoundaryRestriction k X = Λ[1, 0].ι ≫ β) :
    ∃ σ : (Δ[1] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X,
      φ = Λ[1, 0].ι ≫ σ ∧ σ ≫ joinedBoundaryRestriction k X = β := by
  obtain ⟨μ, hboundary, hface⟩ := one_horn_joined_extension hX k φ β w
  let s : (joinedPresheaf ⦋k⦌ X).obj (op ⦋1⦌) :=
    (SSet.yonedaEquiv (X := X) (n := ⦋k + 2⦌)) μ
  let σ : (Δ[1] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X := SSet.yonedaEquiv.symm s
  have hsource : SSet.stdSimplex.δ 1 ≫ σ = SSet.horn.ι 0 1 (by decide) ≫ φ := by
    apply SSet.yonedaEquiv.injective
    have hv := congrArg (SSet.yonedaEquiv (X := X) (n := ⦋k + 1⦌)) hface
    rw [Equiv.apply_symm_apply] at hv
    have ho := yonedaEquiv_precomp_operator σ (SimplexCategory.δ (1 : Fin 2))
    change SSet.yonedaEquiv (SSet.stdSimplex.δ 1 ≫ σ) = _ at ho
    rw [ho, Equiv.apply_symm_apply]
    change X.map ((ordinalJoinLeft ⦋k⦌).map (SimplexCategory.δ 1)).op s = _
    rw [joinMap_coface]
    have hm := yonedaEquiv_precomp_operator μ
      (SimplexCategory.δ (suffixIndex k 1 1))
    exact hm.symm.trans hv
  refine ⟨σ, ?_, ?_⟩
  · apply SSet.horn.hom_ext
    intro j hj
    fin_cases j
    · exact False.elim (hj rfl)
    · have heq : SSet.horn.ι 0 1 (by decide) ≫ φ =
          SSet.horn.ι 0 1 (by decide) ≫ (Λ[1, 0].ι ≫ σ) := by
        rw [← Category.assoc, SSet.horn.ι_ι]
        exact hsource.symm
      have hv := congrArg SSet.yonedaEquiv heq
      simpa only [SSet.yonedaEquiv_comp, SSet.horn.yonedaEquiv_ι] using hv
  · apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change (prefixBoundary k 1).ι ≫
      (SSet.yonedaEquiv (X := X) (n := ⦋k + 2⦌)).symm
        ((SSet.yonedaEquiv (X := X) (n := ⦋k + 2⦌)) μ) = _
    rw [Equiv.symm_apply_apply]
    exact hboundary

end

end DaggerOriginalJoinedOneHornLifting
