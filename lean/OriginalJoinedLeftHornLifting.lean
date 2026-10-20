import OriginalJoinedBoundarySuffixGluing

/-!
# All original relative left-horn lifts for joined boundary restriction

Construct the full joined horn map from the given relative horn and boundary
commuting square. Every nonfinal right-block index becomes an original inner
index. Fill that actual inner horn and prove both original lifting equations,
in all dimensions and arbitrary universe, with no filler supplied as input.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers
open DaggerOriginalOrdinalJoinLeft
open DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedHornPrefix
open DaggerOriginalJoinedCofaces
open DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalJoinedSuffixFaceMaps
open DaggerOriginalJoinedSuffixHornGluing
open DaggerOriginalJoinedBoundarySuffixGluing

universe u

namespace DaggerOriginalJoinedLeftHornLifting

noncomputable section

/-- Fill the original joined horn, retaining the prescribed boundary and every given coface. -/
theorem joined_horn_extension {X : SSet.{u}} (hX : innerHornFillers X)
    (k n : ℕ) (i : Fin (n + 2)) (hi : i < Fin.last (n + 1))
    (φ : (Λ[n + 1, i] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X)
    (β : (Δ[n + 1] : SSet.{u}) ⟶ boundaryJoinedPresheaf k X)
    (w : φ ≫ joinedBoundaryRestriction k X = Λ[n + 1, i].ι ≫ β) :
    ∃ μ : (Δ[k + (n + 1) + 1] : SSet.{u}) ⟶ X,
      (prefixBoundary k (n + 1)).ι ≫ μ = SSet.yonedaEquiv β ∧
      ∀ (j : Fin (n + 2)) (hj : j ≠ i),
        SSet.stdSimplex.δ (suffixIndex k (n + 1) j) ≫ μ = joinedHornCoface k n i j hj φ := by
  obtain ⟨Γ, hΓleft, hΓright⟩ := glue_all_horn k n i φ β w
  obtain ⟨μ, hμ⟩ := joined_leftHorn_filling X hX k (n + 1) i hi Γ
  have hboundary : (prefixBoundary k (n + 1)).ι ≫ μ = SSet.yonedaEquiv β := by
    simpa only [hμ, SSet.Subcomplex.homOfLE_ι_assoc] using hΓleft
  have hsuffix : (suffixHorn k (n + 1) i).ι ≫ μ = suffixHornMap k n i φ := by
    simpa only [hμ, SSet.Subcomplex.homOfLE_ι_assoc] using hΓright
  refine ⟨μ, hboundary, ?_⟩
  intro j hj
  have hf := suffixHornMap_face k n i φ ⟨j, hj⟩
  rw [← hsuffix] at hf
  have hc := congrArg (fun f ↦
    (SSet.stdSimplex.faceSingletonComplIso (suffixIndex k (n + 1) j)).hom ≫ f) hf
  dsimp only at hc
  simpa only [suffixFaceMap, SSet.Subcomplex.homOfLE_ι_assoc,
    SSet.stdSimplex.faceSingletonComplIso_hom_ι_assoc, Iso.hom_inv_id_assoc] using hc

/-- The actual joined boundary restriction lifts every original nonfinal horn. -/
theorem joinedBoundaryRestriction_left_horn_lift {X : SSet.{u}} (hX : innerHornFillers X)
    (k n : ℕ) (i : Fin (n + 2)) (hi : i < Fin.last (n + 1))
    (φ : (Λ[n + 1, i] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X)
    (β : (Δ[n + 1] : SSet.{u}) ⟶ boundaryJoinedPresheaf k X)
    (w : φ ≫ joinedBoundaryRestriction k X = Λ[n + 1, i].ι ≫ β) :
    ∃ σ : (Δ[n + 1] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X,
      φ = Λ[n + 1, i].ι ≫ σ ∧ σ ≫ joinedBoundaryRestriction k X = β := by
  obtain ⟨μ, hboundary, hfaces⟩ := joined_horn_extension hX k n i hi φ β w
  let s : (joinedPresheaf ⦋k⦌ X).obj (op ⦋n + 1⦌) :=
    (SSet.yonedaEquiv (X := X) (n := ⦋k + (n + 1) + 1⦌)) μ
  let σ : (Δ[n + 1] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X := SSet.yonedaEquiv.symm s
  have hsource (j : Fin (n + 2)) (hj : j ≠ i) :
      SSet.stdSimplex.δ j ≫ σ = SSet.horn.ι i j hj ≫ φ := by
    apply (SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋n⦌)).injective
    have hv := congrArg (SSet.yonedaEquiv (X := X) (n := ⦋k + n + 1⦌)) (hfaces j hj)
    change SSet.yonedaEquiv (SSet.stdSimplex.δ (suffixIndex k (n + 1) j) ≫ μ) =
      (SSet.yonedaEquiv (X := X) (n := ⦋k + n + 1⦌))
        ((SSet.yonedaEquiv (X := X) (n := ⦋k + n + 1⦌)).symm
          ((SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋n⦌))
            (SSet.horn.ι i j hj ≫ φ))) at hv
    rw [Equiv.apply_symm_apply] at hv
    have ho := yonedaEquiv_precomp_operator σ (SimplexCategory.δ j)
    change SSet.yonedaEquiv (SSet.stdSimplex.δ j ≫ σ) = _ at ho
    rw [ho, Equiv.apply_symm_apply]
    change X.map ((ordinalJoinLeft ⦋k⦌).map (SimplexCategory.δ j)).op s = _
    rw [joinMap_coface]
    have hm := yonedaEquiv_precomp_operator μ (SimplexCategory.δ (suffixIndex k (n + 1) j))
    exact hm.symm.trans hv
  refine ⟨σ, ?_, ?_⟩
  · apply SSet.horn.hom_ext
    intro j hj
    have heq : SSet.horn.ι i j hj ≫ φ = SSet.horn.ι i j hj ≫ (Λ[n + 1, i].ι ≫ σ) := by
      rw [← Category.assoc, SSet.horn.ι_ι]
      exact (hsource j hj).symm
    have hv := congrArg SSet.yonedaEquiv heq
    simpa only [SSet.yonedaEquiv_comp, SSet.horn.yonedaEquiv_ι] using hv
  · apply (SSet.yonedaEquiv (X := boundaryJoinedPresheaf k X) (n := ⦋n + 1⦌)).injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change (prefixBoundary k (n + 1)).ι ≫
      (SSet.yonedaEquiv (X := X) (n := ⦋k + (n + 1) + 1⦌)).symm
        ((SSet.yonedaEquiv (X := X) (n := ⦋k + (n + 1) + 1⦌)) μ) = _
    rw [Equiv.symm_apply_apply]
    exact hboundary

end

end DaggerOriginalJoinedLeftHornLifting
