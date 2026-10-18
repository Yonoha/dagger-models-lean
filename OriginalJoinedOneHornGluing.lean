import OriginalJoinedCofaceGluing

/-!
# Actual relative one-horn data give the original joined inner horn

A one-dimensional left horn supplies one original joined coface. Its commuting
square with boundary restriction is precisely the overlap equation for the
native subcomplex pushout. Thus the joined horn map is constructed from the
input data, without assuming it as an additional premise.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft
open DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedHornPrefix
open DaggerOriginalJoinedCofaces
open DaggerOriginalJoinedPrefixBoundaryFunctor
open DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalJoinedCofaceGluing

universe u

namespace DaggerOriginalJoinedOneHornGluing

noncomputable section

/-- The actual suffix one-horn is its single original coface. -/
theorem suffix_one_horn_eq_face (k : ℕ) :
    suffixHorn.{u} k 1 0 = SSet.stdSimplex.face {suffixIndex k 1 1}ᶜ := by
  apply le_antisymm
  · rw [suffixHorn, iSup_le_iff]
    rintro ⟨j, hj⟩
    change j ≠ 0 at hj
    fin_cases j
    · exact False.elim (hj rfl)
    · exact le_rfl
  · exact le_iSup (fun j : ({0}ᶜ : Set (Fin 2)) ↦
      SSet.stdSimplex.face {suffixIndex k 1 j.val}ᶜ) ⟨1, by decide⟩

/-- The original relative one-horn commuting square is the exact coface overlap equation. -/
theorem one_horn_overlap {X : SSet.{u}} (k : ℕ)
    (φ : (Λ[1, 0] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X)
    (β : (Δ[1] : SSet.{u}) ⟶ boundaryJoinedPresheaf k X)
    (w : φ ≫ joinedBoundaryRestriction k X = Λ[1, 0].ι ≫ β) :
    prefixBoundaryMap k (SimplexCategory.δ (1 : Fin 2)) ≫ SSet.yonedaEquiv β =
      (prefixBoundary k 0).ι ≫ (SSet.yonedaEquiv (X := X) (n := ⦋k + 1⦌)).symm
        ((SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋0⦌))
          (SSet.horn.ι (n := 0) 0 1 (by decide) ≫ φ)) := by
  have hw : (SSet.horn.ι 0 1 (by decide) ≫ φ) ≫ joinedBoundaryRestriction k X =
      SSet.stdSimplex.δ 1 ≫ β := by
    rw [Category.assoc, w, ← Category.assoc, SSet.horn.ι_ι]
  have hv := congrArg SSet.yonedaEquiv hw
  rw [SSet.yonedaEquiv_comp] at hv
  have hr := yonedaEquiv_precomp_operator β (SimplexCategory.δ (1 : Fin 2))
  change SSet.yonedaEquiv (SSet.stdSimplex.δ 1 ≫ β) = _ at hr
  rw [hr] at hv
  exact hv.symm

/-- Glue the given relative one-horn data into the actual joined inner-horn domain. -/
theorem glue_one_horn {X : SSet.{u}} (k : ℕ)
    (φ : (Λ[1, 0] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X)
    (β : (Δ[1] : SSet.{u}) ⟶ boundaryJoinedPresheaf k X)
    (w : φ ≫ joinedBoundaryRestriction k X = Λ[1, 0].ι ≫ β) :
    ∃ Γ : ((prefixBoundary k 1 ⊔
        SSet.stdSimplex.face {suffixIndex k 1 1}ᶜ :
        (Δ[k + 2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X,
      SSet.Subcomplex.homOfLE le_sup_left ≫ Γ = SSet.yonedaEquiv β ∧
      (SSet.stdSimplex.faceSingletonComplIso (suffixIndex k 1 1)).hom ≫
        SSet.Subcomplex.homOfLE le_sup_right ≫ Γ =
          (SSet.yonedaEquiv (X := X) (n := ⦋k + 1⦌)).symm
            ((SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋0⦌))
          (SSet.horn.ι (n := 0) 0 1 (by decide) ≫ φ)) := by
  exact glue_coface k 0 1 (SSet.yonedaEquiv β)
    ((SSet.yonedaEquiv (X := X) (n := ⦋k + 1⦌)).symm
      ((SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋0⦌))
          (SSet.horn.ι (n := 0) 0 1 (by decide) ≫ φ))) (one_horn_overlap k φ β w)

end

end DaggerOriginalJoinedOneHornGluing
