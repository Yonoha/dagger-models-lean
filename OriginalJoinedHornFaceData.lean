import OriginalJoinedCofaceGluing

/-!
# Actual joined coface maps from arbitrary relative horn data

For every face of an arbitrary-dimensional original horn, the original
commuting square gives the exact overlap with the prescribed joined boundary.
Each face can therefore be glued to that boundary using the native pushout.
These maps retain the original face simplex; their simultaneous gluing along
all mutual intersections is a separate remaining obligation.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedHornPrefix
open DaggerOriginalJoinedPrefixBoundaryFunctor
open DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalJoinedCofaceGluing

universe u

namespace DaggerOriginalJoinedHornFaceData

noncomputable section

/-- The original relative horn square gives the literal overlap equation for every coface. -/
theorem horn_face_overlap {X : SSet.{u}} (k n : ℕ) (i j : Fin (n + 2)) (hj : j ≠ i)
    (φ : (Λ[n + 1, i] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X)
    (β : (Δ[n + 1] : SSet.{u}) ⟶ boundaryJoinedPresheaf k X)
    (w : φ ≫ joinedBoundaryRestriction k X = Λ[n + 1, i].ι ≫ β) :
    prefixBoundaryMap k (SimplexCategory.δ j) ≫ SSet.yonedaEquiv β =
      (prefixBoundary k n).ι ≫
        (SSet.yonedaEquiv (X := X) (n := ⦋k + n + 1⦌)).symm
          ((SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋n⦌))
            (SSet.horn.ι i j hj ≫ φ)) := by
  have hw : (SSet.horn.ι i j hj ≫ φ) ≫ joinedBoundaryRestriction k X =
      SSet.stdSimplex.δ j ≫ β := by
    rw [Category.assoc, w, ← Category.assoc, SSet.horn.ι_ι]
  have hv := congrArg SSet.yonedaEquiv hw
  rw [SSet.yonedaEquiv_comp] at hv
  have hr := yonedaEquiv_precomp_operator β (SimplexCategory.δ j)
  change SSet.yonedaEquiv (SSet.stdSimplex.δ j ≫ β) = _ at hr
  rw [hr] at hv
  exact hv.symm

/-- Construct the map on the actual joined boundary union each supplied horn face. -/
theorem glue_horn_face {X : SSet.{u}} (k n : ℕ) (i j : Fin (n + 2)) (hj : j ≠ i)
    (φ : (Λ[n + 1, i] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X)
    (β : (Δ[n + 1] : SSet.{u}) ⟶ boundaryJoinedPresheaf k X)
    (w : φ ≫ joinedBoundaryRestriction k X = Λ[n + 1, i].ι ≫ β) :
    ∃ Γ : ((prefixBoundary k (n + 1) ⊔
        SSet.stdSimplex.face {suffixIndex k (n + 1) j}ᶜ :
        (Δ[k + (n + 1) + 1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X,
      SSet.Subcomplex.homOfLE le_sup_left ≫ Γ = SSet.yonedaEquiv β ∧
      (SSet.stdSimplex.faceSingletonComplIso (suffixIndex k (n + 1) j)).hom ≫
        SSet.Subcomplex.homOfLE le_sup_right ≫ Γ =
          (SSet.yonedaEquiv (X := X) (n := ⦋k + n + 1⦌)).symm
            ((SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋n⦌))
              (SSet.horn.ι i j hj ≫ φ)) :=
  glue_coface k n j (SSet.yonedaEquiv β)
    ((SSet.yonedaEquiv (X := X) (n := ⦋k + n + 1⦌)).symm
      ((SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋n⦌))
        (SSet.horn.ι i j hj ≫ φ))) (horn_face_overlap k n i j hj φ β w)

end

end DaggerOriginalJoinedHornFaceData
