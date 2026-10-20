import OriginalJoinedHornFaceData

/-!
# Original common-face relations between joined horn coface maps

Naturality of the original horn map transfers an equality of original horn
operators to the joined face maps. In particular, the native two-coface
identity supplies the common-face relation in every dimension. No compatibility
of a completed horn map or additional filling assumption is used.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft
open DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornPrefix
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedCofaces

universe u

namespace DaggerOriginalJoinedHornFaceCompatibility

/-- An equality of actual operators into the original horn gives the joined operator equality. -/
theorem joined_face_operator_compatibility {X : SSet.{u}} (k m n : ℕ)
    (i j l : Fin (n + 2)) (hj : j ≠ i) (hl : l ≠ i)
    (φ : (Λ[n + 1, i] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X)
    (α γ : ⦋m⦌ ⟶ ⦋n⦌)
    (w : SSet.stdSimplex.map α ≫ SSet.horn.ι.{u} i j hj =
      SSet.stdSimplex.map γ ≫ SSet.horn.ι i l hl) :
    SSet.stdSimplex.map ((ordinalJoinLeft ⦋k⦌).map α) ≫
        (SSet.yonedaEquiv (X := X) (n := ⦋k + n + 1⦌)).symm
          ((SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋n⦌))
            (SSet.horn.ι i j hj ≫ φ)) =
      SSet.stdSimplex.map ((ordinalJoinLeft ⦋k⦌).map γ) ≫
        (SSet.yonedaEquiv (X := X) (n := ⦋k + n + 1⦌)).symm
          ((SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋n⦌))
            (SSet.horn.ι i l hl ≫ φ)) := by
  apply (SSet.yonedaEquiv (X := X) (n := ⦋k + m + 1⦌)).injective
  have hα := yonedaEquiv_precomp_operator (k := k + m + 1) (m := k + n + 1)
    ((SSet.yonedaEquiv (X := X) (n := ⦋k + n + 1⦌)).symm
      ((SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋n⦌))
        (SSet.horn.ι i j hj ≫ φ))) ((ordinalJoinLeft ⦋k⦌).map α)
  have hγ := yonedaEquiv_precomp_operator (k := k + m + 1) (m := k + n + 1)
    ((SSet.yonedaEquiv (X := X) (n := ⦋k + n + 1⦌)).symm
      ((SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋n⦌))
        (SSet.horn.ι i l hl ≫ φ))) ((ordinalJoinLeft ⦋k⦌).map γ)
  rw [hα, hγ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hw := congrArg (fun t ↦ t ≫ φ) w
  dsimp only at hw
  rw [Category.assoc, Category.assoc] at hw
  have hv := congrArg (SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋m⦌)) hw
  rw [yonedaEquiv_precomp_operator, yonedaEquiv_precomp_operator] at hv
  exact hv

/-- Native coface identities give the actual common-face relation between two joined cofaces. -/
theorem joined_two_coface_compatibility {X : SSet.{u}} (k n : ℕ)
    (i : Fin (n + 3)) (a b : Fin (n + 2)) (hab : a ≤ b)
    (hb : b.succ ≠ i) (ha : a.castSucc ≠ i)
    (φ : (Λ[n + 2, i] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X) :
    SSet.stdSimplex.δ (suffixIndex k (n + 1) a) ≫
        (SSet.yonedaEquiv (X := X) (n := ⦋k + (n + 1) + 1⦌)).symm
          ((SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋n + 1⦌))
            (SSet.horn.ι i b.succ hb ≫ φ)) =
      SSet.stdSimplex.δ (suffixIndex k (n + 1) b) ≫
        (SSet.yonedaEquiv (X := X) (n := ⦋k + (n + 1) + 1⦌)).symm
          ((SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋n + 1⦌))
            (SSet.horn.ι i a.castSucc ha ≫ φ)) := by
  have w : SSet.stdSimplex.map (SimplexCategory.δ a) ≫ SSet.horn.ι.{u} i b.succ hb =
      SSet.stdSimplex.map (SimplexCategory.δ b) ≫ SSet.horn.ι i a.castSucc ha := by
    apply (cancel_mono Λ[n + 2, i].ι).mp
    rw [Category.assoc, SSet.horn.ι_ι, Category.assoc, SSet.horn.ι_ι]
    exact (SSet.stdSimplex.map_comp _ _).symm.trans
      ((congrArg SSet.stdSimplex.map (SimplexCategory.δ_comp_δ hab)).trans
        (SSet.stdSimplex.map_comp _ _))
  have h := joined_face_operator_compatibility k n (n + 1) i b.succ a.castSucc hb ha
    φ (SimplexCategory.δ a) (SimplexCategory.δ b) w
  rw [joinMap_coface, joinMap_coface] at h
  exact h

end DaggerOriginalJoinedHornFaceCompatibility
