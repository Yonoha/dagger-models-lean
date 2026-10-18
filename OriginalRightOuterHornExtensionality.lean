import OriginalRightOuterHornInclusions

/-!
# Original right outer horn maps are determined by the boundary and suffix face

Every supplied original horn face is either an original omitted-prefix face
or the original suffix-zero face. The original native coface inclusions and
horn extensionality therefore detect equality on the entire original horn,
using whole-boundary equality and the original joined suffix-face map.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedCofaces DaggerOriginalRestBoundaryInverseFaceMaps
open DaggerOriginalRightOuterHornInclusions

universe u

namespace DaggerOriginalRightOuterHornExtensionality

noncomputable section

/-- Every actual original prefix index differs from the omitted last horn index. -/
theorem rightOuterPrefixIndex_ne_last (k : ℕ) (j : Fin (k + 1)) :
    prefixIndex k 1 j ≠ Fin.last (k + 2) := by
  intro h
  have hv := congrArg Fin.val h
  change j.val = k + 2 at hv
  have hj := j.isLt
  omega

/-- Each original standard prefix coface is the same actual coface of the right outer horn. -/
theorem rightOuterPrefixFace_square (k : ℕ) (j : Fin (k + 1)) :
    prefixFaceBoundaryInclusion.{u} k 1 j ≫ rightOuterBoundaryInclusion k =
      SSet.horn.ι (Fin.last (k + 2)) (prefixIndex k 1 j) (rightOuterPrefixIndex_ne_last k j) := by
  apply (cancel_mono Λ[k + 2, Fin.last (k + 2)].ι).mp
  rw [Category.assoc, rightOuterBoundaryInclusion_comp, prefixFaceBoundaryInclusion_comp,
    SSet.horn.ι_ι]

/-- The actual original whole boundary and suffix-zero face determine every right outer horn
map, with no filling or invertibility assumption. -/
theorem rightOuterHorn_hom_ext {X : SSet.{u}} (k : ℕ)
    (φ ψ : (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) ⟶ X)
    (hboundary : rightOuterBoundaryInclusion k ≫ φ = rightOuterBoundaryInclusion k ≫ ψ)
    (hface : rightOuterJoinedFaceInclusion k ≫ φ = rightOuterJoinedFaceInclusion k ≫ ψ) :
    φ = ψ := by
  apply SSet.horn.hom_ext
  intro j hj
  rcases vertex_eq_prefix_or_suffix k 1 j with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · have h := congrArg (fun f ↦ prefixFaceBoundaryInclusion k 1 a ≫ f) hboundary
    dsimp only at h
    rw [← Category.assoc, rightOuterPrefixFace_square,
      ← Category.assoc, rightOuterPrefixFace_square] at h
    simpa only [SSet.yonedaEquiv_comp, SSet.horn.yonedaEquiv_ι] using
      congrArg SSet.yonedaEquiv h
  · have ha : a = 0 := by
      apply Fin.ext
      have hlt := a.isLt
      have hv : k + 1 + a.val ≠ k + 2 := by
        intro h
        apply hj
        exact Fin.ext h
      change a.val = 0
      omega
    subst a
    simpa only [rightOuterJoinedFaceInclusion, SSet.yonedaEquiv_comp,
      SSet.horn.yonedaEquiv_ι] using congrArg SSet.yonedaEquiv hface

end

end DaggerOriginalRightOuterHornExtensionality
