import NativePositivePartialMatchingPi
import NativeHorizontalPiFamilyLifting

/-! Original positive homotopy classes lift along every proper nonempty partial-face inclusion. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite SSet.KanComplex
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeHorizontalPiCompatibility
open DaggerNativeHorizontalPiSections DaggerNativePartialFaceUnionGeometry
open DaggerNativeReedyFibrantHorizontalMapping DaggerNativePositivePartialMatchingPi
open DaggerNativeHorizontalPiFamilyLifting
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePositivePartialMatchingRestriction
noncomputable section

theorem partialFace_restriction_mapπ_surjective (X : BiSSet.{u}) (hX : ReedyFibrant X)
    (hπ : ∀ r : ℕ, Fibration (C := SSet.{u}) (rowProjection X (r + 1)))
    (m : ℕ) (S : Finset (Fin (m + 1))) (k : Fin (m + 1)) (hk : k ∉ S)
    (hS : S.Nonempty) (q : ℕ) (v : (horizontalMapping (Δ[m] : SSet.{u}) X) _⦋0⦌) :
    Function.Surjective (mapπ (horizontalPre (faceUnion.{u} S).ι X) (q + 1) v
      ((horizontalPre (faceUnion.{u} S).ι X).app _ v) rfl) := by
  have ht := (mem_trivialCofibrations_iff _).mp
    (DaggerNativePartialFaceUnionContraction.inclusion_trivial_cofibration S k hk hS)
  have : Cofibration (faceUnion.{u} S).ι := ht.1
  have : WeakEquivalence (faceUnion.{u} S).ι := ht.2
  have : Fibration (C := SSet.{u}) (rowProjection X (q + 1)) := hπ q
  exact simplex_restriction_mapπ_surjective (X := X) (t := q + 1)
    (j := (faceUnion.{u} S).ι) (v := v)
    (hK := (partialFace_piComparison_bijective X hX hπ m S k hk hS q _).1)

theorem partialFace_restriction_mapπ_surjective_rebased (X : BiSSet.{u})
    (hX : ReedyFibrant X)
    (hπ : ∀ r : ℕ, Fibration (C := SSet.{u}) (rowProjection X (r + 1)))
    (m : ℕ) (S : Finset (Fin (m + 1))) (k : Fin (m + 1)) (hk : k ∉ S)
    (hS : S.Nonempty) (q : ℕ) (v : (horizontalMapping (Δ[m] : SSet.{u}) X) _⦋0⦌)
    (w : (horizontalMapping (faceUnion.{u} S) X) _⦋0⦌)
    (hw : (horizontalPre (faceUnion.{u} S).ι X).app _ v = w) :
    Function.Surjective (mapπ (horizontalPre (faceUnion.{u} S).ι X) (q + 1) v w hw) := by
  subst w
  exact partialFace_restriction_mapπ_surjective X hX hπ m S k hk hS q v

end
end DaggerNativePositivePartialMatchingRestriction
