import NativeDiagonalHornCellGeometry
import NativeReedyBoxUnionLifting
import NativePartialFaceUnionContraction

/-! Actual Reedy lifts for the original horn matrix's required horizontal attachment cells. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBoxUnion
open DaggerNativeDiagonalHornMatrix DaggerNativePartialFaceUnionGeometry
open DaggerNativeDiagonalHornCellGeometry DaggerNativeReedyBoxUnionLifting
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeDiagonalHornCellLifting
noncomputable section

def cellInclusion {n p : ℕ} (k : Fin (n + 1))
    (θ : (Δ[p] : SSet.{u}) ⟶ SSet.horn n k) :=
  unionInclusion (SSet.boundary p) (faceUnion (cellFaces k θ))

theorem cell_vertical_anodyne {n p : ℕ} (k : Fin (n + 1))
    (θ : (Δ[p] : SSet.{u}) ⟶ SSet.horn n k) :
    trivialCofibrations SSet.{u} (faceUnion (cellFaces k θ)).ι :=
  DaggerNativePartialFaceUnionContraction.inclusion_trivial_cofibration
    (cellFaces k θ) k (missingFaces_missing k _ (SSet.yonedaEquiv θ))
    (missingFaces_nonempty k _ (SSet.yonedaEquiv θ))

theorem cell_lifting {n p : ℕ} (k : Fin (n + 1))
    (θ : (Δ[p] : SSet.{u}) ⟶ SSet.horn n k)
    {X Y : BiSSet.{u}} (f : X ⟶ Y) (hf : ReedyFibration f) :
    HasLiftingProperty (cellInclusion k θ) f := by
  have : WeakEquivalence (faceUnion (cellFaces k θ)).ι :=
    ((mem_trivialCofibrations_iff _).mp (cell_vertical_anodyne k θ)).2
  exact union_lifting (SSet.boundary p) (faceUnion (cellFaces k θ)) f hf

end
end DaggerNativeDiagonalHornCellLifting
