import NativeDiagonalHornMatrix
import NativeBisimplicialBoxUnion

/-! Exact original matrix data on a horizontal simplex, modulo its original boundary. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeBisimplicialBox DaggerNativeBisimplicialBoxUnion
open DaggerNativeDiagonalHornMatrix DaggerNativePartialFaceUnionGeometry
universe u
namespace DaggerNativeDiagonalHornCellGeometry
noncomputable section

theorem missingFaces_surjective {n : ℕ} (k : Fin (n + 1))
    {h l : SimplexCategoryᵒᵖ} (α : h ⟶ l)
    (hs : Function.Surjective α.unop.toOrderHom)
    (a : (SSet.horn.{u} n k : SSet.{u}).obj h) :
    missingFaces k l ((SSet.horn n k : SSet.{u}).map α a) = missingFaces k h a := by
  classical
  apply Finset.Subset.antisymm
  · intro j hj
    have hh := (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh.1, ?_⟩
    intro r
    obtain ⟨s, hs⟩ := hs r
    have ht := hh.2 s
    change SSet.stdSimplex.asOrderHom a (α.unop.toOrderHom s) ≠ j at ht
    simpa only [hs] using ht
  · exact missingFaces_mono k α a

def cellFaces {n p : ℕ} (k : Fin (n + 1))
    (θ : (Δ[p] : SSet.{u}) ⟶ SSet.horn n k) : Finset (Fin (n + 1)) :=
  missingFaces k (op ⦋p⦌) (SSet.yonedaEquiv θ)

theorem cellFaces_nonboundary {n p : ℕ} (k : Fin (n + 1))
    (θ : (Δ[p] : SSet.{u}) ⟶ SSet.horn n k) (h : SimplexCategoryᵒᵖ)
    (a : (Δ[p] : SSet.{u}).obj h) (ha : a ∉ (SSet.boundary p).obj h) :
    missingFaces k h (θ.app h a) = cellFaces k θ := by
  classical
  let α : op ⦋p⦌ ⟶ h := (SSet.stdSimplex.objEquiv a).op
  have hs : Function.Surjective α.unop.toOrderHom := by
    change ¬¬Function.Surjective (SSet.stdSimplex.asOrderHom a) at ha
    exact not_not.mp ha
  have he : (SSet.horn n k : SSet.{u}).map α (SSet.yonedaEquiv θ) = θ.app h a := by
    have hh := congrFun (θ.naturality α) (SSet.stdSimplex.objEquiv.symm (𝟙 _))
    change θ.app h ((Δ[p] : SSet.{u}).map α (SSet.stdSimplex.objEquiv.symm (𝟙 _))) =
      (SSet.horn n k : SSet.{u}).map α (SSet.yonedaEquiv θ) at hh
    simpa only [SSet.stdSimplex.map_apply, α, Quiver.Hom.unop_op,
      Equiv.apply_symm_apply, Category.comp_id, Equiv.symm_apply_apply] using hh.symm
  rw [← he]
  exact missingFaces_surjective k α hs (SSet.yonedaEquiv θ)

def cellMatrixRow {n p : ℕ} (k : Fin (n + 1))
    (θ : (Δ[p] : SSet.{u}) ⟶ SSet.horn n k) (h : SimplexCategoryᵒᵖ) :
    (boxRow ((Δ[p] : SSet.{u}).obj h) (Δ[n] : SSet.{u})).Subcomplex :=
  (matrixRow k h).preimage ((boxMap θ (𝟙 (Δ[n] : SSet.{u}))).app h)

theorem cellMatrixRow_nonboundary {n p : ℕ} (k : Fin (n + 1))
    (θ : (Δ[p] : SSet.{u}) ⟶ SSet.horn n k) (h v : SimplexCategoryᵒᵖ)
    (a : (Δ[p] : SSet.{u}).obj h) (b : (Δ[n] : SSet.{u}).obj v)
    (ha : a ∉ (SSet.boundary p).obj h) :
    (a, b) ∈ (cellMatrixRow k θ h).obj v ↔ b ∈ (faceUnion (cellFaces k θ)).obj v := by
  change b ∈ (faceUnion (missingFaces k h (θ.app h a))).obj v ↔ _
  rw [cellFaces_nonboundary k θ h a ha]

theorem cellMatrixRow_union_boundary {n p : ℕ} (k : Fin (n + 1))
    (θ : (Δ[p] : SSet.{u}) ⟶ SSet.horn n k) (h : SimplexCategoryᵒᵖ) :
    unionRow (SSet.boundary p) (⊥ : (Δ[n] : SSet.{u}).Subcomplex) h ⊔ cellMatrixRow k θ h =
      unionRow (SSet.boundary p) (faceUnion (cellFaces k θ)) h := by
  ext v x
  change ((x.1 ∈ (SSet.boundary p).obj h ∨ False) ∨
    x ∈ (cellMatrixRow k θ h).obj v) ↔
      x.1 ∈ (SSet.boundary p).obj h ∨ x.2 ∈ (faceUnion (cellFaces k θ)).obj v
  by_cases ha : x.1 ∈ (SSet.boundary p).obj h
  · simp only [ha, true_or]
  · simpa only [ha, false_or] using cellMatrixRow_nonboundary k θ h v x.1 x.2 ha

end
end DaggerNativeDiagonalHornCellGeometry
