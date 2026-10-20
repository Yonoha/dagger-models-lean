import NativeDiagonalHornCellGeometry

/-! The original vertical face-union box maps into the entire original horn matrix. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeBisimplicialBox DaggerNativeDiagonalHornMatrix
open DaggerNativeDiagonalHornCellGeometry DaggerNativePartialFaceUnionGeometry
universe u
namespace DaggerNativeDiagonalHornCellVertical
noncomputable section

theorem theta_factor {n p : ℕ} (k : Fin (n + 1))
    (θ : (Δ[p] : SSet.{u}) ⟶ SSet.horn n k) (h : SimplexCategoryᵒᵖ)
    (a : (Δ[p] : SSet.{u}).obj h) :
    (SSet.horn n k : SSet.{u}).map (SSet.stdSimplex.objEquiv a).op
      (SSet.yonedaEquiv θ) = θ.app h a := by
  have hh := congrFun (θ.naturality (SSet.stdSimplex.objEquiv a).op)
    (SSet.stdSimplex.objEquiv.symm (𝟙 _))
  change θ.app h ((Δ[p] : SSet.{u}).map (SSet.stdSimplex.objEquiv a).op
      (SSet.stdSimplex.objEquiv.symm (𝟙 _))) =
    (SSet.horn n k : SSet.{u}).map (SSet.stdSimplex.objEquiv a).op
      (SSet.yonedaEquiv θ) at hh
  simpa only [SSet.stdSimplex.map_apply, Quiver.Hom.unop_op, Equiv.apply_symm_apply,
    Category.comp_id, Equiv.symm_apply_apply] using hh.symm

theorem cellFaces_subset {n p : ℕ} (k : Fin (n + 1))
    (θ : (Δ[p] : SSet.{u}) ⟶ SSet.horn n k) (h : SimplexCategoryᵒᵖ)
    (a : (Δ[p] : SSet.{u}).obj h) : cellFaces k θ ⊆ missingFaces k h (θ.app h a) := by
  rw [← theta_factor k θ h a]
  exact missingFaces_mono k (SSet.stdSimplex.objEquiv a).op (SSet.yonedaEquiv θ)

def verticalMatrixMap {n p : ℕ} (k : Fin (n + 1))
    (θ : (Δ[p] : SSet.{u}) ⟶ SSet.horn n k) :
    box (Δ[p] : SSet.{u}) (faceUnion (cellFaces k θ) : SSet.{u}) ⟶ hornMatrix n k where
  app h :=
    { app := fun v x ↦ ⟨(θ.app h x.1, x.2.val),
        faceUnion_mono (cellFaces_subset k θ h x.1) v x.2.property⟩
      naturality := by intros; funext x; apply Subtype.ext; rfl }
  naturality h l α := by
    apply NatTrans.ext
    funext v x
    apply Subtype.ext
    exact Prod.ext (congrFun (θ.naturality α) x.1) rfl

theorem verticalMatrixMap_square {n p : ℕ} (k : Fin (n + 1))
    (θ : (Δ[p] : SSet.{u}) ⟶ SSet.horn n k) :
    verticalMatrixMap k θ ≫ matrixInclusion n k =
      boxMap θ (faceUnion (cellFaces k θ)).ι := by
  apply NatTrans.ext
  funext h
  apply NatTrans.ext
  rfl

end
end DaggerNativeDiagonalHornCellVertical
