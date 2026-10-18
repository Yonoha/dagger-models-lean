import NativeKanRigHomWeakRecognition

/-! Actual weak maps between native Kan complexes give point-preserving component equivalences. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeKanWeakComponents
noncomputable section

def equivalence {X Y : SSet.{u}} [X.KanComplex] [Y.KanComplex]
    (f : X ⟶ Y) (hf : WeakEquivalence f) : X.π₀ ≃ Y.π₀ :=
  Equiv.ofBijective (SSet.mapπ₀ f)
    ((SSet.weakEquivalence_iff_kanComplexW f).mp hf).bijective_mapπ₀

theorem equivalence_vertex {X Y : SSet.{u}} [X.KanComplex] [Y.KanComplex]
    (f : X ⟶ Y) (hf : WeakEquivalence f) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (h : f.app (op ⦋0⦌) x = y) : equivalence f hf (SSet.π₀.mk x) = SSet.π₀.mk y := by
  change SSet.mapπ₀ f (SSet.π₀.mk x) = _
  rw [SSet.mapπ₀_mk, h]

theorem equivalence_symm_vertex {X Y : SSet.{u}} [X.KanComplex] [Y.KanComplex]
    (f : X ⟶ Y) (hf : WeakEquivalence f) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (h : f.app (op ⦋0⦌) x = y) :
    (equivalence f hf).symm (SSet.π₀.mk y) = SSet.π₀.mk x :=
  (equivalence f hf).symm_apply_eq.mpr (equivalence_vertex f hf x y h).symm

end
end DaggerNativeKanWeakComponents
