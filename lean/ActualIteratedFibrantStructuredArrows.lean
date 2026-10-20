import NativePositiveStructuredArrowContraction

/-! The exact under-comma categories of the positive iterated-gadget inclusion are contractible. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory DaggerModels OrdinaryRigidification
open DaggerActualIteratedGadgetData DaggerActualIteratedGadgetShift
open DaggerOriginalProductGadget DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualIteratedFibrantStructuredArrows
noncomputable section

/-- Contractibility holds at every original gadget over N(D), retaining its whole map. -/
theorem point_GW (D : SimplicialCat.{u, u})
    (hD : ∀ x y : D.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌))
    (O : Over (coherentNerve.obj D) a b) :
    GW (pointMap (nerve (StructuredArrow O (inclusion D a b)))) := by
  obtain ⟨r, hr⟩ := DaggerActualFibrantGadgetExtensions.exists_retraction D hD
  exact DaggerNativePositiveStructuredArrowContraction.selected_point_GW
    (positive D a b) (over D r hr a b) (overUnit D r hr a b) (fun _ ↦ Nat.succ_pos _) O

/-- This is the actual terminal-map predicate with the same original structured-arrow domain. -/
theorem toUnit_GW (D : SimplicialCat.{u, u})
    (hD : ∀ x y : D.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌))
    (O : Over (coherentNerve.obj D) a b) :
    GW (toUnit (nerve (StructuredArrow O (inclusion D a b)))) := by
  let X := nerve (StructuredArrow O (inclusion D a b))
  let e := pointIsTerminal.{u}.uniqueUpToIso (isTerminalTensorUnit (C := SSet.{u}))
  have : IsIso e.hom := e.isIso_hom
  have : WeakEquivalence (pointMap X) := (weakEquivalence_iff_GW _).mpr (point_GW D hD a b O)
  have he : pointMap X ≫ e.hom = toUnit X := isTerminalTensorUnit.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

end
end DaggerActualIteratedFibrantStructuredArrows
