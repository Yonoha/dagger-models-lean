import ActualCoreOppositeMembership
import NativeSubcomplexOppositeRestriction

/-! Instantiate the generic original subcomplex maps at the exact original ordinary core. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerActualCoreOppositeMembership
open DaggerNativeSubcomplexOppositeRestriction
universe u
namespace DaggerActualCoreOppositeMaps
noncomputable section

def coreOpMap (X : SSet.{u}) [X.Quasicategory] :
    (ordinaryCoreCandidate X : SSet.{u}).op ⟶ (ordinaryCoreCandidate X.op : SSet.{u}) :=
  forward (ordinaryCoreCandidate X) (ordinaryCoreCandidate X.op) (op_mem_core X)

def coreOpInv (X : SSet.{u}) [X.Quasicategory] :
    (ordinaryCoreCandidate X.op : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u}).op :=
  backward (ordinaryCoreCandidate X) (ordinaryCoreCandidate X.op) (inv_mem_core X)

theorem coreOpMap_val (X : SSet.{u}) [X.Quasicategory] (q : SimplexCategoryᵒᵖ)
    (s : (ordinaryCoreCandidate X : SSet.{u}).op.obj q) :
    ((coreOpMap X).app q s).val = s.val :=
  forward_val (ordinaryCoreCandidate X) (ordinaryCoreCandidate X.op) (op_mem_core X) q s

theorem coreOpInv_val (X : SSet.{u}) [X.Quasicategory] (q : SimplexCategoryᵒᵖ)
    (s : (ordinaryCoreCandidate X.op : SSet.{u}).obj q) :
    ((coreOpInv X).app q s).val = s.val :=
  backward_val (ordinaryCoreCandidate X) (ordinaryCoreCandidate X.op) (inv_mem_core X) q s

end
end DaggerActualCoreOppositeMaps
