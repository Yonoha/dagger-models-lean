import NativeKanSimplicialOpposite
import NativeKanSourceOriginalCoreFactor

/-! Opaque membership proofs separate Kan factorization from original simplex values. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerNativeKanSimplicialOpposite DaggerNativeQuasicategoryOpposite
open DaggerNativeKanSourceOriginalCoreFactor DaggerOriginalOrdinaryKanCoreSubcomplex
universe u
namespace DaggerActualCoreOppositeMembership
noncomputable section

theorem op_mem_core (X : SSet.{u}) [X.Quasicategory] (q : SimplexCategoryᵒᵖ)
    (s : (ordinaryCoreCandidate X : SSet.{u}).op.obj q) :
    s.val ∈ (ordinaryCoreCandidate X.op).obj q := by
  letI : (ordinaryCoreCandidate X : SSet.{u}).KanComplex := native_quasi_core_kan X
  letI : (ordinaryCoreCandidate X : SSet.{u}).op.KanComplex :=
    kan_op (ordinaryCoreCandidate X : SSet.{u})
  exact kan_map_mem_core (SSet.opFunctor.map (ordinaryCoreCandidate X).ι) q s

theorem inv_mem_core (X : SSet.{u}) [X.Quasicategory] (q : SimplexCategoryᵒᵖ)
    (s : (ordinaryCoreCandidate X.op : SSet.{u}).obj q) :
    s.val ∈ (ordinaryCoreCandidate X).obj q := by
  letI : X.op.Quasicategory := quasicategory_op X
  letI : (ordinaryCoreCandidate X.op : SSet.{u}).KanComplex := native_quasi_core_kan X.op
  letI : (ordinaryCoreCandidate X.op : SSet.{u}).op.KanComplex :=
    kan_op (ordinaryCoreCandidate X.op : SSet.{u})
  exact kan_map_mem_core
    (SSet.opFunctor.map (ordinaryCoreCandidate X.op).ι ≫
      (SSet.opFunctorCompOpFunctorIso.app X).hom) q
    (show (ordinaryCoreCandidate X.op : SSet.{u}).op.obj q from s)

end
end DaggerActualCoreOppositeMembership
