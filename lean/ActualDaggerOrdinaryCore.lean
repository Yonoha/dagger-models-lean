import ActualOrdinaryCoreMapValue
import NativeDaggerSubcomplexRestriction

/-! The literal original ordinary core inherits the original fixed-vertex dagger. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerNativeKanSourceOriginalCoreFactor
open DaggerActualCoreOppositeMembership DaggerActualOrdinaryCoreMapValue
universe u
namespace DaggerActualDaggerOrdinaryCore
noncomputable section

theorem dagger_stable (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (q : SimplexCategoryᵒᵖ) (s : (ordinaryCoreCandidate X.toSSet : SSet.{u}).obj q) :
    X.dagger.app q s.val ∈ (ordinaryCoreCandidate X.toSSet).obj q := by
  rw [← core_map_val X.dagger q s]
  exact inv_mem_core X.toSSet q ((ordinaryCoreCandidateMap X.dagger).app q s)

def coreDagger (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] : DaggerSSet.{u} :=
  DaggerNativeDaggerSubcomplexRestriction.restricted X
    (ordinaryCoreCandidate X.toSSet) (dagger_stable X)

theorem coreDagger_toSSet (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] :
    (coreDagger X).toSSet = (ordinaryCoreCandidate X.toSSet : SSet.{u}) :=
  DaggerNativeDaggerSubcomplexRestriction.restricted_toSSet _ _ _

theorem coreDagger_dagger_val (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (n : ℕ) (s : (coreDagger X).toSSet _⦋n⦌) :
    ((coreDagger X).dagger.app (op ⦋n⦌) s).val = X.dagger.app (op ⦋n⦌) s.val :=
  DaggerNativeDaggerSubcomplexRestriction.dagger_val _ _ _ n s

theorem coreDagger_kan (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] :
    (coreDagger X).toSSet.KanComplex := by
  rw [coreDagger_toSSet]
  exact native_quasi_core_kan X.toSSet

def coreVerticesEquiv (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] :
    (coreDagger X).toSSet _⦋0⦌ ≃ X.toSSet _⦋0⦌ :=
  DaggerNativeDaggerSubcomplexRestriction.verticesEquiv _ _ _
    (vertex_mem_ordinaryCoreCandidate X.toSSet)

end
end DaggerActualDaggerOrdinaryCore
