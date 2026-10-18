import NativeKanSourceOriginalCoreFactor
import NativeWalkingIntervalHomotopyCategory
import Mathlib.AlgebraicTopology.Quasicategory.Nerve

/-! The exact original walking nerve and products of native Kan objects are Kan. -/
set_option autoImplicit false
open CategoryTheory Simplicial HomotopicalAlgebra MonoidalCategory CartesianMonoidalCategory
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerNativeWalkingIntervalHomotopyCategory
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalQuasicategoryInverseEdgeRepresentatives
open DaggerOriginalNativeKanFromHornFillers DaggerNativeKanSourceOriginalCoreFactor
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeWalkingKanTensor
noncomputable section

theorem walking_edge_invertible (q : J.{u} _⦋1⦌) : edgeIsInvertible J.{u} q := by
  let e := SSet.Edge.mk' q
  have he : SSet.Truncated.HomotopyCategory.homMk e = (hoWalkingObjectIso _ _).hom :=
    @Subsingleton.elim _ (hoWalkingHomSubsingleton _ _) _ _
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk e) := by
    rw [he]
    infer_instance
  exact (edgeIsInvertible_iff_original_homMk_isIso J e).mpr inferInstance

theorem walking_core_eq_top : ordinaryCoreCandidate J.{u} = ⊤ := by
  apply top_unique
  intro q s _
  apply (mem_ordinaryCoreCandidate_iff_edges_iso J q s).mpr
  intro α
  exact walking_edge_invertible _

theorem walking_kan : J.{u}.KanComplex := by
  have : (ordinaryCoreCandidate J.{u} : SSet.{u}).KanComplex := native_quasi_core_kan J
  let e : (ordinaryCoreCandidate J.{u} : SSet.{u}) ≅ J.{u} :=
    SSet.Subcomplex.isoOfEq walking_core_eq_top ≪≫ SSet.Subcomplex.topIso J
  have : Fibration e.inv := inferInstance
  exact isFibrant_of_fibration e.inv

theorem kan_tensor (K L : SSet.{u}) [K.KanComplex] [L.KanComplex] :
    (K ⊗ L).KanComplex := by
  apply kanComplex_of_hornFillers
  intro n i φ
  obtain ⟨a, ha⟩ := SSet.KanComplex.hornFilling (φ ≫ fst K L)
  obtain ⟨b, hb⟩ := SSet.KanComplex.hornFilling (φ ≫ snd K L)
  refine ⟨lift a b, ?_⟩
  apply NatTrans.ext
  funext q x
  exact Prod.ext (congrFun (NatTrans.congr_app ha q) x)
    (congrFun (NatTrans.congr_app hb q) x)

end
end DaggerNativeWalkingKanTensor
