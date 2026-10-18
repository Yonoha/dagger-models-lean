import ActualOrdinaryCoreOpposite

/-! Read original core-map values from the original inclusion equation, without unfolding ho. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex
universe u
namespace DaggerActualOrdinaryCoreMapValue
noncomputable section

theorem core_map_val {X Y : SSet.{u}} (f : X ⟶ Y) (q : SimplexCategoryᵒᵖ)
    (s : (ordinaryCoreCandidate X : SSet.{u}).obj q) :
    ((ordinaryCoreCandidateMap f).app q s).val = f.app q s.val :=
  congrFun (NatTrans.congr_app (ordinaryCoreCandidateMap_comp_ι f) q) s

theorem core_map_mem {X Y : SSet.{u}} (f : X ⟶ Y) (q : SimplexCategoryᵒᵖ)
    (s : (ordinaryCoreCandidate X : SSet.{u}).obj q) :
    f.app q s.val ∈ (ordinaryCoreCandidate Y).obj q := by
  rw [← core_map_val f q s]
  exact ((ordinaryCoreCandidateMap f).app q s).property

end
end DaggerActualOrdinaryCoreMapValue
