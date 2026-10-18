import OriginalFlagFlankInclusion

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {T U : NecklaceCode} {n : ℕ}
variable (F : Flag.{u} T n) (G : Flag.{u} U n)
variable (f : NecklaceCode.Hom.{u} T U) (hfg : NecklaceCode.Flag.map f F = G)

include hfg in
theorem flagged_arrow_image (i : Fin (n + 1)) :
    mapVertices f.map '' F.chain i = G.chain i :=
  congrArg (fun H : Flag.{u} U n ↦ H.chain i) hfg

include hfg in
theorem restrictedOrder_mem (v : Fin (flankLen F + 1)) :
    orderMap f.map (flankEmbedding F v) ∈ selectedVertices G := by
  apply (mem_selectedVertices G _).mpr
  rw [← flagged_arrow_image F G f hfg (Fin.last n)]
  refine ⟨ULift.up (flankEmbedding F v), ?_, ?_⟩
  · exact (mem_selectedVertices F _).mp
      (Finset.orderEmbOfFin_mem (selectedVertices F) (flank_card F) v)
  · apply ULift.ext
    rfl

/-- Restriction followed by the actual finite-order inverse, retaining collapsed images. -/
def restrictedOrder : Fin (flankLen F + 1) →o Fin (flankLen G + 1) where
  toFun v := ((selectedVertices G).orderIsoOfFin (flank_card G)).symm
    ⟨orderMap f.map (flankEmbedding F v), restrictedOrder_mem F G f hfg v⟩
  monotone' _ _ hvw :=
    ((selectedVertices G).orderIsoOfFin (flank_card G)).symm.monotone
      ((orderMap f.map).monotone ((flankEmbedding F).monotone hvw))

theorem restrictedOrder_square (v : Fin (flankLen F + 1)) :
    flankEmbedding G (restrictedOrder F G f hfg v) =
      orderMap f.map (flankEmbedding F v) :=
  congrArg Subtype.val (((selectedVertices G).orderIsoOfFin (flank_card G)).apply_symm_apply
    ⟨orderMap f.map (flankEmbedding F v), restrictedOrder_mem F G f hfg v⟩)

theorem restrictedOrder_first : restrictedOrder F G f hfg 0 = 0 := by
  apply (flankEmbedding G).injective
  rw [restrictedOrder_square]
  simp only [flankEmbedding_first, orderMap_first]

theorem restrictedOrder_last :
    restrictedOrder F G f hfg (Fin.last (flankLen F)) = Fin.last (flankLen G) := by
  apply (flankEmbedding G).injective
  rw [restrictedOrder_square]
  simp only [flankEmbedding_last, orderMap_last]

end

end DaggerOriginalFlagFlankification
