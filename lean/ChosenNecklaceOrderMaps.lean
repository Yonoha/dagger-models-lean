import ChosenNecklaceBeadMaps

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T : NecklaceCode)

theorem adjacent_edge_mem (i : Fin T.len) :
    SSet.stdSimplex.edge.{u} T.len i.castSucc i.succ (Fin.castSucc_le_succ i) ∈
      T.complex.obj (op ⦋1⦌) := by
  obtain ⟨b, hl, hr⟩ := T.exists_bead_at i.succ (by simp)
  have hleft : b.left ≤ i.castSucc := by
    simp only [Fin.lt_def, Fin.val_succ] at hl
    change b.left.val ≤ i.val
    omega
  apply (T.mem_complex_iff _).mpr
  right
  refine ⟨b, ?_⟩
  intro k
  fin_cases k
  · exact Finset.mem_Icc.mpr ⟨hleft, (Fin.castSucc_le_succ i).trans hr⟩
  · exact Finset.mem_Icc.mpr ⟨hl.le, hr⟩

def adjacentEdge (i : Fin T.len) : T.toSSet.obj (op ⦋1⦌) :=
  T.complexIso.inv.app _ ⟨_, T.adjacent_edge_mem i⟩

theorem inclusion_adjacentEdge (i : Fin T.len) :
    T.inclusion.app _ (T.adjacentEdge i) =
      SSet.stdSimplex.edge.{u} T.len i.castSucc i.succ (Fin.castSucc_le_succ i) := by
  have h := congrFun (NatTrans.congr_app T.complexIso.inv_hom_id (op ⦋1⦌))
    ⟨_, T.adjacent_edge_mem i⟩
  exact congrArg Subtype.val h

theorem adjacentEdge_vertex (i : Fin T.len) (k : Fin 2) :
    T.verticesEquiv (T.toSSet.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ k).op
      (T.adjacentEdge i)) =
        ULift.up
          (SSet.stdSimplex.edge.{u} T.len i.castSucc i.succ (Fin.castSucc_le_succ i) k) := by
  apply ULift.ext
  rw [T.verticesEquiv_down, ← stdSimplex_vertex_naturality, T.inclusion_adjacentEdge]
  rfl

variable {T} {U : NecklaceCode}

/-- The vertex function of every actual necklace map is monotone, even if vertices collapse. -/
theorem mapVertices_monotone (f : toSSet.{u} T ⟶ toSSet.{u} U) :
    Monotone (fun v : Fin (T.len + 1) ↦ (mapVertices f (ULift.up v)).down) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  let y := (f ≫ U.inclusion).app _ (T.adjacentEdge i)
  have hy (k : Fin 2) :
      (mapVertices f
        (ULift.up
          (SSet.stdSimplex.edge.{u} T.len i.castSucc i.succ (Fin.castSucc_le_succ i) k))).down =
          y k := by
    rw [← T.adjacentEdge_vertex i k]
    dsimp [mapVertices]
    rw [T.verticesEquiv.symm_apply_apply, U.verticesEquiv_down]
    exact (stdSimplex_vertex_naturality (f ≫ U.inclusion) (T.adjacentEdge i) k).symm
  have hm := SSet.stdSimplex.monotone_apply y (show (0 : Fin 2) ≤ 1 by decide)
  change y 0 ≤ y 1 at hm
  rw [← hy 0, ← hy 1] at hm
  exact hm

def orderMap (f : toSSet.{u} T ⟶ toSSet.{u} U) : Fin (T.len + 1) →o Fin (U.len + 1) where
  toFun v := (mapVertices f (ULift.up v)).down
  monotone' := mapVertices_monotone f

end

end DaggerChosenRigidificationNecklace.NecklaceCode
