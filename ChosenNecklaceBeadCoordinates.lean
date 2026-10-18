import ChosenNecklaceBeadMaps
import ChosenNecklaceIntersections

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode.Bead

noncomputable section

variable {T : NecklaceCode} (b : T.Bead)

def embedding : Fin (b.length + 1) ↪o Fin (T.len + 1) :=
  b.interval.orderEmbOfFin b.card_interval

theorem embedding_zero : b.embedding 0 = b.left := by
  have h := Finset.orderEmbOfFin_zero b.card_interval (Nat.succ_pos b.length)
  have hs : b.embedding 0 = b.interval.min' ⟨b.left, b.left_mem_interval⟩ := by
    simpa [embedding] using h
  rw [hs]
  apply le_antisymm
  · exact b.interval.min'_le b.left b.left_mem_interval
  · exact (Finset.mem_Icc.mp (b.interval.min'_mem _)).1

theorem embedding_last : b.embedding (Fin.last b.length) = b.right := by
  have h := Finset.orderEmbOfFin_last b.card_interval (Nat.succ_pos b.length)
  have hs : b.embedding (Fin.last b.length) =
      b.interval.max' ⟨b.right, b.right_mem_interval⟩ := by
    simpa [embedding] using h
  rw [hs]
  apply le_antisymm
  · exact (Finset.mem_Icc.mp (b.interval.max'_mem _)).2
  · exact b.interval.le_max' b.right b.right_mem_interval

theorem faceIso_hom_apply {n : ℕ} (x : (Δ[b.length] : SSet.{u}).obj (op ⦋n⦌))
    (i : Fin (n + 1)) : (b.faceIso.hom.app _ x).val i = b.embedding (x i) := rfl

theorem beadSimplex_inclusion_apply {n : ℕ}
    (x : (Δ[b.length] : SSet.{u}).obj (op ⦋n⦌)) (i : Fin (n + 1)) :
    T.inclusion.app _ (T.beadSimplex b |>.app _ x) i = b.embedding (x i) := by
  have h := congrFun (NatTrans.congr_app (T.beadSimplex_inclusion b) (op ⦋n⦌)) x
  exact congrArg (fun y : (Δ[T.len] : SSet.{u}).obj (op ⦋n⦌) ↦ y i) h

theorem beadSimplex_vertex (v : Fin (b.length + 1)) :
    T.verticesEquiv (T.beadSimplex b |>.app _ (SSet.stdSimplex.obj₀Equiv.symm v)) =
      ULift.up (b.embedding v) := by
  apply ULift.ext
  rw [T.verticesEquiv_down]
  exact b.beadSimplex_inclusion_apply _ 0

theorem beadSimplex_first :
    T.verticesEquiv (T.beadSimplex b |>.app _ (SSet.stdSimplex.obj₀Equiv.symm 0)) =
      ULift.up b.left := by rw [b.beadSimplex_vertex, b.embedding_zero]

theorem beadSimplex_last :
    T.verticesEquiv (T.beadSimplex b |>.app _
      (SSet.stdSimplex.obj₀Equiv.symm (Fin.last b.length))) = ULift.up b.right := by
  rw [b.beadSimplex_vertex, b.embedding_last]

end

end DaggerChosenRigidificationNecklace.NecklaceCode.Bead
