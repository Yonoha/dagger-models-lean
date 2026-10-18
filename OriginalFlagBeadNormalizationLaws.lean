import OriginalFlagBeadNormalization
import ChosenNecklaceSingleBead
import ChosenNecklacesOverWedge
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

theorem simplex_epi_first {m n : ℕ} (s : ⦋m⦌ ⟶ ⦋n⦌) [Epi s] :
    s.toOrderHom 0 = 0 := by
  obtain ⟨v, hv⟩ := ((SimplexCategory.epi_iff_surjective (f := s)).mp inferInstance) 0
  apply le_antisymm
  · rw [← hv]
    exact s.toOrderHom.monotone (Fin.zero_le v)
  · exact Fin.zero_le _

theorem simplex_epi_last {m n : ℕ} (s : ⦋m⦌ ⟶ ⦋n⦌) [Epi s] :
    s.toOrderHom (Fin.last m) = Fin.last n := by
  obtain ⟨v, hv⟩ :=
    ((SimplexCategory.epi_iff_surjective (f := s)).mp inferInstance) (Fin.last n)
  apply le_antisymm
  · exact Fin.le_last _
  · rw [← hv]
    exact s.toOrderHom.monotone (Fin.le_last v)

theorem stdSimplex_map_vertex {m n : ℕ} (s : ⦋m⦌ ⟶ ⦋n⦌)
    (v : Fin (m + 1)) :
    (SSet.stdSimplex.map s).app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm v) =
      SSet.stdSimplex.obj₀Equiv.symm (s.toOrderHom v) := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  rfl

/-- Literal original vertex image; repeated vertices do not identify code endpoints. -/
def vertexImage (P : NecklacesOver X a b) (v : Fin (P.code.len + 1)) :
    X.obj (op ⦋0⦌) := P.map.app _ (P.code.verticesEquiv.symm (ULift.up v))

theorem vertexImage_first (P : NecklacesOver X a b) : vertexImage P 0 = a := P.first

theorem vertexImage_last (P : NecklacesOver X a b) :
    vertexImage P (Fin.last P.code.len) = b := P.last

theorem beadNormalization_vertex (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) (v : Fin (c.length + 1)) :
    (SSet.yonedaEquiv.symm d.simplex.val).app (op ⦋0⦌)
        (SSet.stdSimplex.obj₀Equiv.symm (d.operator.toOrderHom v)) =
      vertexImage P (c.embedding v) := by
  have h := congrFun
    (NatTrans.congr_app (beadNormalization_triangle P c d) (op ⦋0⦌))
    (SSet.stdSimplex.obj₀Equiv.symm v)
  change (SSet.yonedaEquiv.symm d.simplex.val).app (op ⦋0⦌)
      ((SSet.stdSimplex.map d.operator).app (op ⦋0⦌)
        (SSet.stdSimplex.obj₀Equiv.symm v)) =
    P.map.app _ (P.code.beadSimplex c |>.app _ (SSet.stdSimplex.obj₀Equiv.symm v)) at h
  rw [stdSimplex_map_vertex] at h
  rw [← P.code.verticesEquiv.symm_apply_apply
    (P.code.beadSimplex c |>.app _ (SSet.stdSimplex.obj₀Equiv.symm v)),
    c.beadSimplex_vertex] at h
  exact h

theorem beadNormalization_first (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) :
    (SSet.yonedaEquiv.symm d.simplex.val).app _ (SSet.stdSimplex.obj₀Equiv.symm 0) =
      vertexImage P c.left := by
  letI := d.epi
  simpa only [simplex_epi_first, c.embedding_zero] using
    beadNormalization_vertex P c d 0

theorem beadNormalization_last (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) :
    (SSet.yonedaEquiv.symm d.simplex.val).app _
        (SSet.stdSimplex.obj₀Equiv.symm (Fin.last d.dim)) =
      vertexImage P c.right := by
  letI := d.epi
  simpa only [simplex_epi_last, c.embedding_last] using
    beadNormalization_vertex P c d (Fin.last c.length)

/-- All the chosen decomposition data agree; no Mono condition on the map into X is used. -/
theorem beadNormalization_unique (P : NecklacesOver X a b) (c : P.code.Bead)
    (d e : NondegenerateBeadData P c) : d = e := by
  cases d with
  | mk md fd ed yd hd =>
    cases e with
    | mk me fe ee ye he =>
      letI := ed
      letI := ee
      have hm := X.unique_nonDegenerate_dim (beadElement P c) fd yd hd fe ye he
      cases hm
      have hy := X.unique_nonDegenerate_simplex (beadElement P c) fd yd hd fe ye he
      have hf := X.unique_nonDegenerate_map (beadElement P c) fd yd hd fe ye he
      cases hy
      cases hf
      rfl

/-- Equality is transported through the actual dimension equality, not a quotient class. -/
theorem beadNormalization_simplex_unique (P : NecklacesOver X a b) (c : P.code.Bead)
    (d e : NondegenerateBeadData P c) :
    (beadNormalization_dim_unique P c d e) ▸ d.simplex = e.simplex := by
  have h := beadNormalization_unique P c d e
  cases h
  rfl

theorem beadNormalization_operator_unique (P : NecklacesOver X a b) (c : P.code.Bead)
    (d e : NondegenerateBeadData P c) :
    (beadNormalization_dim_unique P c d e) ▸ d.operator = e.operator := by
  have h := beadNormalization_unique P c d e
  cases h
  rfl

theorem beadNormalization_zero_endpoints (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) (h : d.dim = 0) :
    vertexImage P c.left = vertexImage P c.right := by
  have hf := beadNormalization_first P c d
  have hl := beadNormalization_last P c d
  rcases d with ⟨m, s, hs, y, hy⟩
  cases h
  exact hf.symm.trans hl

end

end DaggerOriginalFlagFlankification
