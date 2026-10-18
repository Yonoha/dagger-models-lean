import ChosenNecklaceCoverage

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T : NecklaceCode)

theorem complex_eq_top_of_zero (h : T.len = 0) : T.complex = ⊤ := by
  apply le_antisymm le_top
  intro q x _
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ n
  apply (T.mem_complex_iff x).mpr
  left
  intro i
  apply Fin.ext
  have hi := (x i).isLt
  have hz : (0 : Fin (T.len + 1)).val = 0 := rfl
  omega

/-- The exceptional point code is compared with its actual full union, without changing it. -/
def complexIso : T.toSSet ≅ T.complex.toSSet :=
  if h : T.len = 0 then
    eqToIso (by simp only [toSSet, if_pos h]) ≪≫
      eqToIso (congrArg (fun n ↦ (Δ[n] : SSet.{u})) h.symm) ≪≫
      (SSet.Subcomplex.topIso (Δ[T.len])).symm ≪≫
      SSet.Subcomplex.eqToIso (T.complex_eq_top_of_zero h).symm
  else eqToIso (by simp only [toSSet, if_neg h])

def inclusion : T.toSSet ⟶ (Δ[T.len] : SSet.{u}) :=
  T.complexIso.hom ≫ T.complex.ι

instance : Mono T.inclusion := by
  dsimp [inclusion]
  infer_instance

/-- Every original necklace vertex, including every joint, is retained in the union. -/
def complexVerticesEquiv : (complex.{u} T).toSSet.obj (op ⦋0⦌) ≃ Fin (T.len + 1) where
  toFun x := SSet.stdSimplex.obj₀Equiv x.val
  invFun v := ⟨SSet.stdSimplex.obj₀Equiv.symm v, T.vertex_mem_complex v _ (by
    intro i
    have hi : i = 0 := Fin.ext (by have hj := i.isLt; omega)
    subst i
    rfl)⟩
  left_inv x := by
    apply Subtype.ext
    exact SSet.stdSimplex.obj₀Equiv.symm_apply_apply x.val
  right_inv v := SSet.stdSimplex.obj₀Equiv.apply_symm_apply v

def verticesEquiv : (toSSet.{u} T).obj (op ⦋0⦌) ≃ Vertices.{u} T :=
  (T.complexIso.app (op ⦋0⦌)).toEquiv.trans
    (T.complexVerticesEquiv.trans Equiv.ulift.symm)

theorem verticesEquiv_down (x : T.toSSet.obj (op ⦋0⦌)) :
    (T.verticesEquiv x).down = SSet.stdSimplex.obj₀Equiv (T.inclusion.app _ x) := rfl

theorem inclusion_vertex (v : Vertices.{u} T) :
    SSet.stdSimplex.obj₀Equiv (T.inclusion.app _ (T.verticesEquiv.symm v)) = v.down := by
  rw [← T.verticesEquiv_down, T.verticesEquiv.apply_symm_apply]

theorem beadι_inclusion (b : T.Bead) :
    T.beadι b ≫ T.inclusion = b.face.ι := by
  have hn := b.len_ne_zero
  simp [beadι, inclusion, complexIso, toSSet, hn]

theorem beadSimplex_inclusion (b : T.Bead) :
    T.beadSimplex b ≫ T.inclusion = b.faceIso.hom ≫ b.face.ι := by
  simp [beadSimplex, Category.assoc, T.beadι_inclusion]

end

end DaggerChosenRigidificationNecklace.NecklaceCode
