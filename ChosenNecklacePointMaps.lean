import ChosenNecklaceWedgeMaps

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

def zeroSimplex (n : ℕ) : (Δ[0] : SSet.{u}).obj (op ⦋n⦌) :=
  SSet.stdSimplex.objMk (OrderHom.const _ 0)

theorem zeroSimplex_unique {n : ℕ} (x : (Δ[0] : SSet.{u}).obj (op ⦋n⦌)) :
    x = zeroSimplex n := by
  apply SSet.stdSimplex.ext
  intro i
  apply Fin.ext
  have h := (x i).isLt
  change (x i).val = 0
  omega

theorem pointAt_inclusion (T : NecklaceCode) (v : Vertices.{u} T) :
    pointAt T v ≫ T.inclusion =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋T.len⦌ v.down) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, pointAt_vertex, SSet.stdSimplex.yonedaEquiv_map]
  apply SSet.stdSimplex.obj₀Equiv.injective
  exact T.inclusion_vertex v

theorem pointAt_inclusion_apply (T : NecklaceCode) (v : Vertices.{u} T) {n : ℕ}
    (x : (Δ[0] : SSet.{u}).obj (op ⦋n⦌)) (i : Fin (n + 1)) :
    T.inclusion.app _ ((pointAt T v).app _ x) i = v.down := by
  have h := congrFun (NatTrans.congr_app (pointAt_inclusion T v) (op ⦋n⦌)) x
  exact congrArg (fun y : (Δ[T.len] : SSet.{u}).obj (op ⦋n⦌) ↦ y i) h

theorem necklace_simplex_ext (T : NecklaceCode) {n : ℕ}
    {x y : (toSSet.{u} T).obj (op ⦋n⦌)}
    (h : ∀ i : Fin (n + 1), T.inclusion.app _ x i = T.inclusion.app _ y i) : x = y := by
  apply (T.complexIso.app (op ⦋n⦌)).toEquiv.injective
  apply Subtype.ext
  exact SSet.stdSimplex.ext _ _ h

theorem constant_simplex_eq (T : NecklaceCode) (v : Vertices.{u} T) {n : ℕ}
    (x : (toSSet.{u} T).obj (op ⦋n⦌)) (hx : ∀ i, T.inclusion.app _ x i = v.down) :
    x = (pointAt T v).app _ (zeroSimplex n) := by
  apply necklace_simplex_ext T
  intro i
  rw [pointAt_inclusion_apply, hx i]

end

end DaggerChosenRigidificationNecklace.NecklaceCode
