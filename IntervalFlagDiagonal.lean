import IntervalFlagContraction

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerOriginalIntervalFlagContraction

noncomputable section

open DaggerChosenRigidificationNecklace hiding E
open NecklaceCode DaggerIntervalNecklaceCompletion

def edgeCollapseCode : Hom.{u} (single 1) NecklaceCode.point where
  map := (singleIso 1).hom ≫
    SSet.stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0)
  first := by
    apply (SSet.stdSimplex.obj₀Equiv (n := 0)).injective
    apply Fin.ext
    omega
  last := by
    apply (SSet.stdSimplex.obj₀Equiv (n := 0)).injective
    apply Fin.ext
    omega

/-- The actual diagonal edge, with Unit Hom, is the degeneracy of the supplied vertex. -/
theorem diagonal_edge_degenerate (a : (E.{u}).obj (op ⦋0⦌)) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0) ≫
      SSet.yonedaEquiv.symm a = endpointEdge a a := by
  apply DaggerIntervalNecklaceCompletion.hom_ext_vertices
  intro v
  obtain ⟨i, rfl⟩ := SSet.stdSimplex.obj₀Equiv.symm.surjective v
  fin_cases i
  · change (SSet.yonedaEquiv.symm a).app _ _ =
      (endpointEdge a a).app _ (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))
    rw [endpointEdge_first]
    exact pointAt_vertex_apply a _
  · change (SSet.yonedaEquiv.symm a).app _ _ =
      (endpointEdge a a).app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last 1))
    rw [endpointEdge_last]
    exact pointAt_vertex_apply a _

def edgeCollapseOver (a : (E.{u}).obj (op ⦋0⦌)) :
    NecklacesOver.Hom (edgeObject a a) (NecklacesOver.point a) where
  hom := edgeCollapseCode
  w := by
    change ((singleIso 1).hom ≫ _) ≫ SSet.yonedaEquiv.symm a =
      (singleIso 1).hom ≫ endpointEdge a a
    rw [Category.assoc, diagonal_edge_degenerate]

theorem collapse_bottomFlag (n : ℕ) :
    NecklaceCode.Flag.map edgeCollapseCode.{u} (bottomFlag 1 n) = NecklaceCode.Flag.pointFlag n :=
  NecklaceCode.Flag.pointFlag_unique _

theorem center_diagonal_identity (a : (E.{u}).obj (op ⦋0⦌))
    (q : SimplexCategoryᵒᵖ) : centerAt (a := a) (b := a) q = flagIdApp a q :=
  Quot.sound ⟨edgeCollapseOver a, (collapse_bottomFlag q.unop.len).symm⟩

theorem center_diagonal (a : (E.{u}).obj (op ⦋0⦌)) :
    center (a := a) (b := a) = (flagIdentity (E.{u}) a).app (op ⦋0⦌) PUnit.unit :=
  center_diagonal_identity a (op ⦋0⦌)

end

end DaggerOriginalIntervalFlagContraction
