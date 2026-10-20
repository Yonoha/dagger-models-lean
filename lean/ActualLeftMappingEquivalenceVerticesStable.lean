import ActualCoreMappingFullVertexIso
import NativeEdgeStableFullVertexFibration
import OriginalComposableTriangleIsomorphisms

/-! The ORIGINAL equivalence vertices are stable along every edge of the ORIGINAL left mapping.
The actual suffix edge is constant, so native iso cancellation compares the two cross edges.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalOrdinaryKanCoreEdgeMaximality DaggerOriginalOrdinaryKanCoreInnerHorns
open DaggerOriginalOrdinalJoinLeft DaggerActualQuasicategoryMappingFibres
open DaggerActualMappingCoreVertexCharacterization DaggerNativeKanSourceOriginalCoreFactor
open DaggerNativeEdgeStableFullVertexFibration
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualLeftMappingEquivalenceVerticesStable
noncomputable section

theorem vertex_first {Z : SSet.{u}} (σ : (Δ[1] : SSet.{u}) ⟶ Z) :
    σ.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm 0) =
      Z.map (SimplexCategory.δ (1 : Fin 2)).op (SSet.yonedaEquiv σ) := by
  have he : SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2) =
      SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ (1 : Fin 2)) := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    rfl
  rw [he]
  exact simplex_app_operator σ (SimplexCategory.δ (1 : Fin 2))

theorem vertex_last {Z : SSet.{u}} (σ : (Δ[1] : SSet.{u}) ⟶ Z) :
    σ.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm 1) =
      Z.map (SimplexCategory.δ (0 : Fin 2)).op (SSet.yonedaEquiv σ) := by
  have he : SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2) =
      SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ (0 : Fin 2)) := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    rfl
  rw [he]
  exact simplex_app_operator σ (SimplexCategory.δ (0 : Fin 2))

theorem join_first : (ordinalJoinLeft ⦋0⦌).map (SimplexCategory.δ (1 : Fin 2)) =
    pairOperator (0 : Fin 3) 1 (by decide) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  fin_cases i <;> rfl

theorem join_last : (ordinalJoinLeft ⦋0⦌).map (SimplexCategory.δ (0 : Fin 2)) =
    pairOperator (0 : Fin 3) 2 (by decide) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  fin_cases i <;> rfl

theorem suffix_pair : AugmentedSimplexCategory.inr' ⦋0⦌ ⦋1⦌ =
    pairOperator (1 : Fin 3) 2 (by decide) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  fin_cases i <;> rfl

theorem unit_edge_iso_iff (X : SSet.{u}) (s : X.obj (op ⦋2⦌))
    (i j : Fin 3) (hij : i ≤ j) :
    edgeIsInvertible X (X.map (pairOperator i j hij).op s) ↔
      IsIso (((homotopyCategoryUnit X).app (op ⦋2⦌) s).map (homOfLE hij)) := by
  have hn := congrFun ((homotopyCategoryUnit X).naturality (pairOperator i j hij).op) s
  have hh := congrArg (fun t : (nerve (SSet.hoFunctor.obj X)).obj (op ⦋1⦌) ↦
    IsIso t.hom) hn
  exact hh.to_iff

theorem equivalenceVertices_edgeStable (X : SSet.{u}) [X.Quasicategory]
    (a b : X.obj (op ⦋0⦌)) : EdgeStable (equivalenceVertices X a b) := by
  intro σ
  let s := SSet.yonedaEquiv σ
  let F := (homotopyCategoryUnit X).app (op ⦋2⦌) s.val.val
  have h0 : σ.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm 0) ∈
      equivalenceVertices X a b ↔ IsIso (F.map (homOfLE (show (0 : Fin 3) ≤ 1 by decide))) := by
    rw [vertex_first]
    change edgeIsInvertible X (X.map
      ((ordinalJoinLeft ⦋0⦌).map (SimplexCategory.δ (1 : Fin 2))).op s.val.val) ↔ _
    rw [join_first]
    exact unit_edge_iso_iff X s.val.val 0 1 (by decide)
  have h1 : σ.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm 1) ∈
      equivalenceVertices X a b ↔ IsIso (F.map (homOfLE (show (0 : Fin 3) ≤ 2 by decide))) := by
    rw [vertex_last]
    change edgeIsInvertible X (X.map
      ((ordinalJoinLeft ⦋0⦌).map (SimplexCategory.δ (0 : Fin 2))).op s.val.val) ↔ _
    rw [join_last]
    exact unit_edge_iso_iff X s.val.val 0 2 (by decide)
  have : (leftMapping X a b).KanComplex := leftMapping_kan X a b
  have hm : X.map (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋1⦌).op s.val.val ∈
      (ordinaryCoreCandidate X).obj (op ⦋1⦌) := by
    rw [suffix_eq_const]
    exact kan_map_mem_core (SSet.const b : leftMapping X a b ⟶ X) _ s
  have hi := (mem_ordinaryCoreCandidate_one_iff X _).mp hm
  rw [suffix_pair] at hi
  have : IsIso (F.map (homOfLE (show (1 : Fin 3) ≤ 2 by decide))) :=
    (unit_edge_iso_iff X s.val.val 1 2 (by decide)).mp hi
  have he : F.map (homOfLE (show (0 : Fin 3) ≤ 1 by decide)) ≫
      F.map (homOfLE (show (1 : Fin 3) ≤ 2 by decide)) =
        F.map (homOfLE (show (0 : Fin 3) ≤ 2 by decide)) := by
    rw [← F.map_comp]
    congr 1
  rw [h0, h1]
  constructor
  · intro h
    have := h
    rw [← he]
    infer_instance
  · intro h
    have := h
    exact IsIso.of_isIso_fac_right he

theorem selected_inclusion_fibration (X : SSet.{u}) [X.Quasicategory]
    (a b : X.obj (op ⦋0⦌)) :
    HomotopicalAlgebra.Fibration
      (DaggerOriginalFullVertexSubcomplex.fullVertexSubcomplex
        (leftMapping X a b) (equivalenceVertices X a b)).ι :=
  inclusion_fibration _ (equivalenceVertices_edgeStable X a b)

end
end DaggerActualLeftMappingEquivalenceVerticesStable
