import OriginalQuasicategoryPathEdgeRepresentatives

/-!
# Exact original homotopy-category unit on vertices and edges

The original unit is transported from the composite coskeleton and truncated
nerve adjunctions. Its factorization and the coskeleton triangle identity give
its exact two-truncation, so the edge formula uses the original path quotient.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial SimplicialObject.Truncated SimplexCategory.Truncated
open DaggerOriginalOrdinaryKanCoreSubcomplex

universe u

namespace DaggerOriginalHomotopyCategoryUnitEdges

noncomputable section

/-- Factor the original unit through its actual coskeleton comparison. -/
theorem original_unit_cosk_factor (X : SSet.{u}) :
    homotopyCategoryUnit X ≫ (SSet.coskAdj 2).unit.app (nerve (SSet.hoFunctor.obj X)) =
      (SSet.coskAdj 2).unit.app X ≫ (SSet.Truncated.cosk 2).map
        (SSet.Truncated.nerve₂Adj.unit.app ((SSet.truncation 2).obj X)) := by
  rw [homotopyCategoryUnit, ← Adjunction.homEquiv_id]
  simp only [nerveAdjunction, Adjunction.ofNatIsoRight,
    Adjunction.mkOfHomEquiv_homEquiv, Equiv.trans_apply,
    Adjunction.equivHomsetRightOfNatIso_apply, Adjunction.homEquiv_id]
  change (((SSet.coskAdj 2).comp SSet.Truncated.nerve₂Adj).unit.app X ≫
    Nerve.cosk₂Iso.inv.app (SSet.hoFunctor.obj X)) ≫
      (SSet.coskAdj 2).unit.app (nerve (SSet.hoFunctor.obj X)) = _
  change (((SSet.coskAdj 2).comp SSet.Truncated.nerve₂Adj).unit.app X ≫
    Nerve.cosk₂Iso.inv.app (SSet.hoFunctor.obj X)) ≫
      Nerve.cosk₂Iso.hom.app (SSet.hoFunctor.obj X) = _
  rw [Category.assoc, Iso.inv_hom_id_app]
  exact (Category.comp_id _).trans ((SSet.coskAdj 2).comp_unit_app
    SSet.Truncated.nerve₂Adj X)

/-- The exact two-truncation of the original full unit is the original truncated unit. -/
theorem original_unit_truncation (X : SSet.{u}) :
    (SSet.truncation 2).map (homotopyCategoryUnit X) =
      SSet.Truncated.nerve₂Adj.unit.app ((SSet.truncation 2).obj X) := by
  let t := SSet.Truncated.nerve₂Adj.unit.app ((SSet.truncation 2).obj X)
  let Y := nerve (SSet.hoFunctor.obj X)
  have hf := congrArg (fun f : X ⟶ (SSet.Truncated.cosk 2).obj
    ((SSet.truncation 2).obj Y) ↦ (SSet.truncation 2).map f) (original_unit_cosk_factor X)
  simp only [Functor.map_comp] at hf
  have hnat := (SSet.coskAdj 2).counit.naturality t
  change (SSet.truncation 2).map ((SSet.Truncated.cosk 2).map t) ≫
    (SSet.coskAdj 2).counit.app ((SSet.truncation 2).obj Y) =
      (SSet.coskAdj 2).counit.app ((SSet.truncation 2).obj X) ≫ t at hnat
  calc
    (SSet.truncation 2).map (homotopyCategoryUnit X) =
        (SSet.truncation 2).map (homotopyCategoryUnit X) ≫
          ((SSet.truncation 2).map ((SSet.coskAdj 2).unit.app Y) ≫
            (SSet.coskAdj 2).counit.app ((SSet.truncation 2).obj Y)) := by
      rw [(SSet.coskAdj 2).left_triangle_components, Category.comp_id]
    _ = ((SSet.truncation 2).map (homotopyCategoryUnit X) ≫
        (SSet.truncation 2).map ((SSet.coskAdj 2).unit.app Y)) ≫
          (SSet.coskAdj 2).counit.app ((SSet.truncation 2).obj Y) := by
      rw [Category.assoc]
    _ = ((SSet.truncation 2).map ((SSet.coskAdj 2).unit.app X) ≫
        (SSet.truncation 2).map ((SSet.Truncated.cosk 2).map t)) ≫
          (SSet.coskAdj 2).counit.app ((SSet.truncation 2).obj Y) := by
      rw [hf]
    _ = (SSet.truncation 2).map ((SSet.coskAdj 2).unit.app X) ≫
        ((SSet.coskAdj 2).counit.app ((SSet.truncation 2).obj X) ≫ t) := by
      rw [Category.assoc, hnat]
    _ = t := by
      rw [← Category.assoc, (SSet.coskAdj 2).left_triangle_components]
      exact Category.id_comp t

/-- The actual original unit sends a vertex to that same vertex of the path quotient. -/
theorem original_unit_app_vertex (X : SSet.{u}) (x : X.obj (op ⦋0⦌)) :
    (homotopyCategoryUnit X).app (op ⦋0⦌) x =
      nerveEquiv.symm (SSet.Truncated.HomotopyCategory.mk x) := by
  have h := congrArg
    (fun f : (SSet.truncation 2).obj X ⟶ (SSet.truncation 2).obj
      (nerve (SSet.hoFunctor.obj X)) ↦ f.app (op ⦋0⦌₂) x) (original_unit_truncation X)
  exact h

/-- The actual original unit sends an edge to its exact original path-quotient arrow. -/
theorem original_unit_app_edge (X : SSet.{u}) {x y : X.obj (op ⦋0⦌)}
    (e : SSet.Edge x y) :
    (homotopyCategoryUnit X).app (op ⦋1⦌) e.edge =
      ComposableArrows.mk₁ (SSet.Truncated.HomotopyCategory.homMk e) := by
  have h := congrArg
    (fun f : (SSet.truncation 2).obj X ⟶ (SSet.truncation 2).obj
      (nerve (SSet.hoFunctor.obj X)) ↦ f.app (op ⦋1⦌₂) e.edge) (original_unit_truncation X)
  change (homotopyCategoryUnit X).app (op ⦋1⦌) e.edge =
    (SSet.Truncated.HomotopyCategory.homToNerveMk
      (𝟭 ((SSet.truncation 2).obj X).HomotopyCategory)).app (op ⦋1⦌₂) e.edge at h
  exact h.trans (SSet.Truncated.HomotopyCategory.homToNerveMk_app_edge _ e)

end

end DaggerOriginalHomotopyCategoryUnitEdges
