import NativeWalkingKanTensor
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-! A native groupoid nerve is Kan, reusing the actual ordinary-core Kan theorem. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalQuasicategoryInverseEdgeRepresentatives
open DaggerNativeKanSourceOriginalCoreFactor
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeGroupoidNerveKan
noncomputable section

theorem nerve_ho_all_iso (G : Type u) [Groupoid.{u} G]
    {x y : SSet.hoFunctor.obj (nerve G)} (a : x ⟶ y) : IsIso a := by
  let e := asIso (nerveAdjunction.counit.app (Cat.of G))
  let f := e.hom.toFunctor
  let g := e.inv.toFunctor
  have hfg : f ⋙ g = 𝟭 (SSet.hoFunctor.obj (nerve G)) :=
    congrArg (fun t ↦ t.toFunctor) e.hom_inv_id
  have : IsIso (f.map a) := inferInstance
  have h : IsIso ((f ⋙ g).map a) := by
    change IsIso (g.map (f.map a))
    infer_instance
  rwa [hfg, Functor.id_map] at h

theorem nerve_edge_invertible (G : Type u) [Groupoid.{u} G] (q : (nerve G) _⦋1⦌) :
    edgeIsInvertible (nerve G) q := by
  let e := SSet.Edge.mk' q
  exact (edgeIsInvertible_iff_original_homMk_isIso (nerve G) e).mpr
    (nerve_ho_all_iso G (SSet.Truncated.HomotopyCategory.homMk e))

theorem nerve_core_eq_top (G : Type u) [Groupoid.{u} G] :
    ordinaryCoreCandidate (nerve G) = ⊤ := by
  apply top_unique
  intro n s _
  apply (mem_ordinaryCoreCandidate_iff_edges_iso (nerve G) n s).mpr
  intro α
  exact nerve_edge_invertible G _

theorem nerve_kan (G : Type u) [Groupoid.{u} G] : (nerve G).KanComplex := by
  have : (ordinaryCoreCandidate (nerve G) : SSet.{u}).KanComplex :=
    native_quasi_core_kan (nerve G)
  let e : (ordinaryCoreCandidate (nerve G) : SSet.{u}) ≅ nerve G :=
    SSet.Subcomplex.isoOfEq (nerve_core_eq_top G) ≪≫ SSet.Subcomplex.topIso _
  have : Fibration e.inv := inferInstance
  exact isFibrant_of_fibration e.inv

end
end DaggerNativeGroupoidNerveKan
