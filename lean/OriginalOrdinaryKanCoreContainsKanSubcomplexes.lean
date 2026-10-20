import OriginalOrdinaryKanCoreKanInverseEdges

/-!
# Every Kan subcomplex lies in the actual core candidate

Outer 2-horn inverse triangles prove that each Kan edge has an invertible
image under the actual homotopy-category unit. Naturality of that same unit
then proves containment for every Kan subcomplex in arbitrary universe.
The candidate's own Kan condition is still a separate theorem.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalOrdinaryKanCoreEdgeMaximality
open DaggerOriginalOrdinaryKanCoreKanInverseEdges

universe u

namespace DaggerOriginalOrdinaryKanCoreContainsKanSubcomplexes

noncomputable section

/-- A mapped Kan edge is invertible in the native homotopy category. -/
theorem kan_unit_mapped_edge_isIso {X : SSet.{u}} [X.KanComplex]
    {x y : X.obj (op ⦋0⦌)} (e : SSet.Edge x y) :
    IsIso (nerve.homEquiv (e.map (homotopyCategoryUnit X))) := by
  obtain ⟨r, ⟨hr⟩⟩ := kan_right_inverse_edge e
  obtain ⟨s, ⟨hs⟩⟩ := kan_right_inverse_edge r
  let f := nerve.homEquiv (e.map (homotopyCategoryUnit X))
  let g := nerve.homEquiv (r.map (homotopyCategoryUnit X))
  let k := nerve.homEquiv (s.map (homotopyCategoryUnit X))
  have hfg : f ≫ g = 𝟙 _ := by
    simpa only [SSet.Edge.map_id, nerve.homEquiv_id] using
      nerve.homEquiv_comp (hr.map (homotopyCategoryUnit X))
  have hgk : g ≫ k = 𝟙 _ := by
    simpa only [SSet.Edge.map_id, nerve.homEquiv_id] using
      nerve.homEquiv_comp (hs.map (homotopyCategoryUnit X))
  have hfk : f = k := by
    calc
      f = f ≫ 𝟙 _ := (Category.comp_id f).symm
      _ = f ≫ (g ≫ k) := by rw [hgk]
      _ = (f ≫ g) ≫ k := (Category.assoc f g k).symm
      _ = k := by rw [hfg, Category.id_comp]
  refine ⟨⟨g, hfg, ?_⟩⟩
  change g ≫ f = 𝟙 _
  rw [hfk]
  exact hgk

/-- Every original degree-one simplex of a Kan complex satisfies the exact core predicate. -/
theorem kan_edgeIsInvertible (X : SSet.{u}) [X.KanComplex]
    (e : X.obj (op ⦋1⦌)) : edgeIsInvertible X e := by
  have h := kan_unit_mapped_edge_isIso (SSet.Edge.mk' e)
  simp only [nerve.homEquiv_apply, SSet.Edge.map_edge, SSet.Edge.mk'_edge,
    isIso_comp_left_iff, isIso_comp_right_iff] at h
  exact h

/-- All Kan subcomplexes of X are contained in the same original preimage core candidate. -/
theorem kanSubcomplex_le_ordinaryCoreCandidate (X : SSet.{u}) (A : X.Subcomplex)
    [(A : SSet.{u}).KanComplex] : A ≤ ordinaryCoreCandidate X := by
  apply (le_ordinaryCoreCandidate_iff_edges_iso X A).mpr
  intro e he
  let ae : (A : SSet.{u}).obj (op ⦋1⦌) := ⟨e, he⟩
  have : IsIso (((homotopyCategoryUnit (A : SSet.{u})).app (op ⦋1⦌) ae).hom) :=
    kan_edgeIsInvertible (A : SSet.{u}) ae
  have h : IsIso ((SSet.hoFunctor.map A.ι).toFunctor.map
      (((homotopyCategoryUnit (A : SSet.{u})).app (op ⦋1⦌) ae).hom)) := inferInstance
  change IsIso (((nerveMap (SSet.hoFunctor.map A.ι).toFunctor).app (op ⦋1⦌)
    ((homotopyCategoryUnit (A : SSet.{u})).app (op ⦋1⦌) ae)).hom) at h
  have hn := (congrArg
    (fun k : (A : SSet.{u}) ⟶ nerve (SSet.hoFunctor.obj X) ↦ k.app (op ⦋1⦌) ae)
    (CategoryTheory.nerveAdjunction.unit.naturality A.ι)).symm
  change (nerveMap (SSet.hoFunctor.map A.ι).toFunctor).app (op ⦋1⦌)
      ((homotopyCategoryUnit (A : SSet.{u})).app (op ⦋1⦌) ae) =
    (homotopyCategoryUnit X).app (op ⦋1⦌) e at hn
  rw [hn] at h
  exact h

/-- If the input is already Kan, the same core candidate contains every simplex. -/
theorem ordinaryCoreCandidate_eq_top_of_kan (X : SSet.{u}) [X.KanComplex] :
    ordinaryCoreCandidate X = ⊤ := by
  apply top_unique
  intro q s _
  apply (mem_ordinaryCoreCandidate_iff_edges_iso X q s).mpr
  intro α
  exact kan_edgeIsInvertible X (X.map α.op s)

end

end DaggerOriginalOrdinaryKanCoreContainsKanSubcomplexes
