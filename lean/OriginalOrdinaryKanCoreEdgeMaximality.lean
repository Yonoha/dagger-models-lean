import OriginalOrdinaryKanCoreEdgeMembership

/-!
# Maximality for the exact edge-invertibility predicate

The candidate has exactly the original edges whose homotopy-category unit
images are isomorphisms. It contains any subcomplex all of whose edges have
that property. This is maximality for the edge predicate, not yet a proof of
the Kan condition or maximality among Kan subcomplexes.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreNerveMembership
open DaggerOriginalOrdinaryKanCoreEdgeMembership

universe v u

namespace DaggerOriginalOrdinaryKanCoreEdgeMaximality

noncomputable section

/-- In degree one every arrow of the diagram is either identity or its single edge. -/
theorem arrows_iso_of_hom_iso {C : Type u} [Category.{v} C]
    (s : ComposableArrows C 1) [IsIso s.hom]
    {i j : Fin 2} (f : i ⟶ j) : IsIso (s.map f) := by
  fin_cases i <;> fin_cases j
  · have hf : f = 𝟙 (0 : Fin 2) := Subsingleton.elim _ _
    rw [hf]
    infer_instance
  · have hf : f = homOfLE (show (0 : Fin 2) ≤ 1 by decide) := Subsingleton.elim _ _
    rw [hf]
    change IsIso s.hom
    infer_instance
  · have hf : ¬ ((1 : Fin 2) ≤ 0) := by decide
    exact False.elim (hf (leOfHom f))
  · have hf : f = 𝟙 (1 : Fin 2) := Subsingleton.elim _ _
    rw [hf]
    infer_instance

/-- The actual degree-one part of the candidate consists exactly of invertible unit edges. -/
theorem mem_ordinaryCoreCandidate_one_iff (X : SSet.{u}) (e : X.obj (op ⦋1⦌)) :
    e ∈ (ordinaryCoreCandidate X).obj (op ⦋1⦌) ↔ edgeIsInvertible X e := by
  constructor
  · intro he
    have h := (mem_ordinaryCoreCandidate_iff_unit_arrows_iso X (op ⦋1⦌) e).mp he
      (homOfLE (show (0 : Fin 2) ≤ 1 by decide))
    exact h
  · intro he
    have : IsIso (((homotopyCategoryUnit X).app (op ⦋1⦌) e).hom) := he
    apply (mem_ordinaryCoreCandidate_iff_unit_arrows_iso X (op ⦋1⦌) e).mpr
    intro i j f
    exact arrows_iso_of_hom_iso _ f

/-- Exact largest-subcomplex characterization by the original edge predicate. -/
theorem le_ordinaryCoreCandidate_iff_edges_iso (X : SSet.{u}) (A : X.Subcomplex) :
    A ≤ ordinaryCoreCandidate X ↔
      ∀ e : X.obj (op ⦋1⦌), e ∈ A.obj (op ⦋1⦌) → edgeIsInvertible X e := by
  constructor
  · intro h e he
    exact (mem_ordinaryCoreCandidate_one_iff X e).mp (h (op ⦋1⦌) he)
  · intro h q s hs
    apply (mem_ordinaryCoreCandidate_iff_edges_iso X q s).mpr
    intro α
    exact h (X.map α.op s) (A.map α.op hs)

end

end DaggerOriginalOrdinaryKanCoreEdgeMaximality
