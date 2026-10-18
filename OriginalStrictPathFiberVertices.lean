import OriginalFullVertexPathFiberModelConsequences
import TopCatModelCategory.SSet.FundamentalGroupoidPiOne

/-!
# Actual strict path-fiber vertices and original components

The native internal-hom vertex equivalence identifies a vertex of the exact
paired-endpoint fiber with an original edge with the same two endpoints.
For Kan input, the existing fundamental-groupoid component theorem therefore
identifies nonemptiness of this same fiber with equality of components.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalFullVertexSubcomplex

universe u

namespace DaggerOriginalStrictPathFiberVertices

noncomputable section

/-- The native zero endpoint is the original source face of the same edge. -/
theorem pathVertex_source {X : SSet.{u}} (q : Δ[1] ⟶ X) :
    X.pathEv₀.app (op ⦋0⦌) (SSet.ihom₀Equiv.symm q) =
      SimplicialObject.δ X (1 : Fin 2) (SSet.yonedaEquiv q) := by
  obtain ⟨s, rfl⟩ := SSet.yonedaEquiv.symm.surjective q
  rw [SSet.pathEv₀, SSet.ihomEv_app_app_ihom₀Equiv_symm, Equiv.apply_symm_apply]
  calc
    _ = SSet.yonedaEquiv (SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm s) := by
      rw [SSet.stdSimplex.δ_one]
      rfl
    _ = _ := by rw [← SSet.yonedaEquiv_symm_δ, Equiv.apply_symm_apply]

/-- The native one endpoint is the original target face of the same edge. -/
theorem pathVertex_target {X : SSet.{u}} (q : Δ[1] ⟶ X) :
    X.pathEv₁.app (op ⦋0⦌) (SSet.ihom₀Equiv.symm q) =
      SimplicialObject.δ X (0 : Fin 2) (SSet.yonedaEquiv q) := by
  obtain ⟨s, rfl⟩ := SSet.yonedaEquiv.symm.surjective q
  rw [SSet.pathEv₁, SSet.ihomEv_app_app_ihom₀Equiv_symm, Equiv.apply_symm_apply]
  calc
    _ = SSet.yonedaEquiv (SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm s) := by
      rw [SSet.stdSimplex.δ_zero]
      rfl
    _ = _ := by rw [← SSet.yonedaEquiv_symm_δ, Equiv.apply_symm_apply]

/-- An original edge gives a vertex in the exact original strict endpoint fiber. -/
def pathVertexOfEdge {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} (e : SSet.Edge a b) :
    (strictPathFiber X a b : SSet).obj (op ⦋0⦌) :=
  ⟨SSet.ihom₀Equiv.symm (SSet.yonedaEquiv.symm e.edge), by
    apply (SSet.Subcomplex.mem_fiber_obj_zero_iff X.pathEv₀₁ (a, b) _).mpr
    apply Prod.ext
    · change X.pathEv₀.app (op ⦋0⦌)
        (SSet.ihom₀Equiv.symm (SSet.yonedaEquiv.symm e.edge)) = a
      rw [pathVertex_source, Equiv.apply_symm_apply]
      exact e.src_eq
    · change X.pathEv₁.app (op ⦋0⦌)
        (SSet.ihom₀Equiv.symm (SSet.yonedaEquiv.symm e.edge)) = b
      rw [pathVertex_target, Equiv.apply_symm_apply]
      exact e.tgt_eq⟩

/-- A vertex of the exact strict endpoint fiber recovers its original edge. -/
def edgeOfPathVertex {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}
    (v : (strictPathFiber X a b : SSet).obj (op ⦋0⦌)) : SSet.Edge a b where
  edge := SSet.yonedaEquiv (SSet.ihom₀Equiv v.val)
  src_eq := by
    have hv := congrArg Prod.fst
      ((SSet.Subcomplex.mem_fiber_obj_zero_iff X.pathEv₀₁ (a, b) v.val).mp v.property)
    change X.pathEv₀.app (op ⦋0⦌) v.val = a at hv
    have h := pathVertex_source (SSet.ihom₀Equiv v.val)
    rw [Equiv.symm_apply_apply] at h
    exact h.symm.trans hv
  tgt_eq := by
    have hv := congrArg Prod.snd
      ((SSet.Subcomplex.mem_fiber_obj_zero_iff X.pathEv₀₁ (a, b) v.val).mp v.property)
    change X.pathEv₁.app (op ⦋0⦌) v.val = b at hv
    have h := pathVertex_target (SSet.ihom₀Equiv v.val)
    rw [Equiv.symm_apply_apply] at h
    exact h.symm.trans hv

/-- The strict path-fiber vertices are exactly the same original edges, with fixed endpoints. -/
def strictPathVertexEquiv (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    (strictPathFiber X a b : SSet).obj (op ⦋0⦌) ≃ SSet.Edge a b where
  toFun := edgeOfPathVertex
  invFun := pathVertexOfEdge
  left_inv v := by
    apply Subtype.ext
    change SSet.ihom₀Equiv.symm
      (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (SSet.ihom₀Equiv v.val))) = v.val
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  right_inv e := by
    apply SSet.Edge.ext
    change SSet.yonedaEquiv
      (SSet.ihom₀Equiv (SSet.ihom₀Equiv.symm (SSet.yonedaEquiv.symm e.edge))) = e.edge
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The original strict path fiber has a vertex exactly when its original endpoints agree in π₀.
-/
theorem strictPathFiber_vertex_nonempty_iff (X : SSet.{u}) [X.KanComplex]
    (a b : X.obj (op ⦋0⦌)) :
    Nonempty ((strictPathFiber X a b : SSet).obj (op ⦋0⦌)) ↔ SSet.π₀.mk a = SSet.π₀.mk b := by
  constructor
  · rintro ⟨v⟩
    let e := strictPathVertexEquiv X a b v
    exact SSet.π₀.sound e.edge e.src_eq e.tgt_eq
  · intro h
    obtain ⟨e⟩ := (SSet.KanComplex.π₀_mk_eq_π₀_mk_iff a b).mp h
    refine ⟨⟨SSet.ihom₀Equiv.symm e.map, ?_⟩⟩
    apply (SSet.Subcomplex.mem_fiber_obj_zero_iff X.pathEv₀₁ (a, b) _).mpr
    apply Prod.ext
    · change X.pathEv₀.app (op ⦋0⦌) (SSet.ihom₀Equiv.symm e.map) = a
      rw [SSet.pathEv₀, SSet.ihomEv_app_app_ihom₀Equiv_symm]
      exact e.comm₀'
    · change X.pathEv₁.app (op ⦋0⦌) (SSet.ihom₀Equiv.symm e.map) = b
      rw [SSet.pathEv₁, SSet.ihomEv_app_app_ihom₀Equiv_symm]
      exact e.comm₁'

/-- Native weak equivalences of Kan complexes preserve existence of actual vertices. -/
theorem vertices_nonempty_iff_of_weakEquivalence {X Y : SSet.{u}} [X.KanComplex]
    [Y.KanComplex] (f : X ⟶ Y) [WeakEquivalence f] :
    Nonempty (X.obj (op ⦋0⦌)) ↔ Nonempty (Y.obj (op ⦋0⦌)) := by
  constructor
  · rintro ⟨x⟩
    exact ⟨f.app (op ⦋0⦌) x⟩
  · rintro ⟨y⟩
    have hf : SSet.KanComplex.W f := (SSet.weakEquivalence_iff_kanComplexW f).1 inferInstance
    obtain ⟨c, _⟩ := hf.bijective_mapπ₀.2 (SSet.π₀.mk y)
    obtain ⟨x, _⟩ := SSet.π₀.mk_surjective c
    exact ⟨x⟩

end

end DaggerOriginalStrictPathFiberVertices
