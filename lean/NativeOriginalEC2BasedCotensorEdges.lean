import NativeOriginalEC2CanonicalComponents
import NativeOriginalEquivariantCotensorAdjunction
import NativeOriginalCoslicePathMap
import OriginalStrictPathFiberVertices

/-! Actual based equivariant cotensor maps are actual edges between the SAME enriched constants. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction
open DaggerOriginalSimplicialEquivariantParameterTensor
open DaggerOriginalSimplicialEquivariantEnrichedAdjunction
open DaggerNativeOriginalEC2CanonicalComponents DaggerNativeOriginalEquivariantCotensorAdjunction
open DaggerNativeOriginalCoslicePathMap
open scoped SSet.modelCategoryQuillen DaggerOriginalSimplicialActionModelCategory
universe u
namespace DaggerNativeOriginalEC2BasedCotensorEdges
noncomputable section

variable (A : Action SSet.{u} C2.{u}) (x y : A.V _⦋0⦌)
variable (hx : ∀ g, (A.ρ g).asHom.app (op ⦋0⦌) x = x)
variable (hy : ∀ g, (A.ρ g).asHom.app (op ⦋0⦌) y = y)

def BasedHom := {f : simplicialAction.{u} ⟶ cotensorAction Δ[1] A //
  f.hom ≫ A.V.pathEv₀ = SSet.const x ∧ f.hom ≫ A.V.pathEv₁ = SSet.const y}

theorem endpoint_iff (q : simplicialParameterTensor simplicialAction.{u} Δ[1] ⟶ A)
    (v : Fin 2) :
    intervalEndpoint simplicialAction.V v ≫ q.hom = SSet.const x ↔
      simplicialParameterTensorMap simplicialAction
        (SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm v)) ≫ q =
          enrichedConstant A x hx := by
  constructor
  · intro h
    apply Action.hom_ext
    rw [enrichedConstant_hom]
    apply NatTrans.ext
    funext n p
    rcases p with ⟨e, z⟩
    have hz : z = SSet.stdSimplex.const 0 0 n := Subsingleton.elim _ _
    subst z
    change q.hom.app n (e, SSet.stdSimplex.const 1 v n) =
      (SSet.const x : simplicialAction.V ⟶ A.V).app n e
    exact congrFun (NatTrans.congr_app h n) e
  · intro h
    have hh := congrArg Action.Hom.hom h
    rw [enrichedConstant_hom] at hh
    apply NatTrans.ext
    funext n e
    exact congrFun (NatTrans.congr_app hh n) (e, SSet.stdSimplex.const 0 0 n)

def edgeOfBasedHom (f : BasedHom A x y) :
    SSet.Edge (enrichedConstant A x hx) (enrichedConstant A y hy) where
  edge := uncurryAction Δ[1] simplicialAction A f.val
  src_eq := by
    let q := uncurryAction Δ[1] simplicialAction A f.val
    have hc : curryAction Δ[1] simplicialAction A q = f.val :=
      (cotensorActionHomEquiv Δ[1] simplicialAction A).symm_apply_apply f.val
    have h := curry_evaluation q.hom (0 : Fin 2)
    change (curryAction Δ[1] simplicialAction A q).hom ≫ A.V.pathEv₀ = _ at h
    rw [hc, f.property.1] at h
    change simplicialParameterTensorMap simplicialAction (SSet.stdSimplex.δ 1) ≫ q = _
    rw [SSet.stdSimplex.δ_one]
    exact (endpoint_iff A x hx q 0).1 h.symm
  tgt_eq := by
    let q := uncurryAction Δ[1] simplicialAction A f.val
    have hc : curryAction Δ[1] simplicialAction A q = f.val :=
      (cotensorActionHomEquiv Δ[1] simplicialAction A).symm_apply_apply f.val
    have h := curry_evaluation q.hom (1 : Fin 2)
    change (curryAction Δ[1] simplicialAction A q).hom ≫ A.V.pathEv₁ = _ at h
    rw [hc, f.property.2] at h
    change simplicialParameterTensorMap simplicialAction (SSet.stdSimplex.δ 0) ≫ q = _
    rw [SSet.stdSimplex.δ_zero]
    exact (endpoint_iff A y hy q 1).1 h.symm

def basedHomOfEdge (e : SSet.Edge (enrichedConstant A x hx) (enrichedConstant A y hy)) :
    BasedHom A x y :=
  ⟨curryAction Δ[1] simplicialAction A e.edge, by
    constructor
    · change (curryAction Δ[1] simplicialAction A e.edge).hom ≫ A.V.pathEv₀ = _
      rw [show (curryAction Δ[1] simplicialAction A e.edge).hom =
        curry ((β_ Δ[1] simplicialAction.V).hom ≫ e.edge.hom) from rfl]
      rw [SSet.pathEv₀, curry_evaluation]
      apply (endpoint_iff A x hx e.edge 0).2
      have h := e.src_eq
      change simplicialParameterTensorMap simplicialAction (SSet.stdSimplex.δ 1) ≫ e.edge = _ at h
      rw [SSet.stdSimplex.δ_one] at h
      exact h
    · change (curryAction Δ[1] simplicialAction A e.edge).hom ≫ A.V.pathEv₁ = _
      rw [show (curryAction Δ[1] simplicialAction A e.edge).hom =
        curry ((β_ Δ[1] simplicialAction.V).hom ≫ e.edge.hom) from rfl]
      rw [SSet.pathEv₁, curry_evaluation]
      apply (endpoint_iff A y hy e.edge 1).2
      have h := e.tgt_eq
      change simplicialParameterTensorMap simplicialAction (SSet.stdSimplex.δ 0) ≫ e.edge = _ at h
      rw [SSet.stdSimplex.δ_zero] at h
      exact h⟩

theorem basedHom_nonempty_iff_edges :
    Nonempty (BasedHom A x y) ↔
      Nonempty (SSet.Edge (enrichedConstant A x hx) (enrichedConstant A y hy)) :=
  ⟨fun ⟨f⟩ ↦ ⟨edgeOfBasedHom A x y hx hy f⟩,
    fun ⟨e⟩ ↦ ⟨basedHomOfEdge A x y hx hy e⟩⟩

theorem basedHom_nonempty_iff_canonical_components [A.V.KanComplex] :
    Nonempty (BasedHom A x y) ↔
      SSet.π₀.mk (DaggerNativeOriginalActionCanonicalConstants.canonicalZero A x hx) =
        SSet.π₀.mk (DaggerNativeOriginalActionCanonicalConstants.canonicalZero A y hy) := by
  have : IsFibrant A :=
    (DaggerOriginalSimplicialActionModelCategory.isFibrant_iff_underlying _).2 inferInstance
  have : (enrichedMapping simplicialAction A).KanComplex :=
    DaggerOriginalCompletedDaggerDerivedMapping.enrichedMapping_kan simplicialAction A
  have he : Nonempty (SSet.Edge (enrichedConstant A x hx) (enrichedConstant A y hy)) ↔
      SSet.π₀.mk (enrichedConstant A x hx) = SSet.π₀.mk (enrichedConstant A y hy) := by
    constructor
    · rintro ⟨e⟩
      exact SSet.π₀.sound e.edge e.src_eq e.tgt_eq
    · intro h
      obtain ⟨v⟩ :=
        (DaggerOriginalStrictPathFiberVertices.strictPathFiber_vertex_nonempty_iff
          (enrichedMapping simplicialAction A) _ _).2 h
      exact ⟨DaggerOriginalStrictPathFiberVertices.edgeOfPathVertex v⟩
  exact (basedHom_nonempty_iff_edges A x y hx hy).trans
    (he.trans (same_component_iff A x y hx hy))

end
end DaggerNativeOriginalEC2BasedCotensorEdges
