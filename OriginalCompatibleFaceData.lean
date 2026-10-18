import OriginalSubcomplexNerveData
import RigidificationCofRestrictions
import RigidificationCofObjectTransport

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.SubcomplexNerveData

noncomputable section

open DaggerOrdinaryRigidificationCof.BoundaryData
open DaggerModels.OrdinaryRigidification.NerveVertices

variable {d : ℕ} (K : (Δ[d] : SSet.{u}).Subcomplex) {A : SC.{u}}

/-- Evaluate a vertex actually present in the supplied subcomplex. -/
def vertex (a : (K : SSet) ⟶ N.obj A)
    (hV : ∀ i : Fin (d + 1), Contains K (vertexMap i))
    (i : Fin (d + 1)) : A.Obj :=
  (simplex K a (vertexMap i) (hV i)).obj zeroObject

/-- Every included simplex has the vertex objects supplied by that same map `a`. -/
theorem simplex_obj (a : (K : SSet) ⟶ N.obj A)
    (hV : ∀ i : Fin (d + 1), Contains K (vertexMap i))
    {m : SimplexCategory} (φ : m ⟶ ⦋d⦌) (hφ : Contains K φ)
    (i : Fin (m.len + 1)) :
    (simplex K a φ hφ).obj (.mk (ULift.up i)) =
      vertex K a hV (φ.toOrderHom i) := by
  have h := congrArg (fun F : T.obj ⦋0⦌ ⟶ A ↦ F.obj zeroObject)
    (simplex_precompose K a φ hφ (vertexMap i))
  have he := simplex_eq K a (vertexMap_comp φ i)
    (contains_comp K φ hφ (vertexMap i)) (hV (φ.toOrderHom i))
  exact h.trans (congrArg (fun F : T.obj ⦋0⦌ ⟶ A ↦ F.obj zeroObject) he)

/-- A face functor has the shared vertex assignment at every object. -/
theorem faceFunctor_vertex (a : (K : SSet) ⟶ N.obj A)
    (hV : ∀ i : Fin (d + 1), Contains K (vertexMap i))
    (s : Finset (Fin (d + 1))) (hs : s.Nonempty)
    (hface : Contains K (faceOrdinal s hs))
    (x : (faceSource.{u} s).Obj) :
    (faceFunctor K a s hs hface).obj x = vertex K a hV x.as.down.val := by
  have h := simplex_obj K a hV (faceOrdinal s hs) hface
    ((faceOrderIso s hs).symm x.as.down)
  dsimp [faceOrdinal] at h
  simp only [OrderIso.apply_symm_apply] at h
  exact h

end

end DaggerOrdinaryRigidificationCof.SubcomplexNerveData

namespace DaggerOrdinaryRigidificationCof

noncomputable section

open BoundaryData

/-- Whole enriched face functors with one literal common vertex assignment. -/
structure CompatibleFaceData (d : ℕ) (A : SC.{u})
    (P : Finset (Fin (d + 1)) → Prop) where
  obj : Fin (d + 1) → A.Obj
  F : ∀ (s : Finset (Fin (d + 1))), s.Nonempty → P s → (faceSource.{u} s ⟶ A)
  F_obj : ∀ s hs hp (x : (faceSource.{u} s).Obj),
    (F s hs hp).obj x = obj x.as.down.val
  F_restrict : ∀ (s t : Finset (Fin (d + 1)))
      (hs : s.Nonempty) (ht : t.Nonempty)
      (hps : P s) (hpt : P t) (hst : s ⊆ t),
    faceInclusionFunctor.{u} hst ≫ F t ht hpt = F s hs hps

namespace CompatibleFaceData

variable {d : ℕ} {A : SC.{u}} {P : Finset (Fin (d + 1)) → Prop}

/-- All four fields come from the same actual map from a subcomplex to `N A`. -/
def ofSubcomplex (K : (Δ[d] : SSet.{u}).Subcomplex)
    (a : (K : SSet) ⟶ N.obj A)
    (hV : ∀ i : Fin (d + 1), SubcomplexNerveData.Contains K (vertexMap i))
    (hP : ∀ s hs, P s → SubcomplexNerveData.Contains K (faceOrdinal s hs)) :
    CompatibleFaceData d A P where
  obj := SubcomplexNerveData.vertex K a hV
  F := fun s hs hp ↦ SubcomplexNerveData.faceFunctor K a s hs (hP s hs hp)
  F_obj := by
    intro s hs hp x
    exact SubcomplexNerveData.faceFunctor_vertex K a hV s hs (hP s hs hp) x
  F_restrict := by
    intro s t hs ht hps hpt hst
    exact SubcomplexNerveData.faceFunctor_restrict K a s t hs ht
      (hP s hs hps) (hP t ht hpt) hst

/-- Transport only object names, retaining the same complete enriched face functor. -/
def canonicalF (D : CompatibleFaceData d A P)
    (s : Finset (Fin (d + 1))) (hs : s.Nonempty) (hp : P s) :
    faceSource.{u} s ⟶ A :=
  reobject (D.F s hs hp) (fun x ↦ D.obj x.as.down.val) (D.F_obj s hs hp)

@[simp]
theorem canonicalF_obj (D : CompatibleFaceData d A P)
    (s : Finset (Fin (d + 1))) (hs : s.Nonempty) (hp : P s)
    (x : (faceSource.{u} s).Obj) :
    (D.canonicalF s hs hp).obj x = D.obj x.as.down.val := rfl

/-- Canonical object names do not replace the original enriched face functor. -/
theorem canonicalF_eq (D : CompatibleFaceData d A P)
    (s : Finset (Fin (d + 1))) (hs : s.Nonempty) (hp : P s) :
    D.canonicalF s hs hp = D.F s hs hp :=
  reobject_self _ _ _

/-- Canonical object names preserve the entire enriched restriction equation. -/
theorem canonicalF_restrict (D : CompatibleFaceData d A P)
    (s t : Finset (Fin (d + 1))) (hs : s.Nonempty) (ht : t.Nonempty)
    (hps : P s) (hpt : P t) (hst : s ⊆ t) :
    faceInclusionFunctor.{u} hst ≫ D.canonicalF t ht hpt =
      D.canonicalF s hs hps := by
  unfold canonicalF
  rw [reobject_comp]
  exact reobject_eq (D.F_restrict s t hs ht hps hpt hst) _ _ _

end CompatibleFaceData

end

end DaggerOrdinaryRigidificationCof
