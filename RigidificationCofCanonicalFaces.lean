import RigidificationCofSubsets
import RigidificationCofObjectTransport

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.BoundaryData

noncomputable section

variable {n : ℕ} {A : SC.{u}}

theorem faceFunctor_vertex (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : s ≠ Finset.univ)
    (x : SimplicialThickening (ULift.{u} s)) :
    (faceFunctor a s hs hp).obj x = vertex a x.as.down.val := by
  have h := simplex_obj a (faceOrdinal s hs) (faceOrdinal_not_surjective s hs hp)
    ((faceOrderIso s hs).symm x.as.down)
  dsimp [faceOrdinal] at h
  simp only [OrderIso.apply_symm_apply] at h
  exact h

/-- SAME face functor; only its object names are transported to the original boundary vertices. -/
def canonicalFaceFunctor (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : s ≠ Finset.univ) :
    DaggerModels.SimplicialCat.of (SimplicialThickening (ULift.{u} s)) ⟶ A :=
  reobject (faceFunctor a s hs hp) (fun x => vertex a x.as.down.val)
    (faceFunctor_vertex a s hs hp)

theorem canonicalFaceFunctor_obj (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : s ≠ Finset.univ)
    (x : SimplicialThickening (ULift.{u} s)) :
    (canonicalFaceFunctor a s hs hp).obj x = vertex a x.as.down.val := rfl

/-- The WHOLE original functor restricts strictly, including all Hom simplices. -/
theorem canonicalFaceFunctor_restrict
    (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (s t : Finset (Fin (n + 2))) (hs : s.Nonempty) (ht : t.Nonempty)
    (hps : s ≠ Finset.univ) (hpt : t ≠ Finset.univ) (hst : s ⊆ t) :
    SimplicialThickening.functor (faceInclusion hst).uliftMap ≫
      canonicalFaceFunctor a t ht hpt = canonicalFaceFunctor a s hs hps := by
  unfold canonicalFaceFunctor
  rw [reobject_comp]
  exact reobject_eq (faceFunctor_restrict a s t hs ht hps hpt hst) _ _ _

end

end DaggerOrdinaryRigidificationCof.BoundaryData
