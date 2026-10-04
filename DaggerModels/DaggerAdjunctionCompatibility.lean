import DaggerModels.RigidificationOpposite
import DaggerModels.DaggerCoherentNerve

/-!
# Restricting the original adjunction to dagger-compatible maps

The original ordinary adjunction and its proved opposite mate identify the exact
dagger commutation equations on both sides. All full enriched and simplicial maps
are retained. No fibrancy, model structure, or new mathematical premise is used.
-/

open CategoryTheory

universe u

noncomputable section

namespace DaggerModels.OrdinaryRigidification.DaggerAdjunction

open RigidificationOpposite NerveOpposite DaggerNerve

/-- The ordinary adjoint is dagger-compatible exactly when the original map is. -/
theorem dagger_compatibility_iff (X : DaggerSSet.{u}) (C : DaggerSimplicialCat.{u, u})
    (f : rigidification.obj X.toSSet ⟶ C.toSimplicialCat) :
    f ≫ enrichedDagger C =
      rigidification.map X.dagger ≫ rigidificationOppositeIso.hom.app X.toSSet ≫
        SimplicialCat.oppositeFunctor.map f ↔
    rigidificationCoherentNerveAdjunction.homEquiv X.toSSet C.toSimplicialCat f ≫
        nerveDagger C =
      X.dagger ≫ SSet.opFunctor.map
        (rigidificationCoherentNerveAdjunction.homEquiv X.toSSet C.toSimplicialCat f) := by
  let A := rigidificationCoherentNerveAdjunction.{u}
  have hmate : A.homEquiv X.toSSet.op (SimplicialCat.opposite C.toSimplicialCat)
      (rigidificationOppositeIso.hom.app X.toSSet ≫ SimplicialCat.oppositeFunctor.map f) =
      SSet.opFunctor.map (A.homEquiv X.toSSet C.toSimplicialCat f) ≫
        coherentNerveOppositeIso.inv.app C.toSimplicialCat :=
    rigidificationOppositeIso_mate X.toSSet C.toSimplicialCat f
  constructor
  · intro h
    have h' := congrArg (A.homEquiv X.toSSet (SimplicialCat.opposite C.toSimplicialCat)) h
    rw [A.homEquiv_naturality_right, A.homEquiv_naturality_left,
      hmate] at h'
    have h'' := congrArg (fun k ↦ k ≫ coherentNerveOppositeIso.hom.app C.toSimplicialCat) h'
    simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, nerveDagger] using h''
  · intro h
    apply (A.homEquiv X.toSSet (SimplicialCat.opposite C.toSimplicialCat)).injective
    rw [A.homEquiv_naturality_right, A.homEquiv_naturality_left,
      hmate]
    apply (cancel_mono (coherentNerveOppositeIso.hom.app C.toSimplicialCat)).1
    simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, nerveDagger] using h

end DaggerModels.OrdinaryRigidification.DaggerAdjunction
