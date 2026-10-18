import OriginalAmalgamTranslationCollapseRecovered

/-!
# Endpoint equality transports in the original simplicial category

The selected ordinary enriched functor transport theorem is reused directly.
These wrappers retain both source and target endpoint equalities for arrow
retracts. No dagger structure or fibrancy assumption occurs here.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels

universe u

namespace DaggerModels.OriginalOrdinaryEndpointTransport

noncomputable section

/-- Transport an original Hom simplicial set across both endpoint equalities. -/
def transport (C : SimplicialCat.{u, u}) {a a' b b' : C.Obj}
    (ha : a = a') (hb : b = b') :
    C.enriched.Hom a b ⟶ C.enriched.Hom a' b' :=
  eqToHom (by rw [ha, hb])

@[simp] theorem transport_refl (C : SimplicialCat.{u, u}) (a b : C.Obj) :
    transport C (rfl : a = a) (rfl : b = b) = 𝟙 _ := rfl

@[simp] theorem transport_comp (C : SimplicialCat.{u, u})
    {a a' a'' b b' b'' : C.Obj} (ha : a = a') (ha' : a' = a'')
    (hb : b = b') (hb' : b' = b'') :
    transport C ha hb ≫ transport C ha' hb' =
      transport C (ha.trans ha') (hb.trans hb') := by
  cases ha
  cases ha'
  cases hb
  cases hb'
  simp

/-- Naturality of both endpoint transports for an actual ordinary functor. -/
theorem transport_map {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    {a a' b b' : C.Obj} (ha : a = a') (hb : b = b') :
    transport C ha hb ≫ F.map a' b' =
      F.map a b ≫ transport D (congrArg F.obj ha) (congrArg F.obj hb) :=
  DaggerAmalgamTranslationCollapse.map_transport F ha hb

/-- Equality of ordinary enriched functors includes the target Hom cast. -/
theorem map_of_eq {C D : SimplicialCat.{u, u}} {F G : C ⟶ D}
    (h : F = G) (a b : C.Obj) :
    F.map a b ≫ transport D
      (congrArg (fun T : C ⟶ D ↦ T.obj a) h)
      (congrArg (fun T : C ⟶ D ↦ T.obj b) h) = G.map a b := by
  cases h
  simp

end

end DaggerModels.OriginalOrdinaryEndpointTransport
