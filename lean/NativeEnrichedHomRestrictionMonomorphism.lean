import NativeDaggerEnrichedHomRestriction

/-! The original Hom subcomplex inclusions are monomorphisms of whole enriched categories. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels
open DaggerNativeEnrichedHomSubcomplexRestriction
universe u
namespace DaggerNativeEnrichedHomRestrictionMonomorphism
noncomputable section

def objectHomData {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    Σ o : C.Obj → D.Obj, ∀ x y, C.enriched.Hom x y ⟶ D.enriched.Hom (o x) (o y) :=
  ⟨F.obj, F.map⟩

theorem inclusion_mono (C : SimplicialCat.{u, u})
    (A : ∀ x y : C.Obj, (C.enriched.Hom x y).Subcomplex)
    (hi : ∀ x q s, (C.enriched.id x).app q s ∈ (A x x).obj q)
    (hc : ∀ x y z q (s : (A x y : SSet.{u}).obj q) (t : (A y z : SSet.{u}).obj q),
      (C.enriched.comp x y z).app q (s.val, t.val) ∈ (A x z).obj q) :
    Mono (inclusion C A hi hc) where
  right_cancellation := by
    intro E F G h
    rcases F with ⟨oF, mF, iF, cF⟩
    rcases G with ⟨oG, mG, iG, cG⟩
    have ho : oF = oG := congrArg (fun H : E ⟶ C ↦ H.obj) h
    cases ho
    have hd := congrArg (objectHomData (C := E) (D := C)) h
    have hm : (fun x y ↦ mF x y ≫ (A (oF x) (oF y)).ι) =
        (fun x y ↦ mG x y ≫ (A (oF x) (oF y)).ι) :=
      eq_of_heq (Sigma.mk.inj hd).2
    have hmap : mF = mG := by
      funext x y
      apply (cancel_mono (A (oF x) (oF y)).ι).mp
      exact congrFun (congrFun hm x) y
    cases hmap
    rfl

theorem dagger_inclusion_mono (D : DaggerSimplicialCat.{u, u})
    (A : ∀ x y : D.Obj, (D.enriched.Hom x y).Subcomplex)
    (hi : ∀ x q s, (D.enriched.id x).app q s ∈ (A x x).obj q)
    (hc : ∀ x y z q (s : (A x y : SSet.{u}).obj q) (t : (A y z : SSet.{u}).obj q),
      (D.enriched.comp x y z).app q (s.val, t.val) ∈ (A x z).obj q)
    (hd : ∀ x y q (s : (A x y : SSet.{u}).obj q),
      (D.daggerStructure.dagger x y).app q s.val ∈ (A y x).obj q) :
    Mono (DaggerNativeDaggerEnrichedHomRestriction.inclusion D A hi hc hd) where
  right_cancellation := by
    intro E F G h
    apply DaggerSimplicialCat.Hom.ext
    have := inclusion_mono D.toSimplicialCat A hi hc
    have h0 := congrArg (fun H : E ⟶ D ↦ H.toEnrichedFunctor) h
    let f0 : E.toSimplicialCat ⟶ restricted D.toSimplicialCat A hi hc := F.toEnrichedFunctor
    let g0 : E.toSimplicialCat ⟶ restricted D.toSimplicialCat A hi hc := G.toEnrichedFunctor
    have hp : f0 ≫ inclusion D.toSimplicialCat A hi hc =
        g0 ≫ inclusion D.toSimplicialCat A hi hc := h0
    exact (cancel_mono (inclusion D.toSimplicialCat A hi hc)).mp hp

end
end DaggerNativeEnrichedHomRestrictionMonomorphism
