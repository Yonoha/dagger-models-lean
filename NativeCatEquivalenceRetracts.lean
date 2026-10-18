import NativeCatEquivalenceWeakProperties

/-!
# Strict Cat arrow retracts preserve ordinary category equivalences

Use native equivalence data and whiskering on the actual arrow-retract
squares and their exact equations. No weakening to objectwise retracts occurs.
-/
set_option autoImplicit false
open CategoryTheory
universe u
namespace DaggerNativeCatEquivalenceRetracts
open DaggerNativeCatEquivalenceWeakProperties

/-- The strict retract squares give an explicit inverse through the larger equivalence. -/
theorem equivalence_of_retract {X Y Z W : Cat.{u, u}} {f : X ⟶ Y} {g : Z ⟶ W}
    (h : RetractArrow f g) (hg : equivalences g) : equivalences f := by
  letI : g.toFunctor.IsEquivalence := hg
  let e := g.toFunctor.asEquivalence
  let e₁ : h.i.left.toFunctor ⋙ h.r.left.toFunctor ≅ 𝟭 X :=
    eqToIso (congrArg (fun k : X ⟶ X ↦ k.toFunctor) h.left.retract)
  let e₂ : h.i.right.toFunctor ⋙ h.r.right.toFunctor ≅ 𝟭 Y :=
    eqToIso (congrArg (fun k : Y ⟶ Y ↦ k.toFunctor) h.right.retract)
  let si : h.i.left.toFunctor ⋙ g.toFunctor ≅ f.toFunctor ⋙ h.i.right.toFunctor :=
    eqToIso (congrArg (fun k : X ⟶ W ↦ k.toFunctor) h.i_w)
  let sr : h.r.left.toFunctor ⋙ f.toFunctor ≅ g.toFunctor ⋙ h.r.right.toFunctor :=
    eqToIso (congrArg (fun k : Z ⟶ Y ↦ k.toFunctor) h.r_w)
  let inverse := h.i.right.toFunctor ⋙ e.inverse ⋙ h.r.left.toFunctor
  let unit : 𝟭 X ≅ f.toFunctor ⋙ inverse :=
    e₁.symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft h.i.left.toFunctor e.unitIso)
        h.r.left.toFunctor ≪≫
      Functor.isoWhiskerRight si (e.inverse ⋙ h.r.left.toFunctor)
  let counit : inverse ⋙ f.toFunctor ≅ 𝟭 Y :=
    Functor.isoWhiskerLeft (h.i.right.toFunctor ⋙ e.inverse) sr ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft h.i.right.toFunctor e.counitIso)
        h.r.right.toFunctor ≪≫ e₂
  let result := CategoryTheory.Equivalence.mk f.toFunctor inverse unit counit
  exact show result.functor.IsEquivalence by infer_instance

instance stableRetracts : equivalences.{u}.IsStableUnderRetracts where
  of_retract := equivalence_of_retract

end DaggerNativeCatEquivalenceRetracts
