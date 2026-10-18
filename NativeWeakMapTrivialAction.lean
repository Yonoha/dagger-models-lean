import NativeUnitalMultiplicationAction

/-! Native weak maps of Kan complexes transport trivial based loop actions. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open SSet.KanComplex SSet.KanComplex.FundamentalGroupoid
open DaggerNativeUnitalMultiplicationAction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeWeakMapTrivialAction
noncomputable section

theorem trivial_action_of_weak {X Y : SSet.{u}} [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y) [WeakEquivalence f] (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (h : f.app _ x = y) (hX : TrivialActionAt X x) : TrivialActionAt Y y := by
  subst y
  have hw : W f := (SSet.weakEquivalence_iff_kanComplexW f).mp inferInstance
  have : (mapFundamentalGroupoid f).IsEquivalence := hw.isEquivalence
  intro n p s
  obtain ⟨p, rfl⟩ := (mapFundamentalGroupoid f).map_surjective
    (X := FundamentalGroupoid.mk x) (Y := FundamentalGroupoid.mk x) p
  obtain ⟨s, rfl⟩ := (hw.bijective n x _ rfl).surjective s
  have hn := congrFun ((actionMap f n).naturality p) s
  change mapπ f n x _ rfl (action.map p s) =
    action.map ((mapFundamentalGroupoid f).map p) (mapπ f n x _ rfl s) at hn
  rw [hX n p s] at hn
  exact hn.symm

theorem trivial_action_of_iso {X : SSet.{u}} [IsFibrant X]
    {x y : FundamentalGroupoid X} (e : x ≅ y) (hx : TrivialActionAt X x.pt) :
    TrivialActionAt X y.pt := by
  intro n p s
  obtain ⟨s, rfl⟩ := (action.bijective_map n e.hom).surjective s
  have he : (e.hom ≫ p ≫ e.inv) ≫ e.hom = e.hom ≫ p := by simp
  rw [← action.map_comp_apply, ← he, action.map_comp_apply, hx n _ s]

theorem all_trivial_actions_of_weak {X Y : SSet.{u}} [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y) [WeakEquivalence f] (hX : ∀ x : X _⦋0⦌, TrivialActionAt X x) :
    ∀ y : Y _⦋0⦌, TrivialActionAt Y y := by
  have hw : W f := (SSet.weakEquivalence_iff_kanComplexW f).mp inferInstance
  have : (mapFundamentalGroupoid f).IsEquivalence := hw.isEquivalence
  intro y
  let z := (mapFundamentalGroupoid f).objPreimage (FundamentalGroupoid.mk y)
  let e := (mapFundamentalGroupoid f).objObjPreimageIso (FundamentalGroupoid.mk y)
  exact trivial_action_of_iso e
    (trivial_action_of_weak f z.pt _ rfl (hX z.pt))

end
end DaggerNativeWeakMapTrivialAction
