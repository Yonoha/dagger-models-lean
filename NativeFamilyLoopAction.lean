import NativeCoproductLoopActionTrivial

/-! The exact old pointwise family inherits Kan fibrancy and its original based actions. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite HomotopicalAlgebra
open DaggerOriginalProductGadget DaggerNativeUnitalMultiplicationAction
open DaggerNativeCoproductLoopActionTrivial DaggerNativeWeakMapTrivialAction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeFamilyLoopAction
noncomputable section

instance family_fibrant {I : Type u} (X : I → SSet.{u}) [∀ i, IsFibrant (X i)] :
    IsFibrant (familySSet X) := isFibrant_of_fibration (familySigmaIso X).inv

theorem family_actions_trivial {I : Type u} (X : I → SSet.{u})
    [∀ i, IsFibrant (X i)] (hX : ∀ i x, TrivialActionAt (X i) x) :
    ∀ a : (familySSet X) _⦋0⦌, TrivialActionAt (familySSet X) a :=
  all_trivial_actions_of_weak (familySigmaIso X).hom (coproduct_actions_trivial X hX)

theorem realized_family_actions_trivial {I : Type u} (X : I → SSet.{u})
    [∀ i, IsFibrant (X i)] (hX : ∀ i x, TrivialActionAt (X i) x) :
    ∀ a : (TopCat.toSSet.obj (SSet.toTop.obj (familySSet X))) _⦋0⦌,
      TrivialActionAt (TopCat.toSSet.obj (SSet.toTop.obj (familySSet X))) a :=
  all_trivial_actions_of_weak (sSetTopAdj.unit.app (familySSet X))
    (family_actions_trivial X hX)

end
end DaggerNativeFamilyLoopAction
