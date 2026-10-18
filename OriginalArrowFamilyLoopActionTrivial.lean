import OriginalHomLoopActionTrivial
import NativeFinitePiHomotopyAction
import OriginalNerveRowChainData

/-! Native loop actions on all original finite row-arrow families vanish. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite DaggerModels
open DaggerOriginalAmbientDaggerPiZeroGroupoid DaggerOriginalHomLoopActionTrivial
open DaggerNativeUnitalMultiplicationAction DaggerNativeWeakMapTrivialAction
open DaggerNativeFinitePiWeak DaggerNativeFinitePiKan DaggerNativeFinitePiHomotopyAction
open DaggerOriginalNerveRowChainData
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalArrowFamilyLoopActionTrivial
noncomputable section

instance arrowFamily_fibrant (C : SimplicialCat.{u, u})
    [∀ x y : C.Obj, IsFibrant (C.enriched.Hom x y)]
    {k : ℕ} (O : Fin (k + 1) → C.Obj) : IsFibrant (arrowFamily C O) :=
  finitePi_kan (fun i : Fin k ↦ C.enriched.Hom (O i.castSucc) (O i.succ))
    (fun _ ↦ inferInstance)

theorem arrow_family_actions_trivial (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) [∀ x y : C.Obj, IsFibrant (C.enriched.Hom x y)]
    {k : ℕ} (O : Fin (k + 1) → C.Obj) (a : (arrowFamily C O) _⦋0⦌) :
    TrivialActionAt (arrowFamily C O) a := by
  let X : Fin k → SSet.{u} := fun i ↦ C.enriched.Hom (O i.castSucc) (O i.succ)
  letI : ∀ i, IsFibrant (X i) := fun _ ↦ inferInstance
  letI : IsFibrant (piObject X) := finitePi_kan X (fun _ ↦ inferInstance)
  apply product_action_trivial X a
  intro i
  exact hom_action_trivial C hC (a i)

theorem realized_arrow_family_actions_trivial (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) [∀ x y : C.Obj, IsFibrant (C.enriched.Hom x y)]
    {k : ℕ} (O : Fin (k + 1) → C.Obj) :
    ∀ a : (TopCat.toSSet.obj (SSet.toTop.obj (arrowFamily C O))) _⦋0⦌,
      TrivialActionAt (TopCat.toSSet.obj (SSet.toTop.obj (arrowFamily C O))) a :=
  all_trivial_actions_of_weak (sSetTopAdj.unit.app (arrowFamily C O))
    (arrow_family_actions_trivial C hC O)

end
end DaggerOriginalArrowFamilyLoopActionTrivial
