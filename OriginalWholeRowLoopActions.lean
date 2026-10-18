import NativeFamilyLoopAction
import NativeBinaryProductLoopAction
import OriginalArrowFamilyLoopActionTrivial
import OriginalBarRowFullData
import OriginalRealizedHomLoopActionTrivial

/-! All original full base and bar rows retain their actual native based loop actions. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite MonoidalCategory DaggerModels
open DaggerOriginalAmbientDaggerPiZeroGroupoid DaggerOriginalHomLoopActionTrivial
open DaggerNativeUnitalMultiplicationAction DaggerNativeWeakMapTrivialAction
open DaggerOriginalProductGadget DaggerNativeFamilyLoopAction
open DaggerNativeBinaryProductLoopAction DaggerOriginalArrowFamilyLoopActionTrivial
open DaggerOriginalNerveRowChainData DaggerOriginalBarRowFullData
open DaggerOriginalSimplicialCategoryBarRows DaggerOriginalPiZeroGroupoidLocalWeakInvariance
open OriginalOrdinaryLocalKanReplacement
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalWholeRowLoopActions
noncomputable section

instance base_row_fibrant (C : SimplicialCat.{u, u})
    [∀ x y : C.Obj, IsFibrant (C.enriched.Hom x y)] (k : ℕ) :
    IsFibrant (baseRow C k) := by
  have : IsFibrant (chainRows C k) := family_fibrant (arrowFamily C)
  exact isFibrant_of_fibration (rowChainIso C k).hom

instance bar_row_fibrant (C : SimplicialCat.{u, u})
    [∀ x y : C.Obj, IsFibrant (C.enriched.Hom x y)] (z : C.Obj) (k : ℕ) :
    IsFibrant (barRow C z k) := by
  letI : ∀ O : Fin (k + 1) → C.Obj,
      IsFibrant (arrowFamily C O ⊗ C.enriched.Hom (O (Fin.last k)) z) :=
    fun O ↦ tensor_fibrant _ _
  have : IsFibrant (barRowFamily C z k) := family_fibrant _
  exact isFibrant_of_fibration (barRowDataIso C z k).hom

theorem base_row_actions_trivial (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) [∀ x y : C.Obj, IsFibrant (C.enriched.Hom x y)]
    (k : ℕ) : ∀ a : (baseRow C k) _⦋0⦌, TrivialActionAt (baseRow C k) a := by
  have : IsFibrant (chainRows C k) := family_fibrant (arrowFamily C)
  apply all_trivial_actions_of_weak (rowChainIso C k).inv
  exact family_actions_trivial (arrowFamily C) (arrow_family_actions_trivial C hC)

theorem bar_row_actions_trivial (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) [∀ x y : C.Obj, IsFibrant (C.enriched.Hom x y)]
    (z : C.Obj) (k : ℕ) :
    ∀ a : (barRow C z k) _⦋0⦌, TrivialActionAt (barRow C z k) a := by
  letI : ∀ O : Fin (k + 1) → C.Obj,
      IsFibrant (arrowFamily C O ⊗ C.enriched.Hom (O (Fin.last k)) z) :=
    fun O ↦ tensor_fibrant _ _
  have : IsFibrant (barRowFamily C z k) := family_fibrant _
  apply all_trivial_actions_of_weak (barRowDataIso C z k).inv
  apply family_actions_trivial
  intro O
  exact tensor_actions_trivial _ _ (arrow_family_actions_trivial C hC O)
    (fun a ↦ hom_action_trivial C hC a)

theorem realized_base_row_actions_trivial (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) [∀ x y : C.Obj, IsFibrant (C.enriched.Hom x y)]
    (k : ℕ) : ∀ a : (TopCat.toSSet.obj (SSet.toTop.obj (baseRow C k))) _⦋0⦌,
      TrivialActionAt (TopCat.toSSet.obj (SSet.toTop.obj (baseRow C k))) a :=
  all_trivial_actions_of_weak (sSetTopAdj.unit.app (baseRow C k))
    (base_row_actions_trivial C hC k)

theorem realized_bar_row_actions_trivial (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) [∀ x y : C.Obj, IsFibrant (C.enriched.Hom x y)]
    (z : C.Obj) (k : ℕ) :
    ∀ a : (TopCat.toSSet.obj (SSet.toTop.obj (barRow C z k))) _⦋0⦌,
      TrivialActionAt (TopCat.toSSet.obj (SSet.toTop.obj (barRow C z k))) a :=
  all_trivial_actions_of_weak (sSetTopAdj.unit.app (barRow C z k))
    (bar_row_actions_trivial C hC z k)

theorem replacement_realized_base_row_actions_trivial (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (k : ℕ) :
    ∀ a : (TopCat.toSSet.obj (SSet.toTop.obj (baseRow (replacement.obj C) k))) _⦋0⦌,
      TrivialActionAt (TopCat.toSSet.obj (SSet.toTop.obj
        (baseRow (replacement.obj C) k))) a := by
  letI : ∀ x y : (replacement.obj C).Obj,
      IsFibrant ((replacement.obj C).enriched.Hom x y) := replacement_locallyKan C
  exact realized_base_row_actions_trivial (replacement.obj C)
    ((replacement_groupoid_iff C).mp hC) k

theorem replacement_realized_bar_row_actions_trivial (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (z : (replacement.obj C).Obj) (k : ℕ) :
    ∀ a : (TopCat.toSSet.obj (SSet.toTop.obj (barRow (replacement.obj C) z k))) _⦋0⦌,
      TrivialActionAt (TopCat.toSSet.obj (SSet.toTop.obj
        (barRow (replacement.obj C) z k))) a := by
  letI : ∀ x y : (replacement.obj C).Obj,
      IsFibrant ((replacement.obj C).enriched.Hom x y) := replacement_locallyKan C
  exact realized_bar_row_actions_trivial (replacement.obj C)
    ((replacement_groupoid_iff C).mp hC) z k

end
end DaggerOriginalWholeRowLoopActions
