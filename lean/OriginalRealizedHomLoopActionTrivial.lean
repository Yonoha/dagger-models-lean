import OriginalHomLoopActionTrivial
import OriginalPiZeroGroupoidLocalWeakInvariance

/-! Native based loop actions vanish at every singular vertex of the original realized Hom. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite DaggerModels
open DaggerOriginalAmbientDaggerPiZeroGroupoid DaggerOriginalHomLoopActionTrivial
open DaggerNativeUnitalMultiplicationAction DaggerNativeWeakMapTrivialAction
open DaggerOriginalPiZeroGroupoidLocalWeakInvariance OriginalOrdinaryLocalKanReplacement
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalRealizedHomLoopActionTrivial
noncomputable section

abbrev realizedSingularHom (C : SimplicialCat.{u, u}) (x y : C.Obj) : SSet.{u} :=
  TopCat.toSSet.obj (SSet.toTop.obj (C.enriched.Hom x y))

theorem realized_hom_actions_trivial (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C)
    (hH : ∀ x y : C.Obj, (C.enriched.Hom x y).KanComplex) (x y : C.Obj) :
    ∀ a : (realizedSingularHom C x y) _⦋0⦌,
      TrivialActionAt (realizedSingularHom C x y) a := by
  have := hH x y
  have := hH y y
  apply all_trivial_actions_of_weak (sSetTopAdj.unit.app (C.enriched.Hom x y))
  intro a
  exact hom_action_trivial C hC a

theorem replacement_realized_hom_actions_trivial (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (x y : (replacement.obj C).Obj) :
    ∀ a : (realizedSingularHom (replacement.obj C) x y) _⦋0⦌,
      TrivialActionAt (realizedSingularHom (replacement.obj C) x y) a :=
  realized_hom_actions_trivial (replacement.obj C) ((replacement_groupoid_iff C).mp hC)
    (replacement_locallyKan C) x y

end
end DaggerOriginalRealizedHomLoopActionTrivial
