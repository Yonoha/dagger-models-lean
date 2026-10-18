import NativeWeakMapTrivialAction
import OriginalSimplicialCategoryGroupoidHomTransport
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-! All native loop actions on original Kan Homs vanish under the actual pi0 groupoid input. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite MonoidalCategory DaggerModels
open DaggerNativeUnitalMultiplicationAction DaggerNativeWeakMapTrivialAction
open DaggerOriginalSimplicialCategoryVertexComposition
open DaggerOriginalSimplicialCategoryGroupoidHomTransport DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerOriginalSimplicialPiZeroLaxMonoidal
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalHomLoopActionTrivial
noncomputable section

def identityVertex (C : SimplicialCat.{u, u}) (x : C.Obj) : (C.enriched.Hom x x) _⦋0⦌ :=
  (C.enriched.id x).app (op ⦋0⦌) PUnit.unit

theorem endomorphism_identity_action_trivial (C : SimplicialCat.{u, u}) (x : C.Obj)
    [(C.enriched.Hom x x).KanComplex] :
    TrivialActionAt (C.enriched.Hom x x) (identityVertex C x) := by
  apply unit_action_trivial (identityVertex C x) (C.enriched.comp x x x)
  · intro q a
    have h := congrFun (NatTrans.congr_app (precomposeVertex_id C x x) q) a
    change (C.enriched.comp x x x).app q
      (((SSet.unitHomEquiv _).symm (identityVertex C x)).app q PUnit.unit, a) = a at h
    rw [unitPoint_eq_const] at h
    exact h
  · intro q a
    have h := congrFun (NatTrans.congr_app (postcomposeVertex_id C x x) q) a
    change (C.enriched.comp x x x).app q
      (a, ((SSet.unitHomEquiv _).symm (identityVertex C x)).app q PUnit.unit) = a at h
    rw [unitPoint_eq_const] at h
    exact h

theorem precompose_identity_vertex (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y) _⦋0⦌) :
    (precomposeVertex C a y).app (op ⦋0⦌) (identityVertex C y) = a := by
  rw [precomposeVertex_apply, vertexPoint_zero]
  exact @Category.comp_id
    (DaggerOriginalSimplicialDegreeCategory.degreeObjects C (op ⦋0⦌))
    (DaggerOriginalSimplicialDegreeCategory.degreeCategory C (op ⦋0⦌)) x y a

theorem hom_action_trivial (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C)
    {x y : C.Obj} (a : (C.enriched.Hom x y) _⦋0⦌)
    [(C.enriched.Hom y y).KanComplex] [(C.enriched.Hom x y).KanComplex] :
    TrivialActionAt (C.enriched.Hom x y) a := by
  have : WeakEquivalence (precomposeVertex C a y) :=
    precomposeVertex_weakEquivalence_of_actualGroupoid C hC a y
  exact trivial_action_of_weak (precomposeVertex C a y) (identityVertex C y) a
    (precompose_identity_vertex C a) (endomorphism_identity_action_trivial C y)

end
end DaggerOriginalHomLoopActionTrivial
