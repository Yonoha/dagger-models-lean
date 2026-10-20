import NativeGroupoidCompletionNerveBaseCases

/-! Mathlib's ACTUAL free-groupoid unit on nerves is closed under exact category retracts. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeCategoryCompletionNerveRetracts
noncomputable section

def completionNerve : Cat.{u, u} ⥤ SSet.{u} :=
  Grpd.free ⋙ Grpd.forgetToCat ⋙ nerveFunctor

def unit : nerveFunctor.{u} ⟶ completionNerve :=
  Functor.whiskerRight Grpd.freeForgetAdjunction.unit nerveFunctor

theorem unit_app (C : Type u) [Category.{u} C] :
    unit.app (Cat.of C) = nerveMap (FreeGroupoid.of C) := rfl

def unitRetract {C D : Cat.{u, u}} (i : C ⟶ D) (r : D ⟶ C) (hi : i ≫ r = 𝟙 C) :
    RetractArrow (unit.app C) (unit.app D) where
  i := Arrow.homMk (nerveFunctor.map i) (completionNerve.map i) (unit.naturality i)
  r := Arrow.homMk (nerveFunctor.map r) (completionNerve.map r) (unit.naturality r)
  retract := by
    apply Arrow.hom_ext
    · change nerveFunctor.map i ≫ nerveFunctor.map r = 𝟙 _
      rw [← CategoryTheory.Functor.map_comp, hi, CategoryTheory.Functor.map_id]
    · change completionNerve.map i ≫ completionNerve.map r = 𝟙 _
      rw [← CategoryTheory.Functor.map_comp, hi, CategoryTheory.Functor.map_id]

theorem unit_weak_of_retract {C D : Cat.{u, u}} (i : C ⟶ D) (r : D ⟶ C)
    (hi : i ≫ r = 𝟙 C) (hD : WeakEquivalence (unit.app D)) :
    WeakEquivalence (unit.app C) := by
  have := hD
  exact ⟨MorphismProperty.of_retract (unitRetract i r hi) (mem_weakEquivalences (unit.app D))⟩

theorem unit_weak_of_iso {C D : Cat.{u, u}} (e : C ≅ D)
    (hD : WeakEquivalence (unit.app D)) : WeakEquivalence (unit.app C) :=
  unit_weak_of_retract e.hom e.inv e.hom_inv_id hD

end
end DaggerNativeCategoryCompletionNerveRetracts
