import OriginalStrictSimplicialPiZeroGroupoid
import OriginalFixedObjectPiZeroEquivalence
import OriginalFixedObjectGroupoidCompletionAdjunction

/-!
# Necessary pi0 groupoid condition for the actual groupoid-completion unit

A full original local weak equivalence induces a fully faithful actual pi0
functor. If its target is a strict simplicial groupoid, the target pi0 category
is a groupoid. Native reflection of isomorphisms therefore gives a groupoid
structure on the original source pi0 category. This proves the only-if part
of DK80 Proposition 9.5 for the actual original localization, without a
cofibrancy assumption. The converse and higher homotopy comparison remain.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalSimplicialPiZeroCategory DaggerOriginalSimplicialPiZeroFunctor
open DaggerOriginalStrictSimplicialPiZeroGroupoid
open DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectGroupoidCompletionAdjunction
open DaggerOriginalFixedObjectAmbientDaggerModel DaggerOriginalAmbientDaggerPiZeroGroupoid
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerOriginalCompletionWeakNecessity
noncomputable section

/-- Local weakness into a strict target forces the actual source pi0 category to be a groupoid. -/
def componentGroupoid_of_localWeak {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hD : IsStrictGroupoid D) (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) :
    Groupoid.{u, u} (componentObjects C) := by
  have h := componentFunctorFullyFaithful F hF
  have : (componentFunctor F).Full := h.full
  have : (componentFunctor F).Faithful := h.faithful
  exact Groupoid.ofIsIso (fun {x y} a ↦ by
    have : IsIso ((componentFunctor F).map a) :=
      componentIsIso_of_strict D hD ((componentFunctor F).map a)
    exact isIso_of_reflects_iso a (componentFunctor F))

/-- The source groupoid retains the entire original component category. -/
theorem componentGroupoid_of_localWeak_category {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hD : IsStrictGroupoid D) (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) :
    (componentGroupoid_of_localWeak F hD hF).toCategory = componentCategory C := rfl

/-- The exact native localization can be locally weak only when the original pi0 is a groupoid. -/
theorem localizationWeak_implies_actualPiZeroGroupoid (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, WeakEquivalence ((localization C).map x y)) :
    HasActualComponentGroupoid C :=
  ⟨componentGroupoid_of_localWeak (localization C) (completion_isStrictGroupoid C) hC, rfl⟩

/-- The actual fixed-object dagger localization satisfies the same necessary condition. -/
theorem daggerLocalizationWeak_implies_actualPiZeroGroupoid {O : Type u}
    (H : FixedDaggerCategory O) [WeakEquivalence (fixedDaggerLocalization H)] :
    HasActualComponentGroupoid (original O H.underlying) := by
  apply localizationWeak_implies_actualPiZeroGroupoid (original O H.underlying)
  exact (weakEquivalence_iff_original (fixedDaggerLocalization H)).1 inferInstance

end
end DaggerOriginalCompletionWeakNecessity
