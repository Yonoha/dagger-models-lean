import ActualDaggerIsomorphismComponentMaps
import ActualIsomorphismPartFibrancy

/-! Keep the original dagger maps while restricting all weak Hom maps and locally Kan objects. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualDaggerIsomorphismPartLocalWeak
noncomputable section

theorem hom_weak {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) (x y : C.Obj) :
    WeakEquivalence ((DaggerActualDaggerIsomorphismComponentMaps.map F).map x y) :=
  DaggerActualIsomorphismPartLocalWeakInvariance.hom_weak F.toEnrichedFunctor hF x y

theorem locallyKan (C : DaggerSimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y)) (x y : C.Obj) :
    SSet.KanComplex
      ((DaggerActualDaggerIsomorphismComponentPart.part C).enriched.Hom x y) :=
  DaggerActualIsomorphismPartFibrancy.locallyKan C.toSimplicialCat hC x y

end
end DaggerActualDaggerIsomorphismPartLocalWeak
