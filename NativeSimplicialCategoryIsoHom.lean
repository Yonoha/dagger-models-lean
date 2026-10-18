import ActualKanRigidificationCompletionWeak
import Mathlib.CategoryTheory.NatIso

/-! An isomorphism of the ORIGINAL enriched categories induces isomorphisms of all Hom spaces. -/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerOriginalSimplicialDegreeCategory
universe u
namespace DaggerNativeSimplicialCategoryIsoHom
noncomputable section

def degreeEquivalence {C D : SimplicialCat.{u, u}} (e : C ≅ D)
    (q : SimplexCategoryᵒᵖ) : degreeObjects C q ≌ degreeObjects D q :=
  CategoryTheory.Equivalence.mk (degreeFunctor e.hom q) (degreeFunctor e.inv q)
    (eqToIso (congrArg (fun F : C ⟶ C ↦ degreeFunctor F q) e.hom_inv_id.symm))
    (eqToIso (congrArg (fun F : D ⟶ D ↦ degreeFunctor F q) e.inv_hom_id))

theorem hom_app_isIso {C D : SimplicialCat.{u, u}} (e : C ≅ D) (x y : C.Obj)
    (q : SimplexCategoryᵒᵖ) : IsIso ((e.hom.map x y).app q) := by
  have : (degreeFunctor e.hom q).Full :=
    inferInstanceAs (degreeEquivalence e q).functor.Full
  have : (degreeFunctor e.hom q).Faithful :=
    inferInstanceAs (degreeEquivalence e q).functor.Faithful
  exact (isIso_iff_bijective _).2
    ⟨(degreeFunctor e.hom q).map_injective, (degreeFunctor e.hom q).map_surjective⟩

theorem hom_isIso {C D : SimplicialCat.{u, u}} (e : C ≅ D) (x y : C.Obj) :
    IsIso (e.hom.map x y) := by
  have (q : SimplexCategoryᵒᵖ) : IsIso ((e.hom.map x y).app q) := hom_app_isIso e x y q
  exact NatIso.isIso_of_isIso_app _

end
end DaggerNativeSimplicialCategoryIsoHom
