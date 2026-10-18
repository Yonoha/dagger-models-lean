import OriginalSimplicialPiZeroFunctor
import OriginalAmbientDaggerPiZeroGroupoid
import OriginalLocalKanReplacementDiagonalWeak

/-! The actual pi0 groupoid condition is preserved and reflected by original local weak maps. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalSimplicialPiZeroCategory DaggerOriginalSimplicialPiZeroFunctor
open DaggerOriginalAmbientDaggerPiZeroGroupoid DaggerOriginalLocalKanReplacementDiagonalWeak
open OriginalOrdinaryLocalKanReplacement
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalPiZeroGroupoidLocalWeakInvariance
noncomputable section

theorem component_isIso (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C)
    {x y : componentObjects C} (f : x ⟶ y) : IsIso f := by
  obtain ⟨G, hG⟩ := hC
  have hi : ∀ {r s : componentObjects C} (a : r ⟶ s), IsIso a := by
    rw [← hG]
    intro r s a
    let g : Groupoid.{u, u} (componentObjects C) := G
    infer_instance
  exact hi f

theorem reflected {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y))
    (hD : HasActualComponentGroupoid D) : HasActualComponentGroupoid C := by
  let h := componentFunctorFullyFaithful F hF
  have : (componentFunctor F).Full := h.full
  have : (componentFunctor F).Faithful := h.faithful
  refine ⟨Groupoid.ofIsIso (fun {x y} a ↦ ?_), rfl⟩
  have : IsIso ((componentFunctor F).map a) := component_isIso D hD _
  exact isIso_of_reflects_iso a (componentFunctor F)

theorem preserved {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hO : Function.Surjective F.obj)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y))
    (hC : HasActualComponentGroupoid C) : HasActualComponentGroupoid D := by
  have hi : ∀ {x y : componentObjects D} (f : x ⟶ y), IsIso f := by
    intro x y f
    obtain ⟨x, rfl⟩ := hO x
    obtain ⟨y, rfl⟩ := hO y
    obtain ⟨a, rfl⟩ := (componentMap_bijective F hF x y).surjective f
    have : IsIso a := component_isIso C hC a
    infer_instance
  exact ⟨Groupoid.ofIsIso hi, rfl⟩

theorem groupoid_iff {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hO : Function.Surjective F.obj)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) :
    HasActualComponentGroupoid C ↔ HasActualComponentGroupoid D :=
  ⟨preserved F hO hF, reflected F hF⟩

theorem replacement_groupoid_iff (C : SimplicialCat.{u, u}) :
    HasActualComponentGroupoid C ↔ HasActualComponentGroupoid (replacement.obj C) :=
  groupoid_iff (unit.app C) (unit_obj_bijective C).surjective (unit_hom_weak C)

end
end DaggerOriginalPiZeroGroupoidLocalWeakInvariance
