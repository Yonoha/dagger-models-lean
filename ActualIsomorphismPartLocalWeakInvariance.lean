import ActualSimplicialIsomorphismComponentMaps
import OriginalSimplicialPiZeroFunctor
import NativeSubcomplexWeakRestriction
import NativeConstantProjectionSubcomplexFibration

/-! ALL-isomorphism-component restriction preserves original local weak equivalences. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerOriginalSimplicialPiZeroCategory DaggerOriginalSimplicialPiZeroFunctor
open DaggerActualConstantSimplicialCategory DaggerActualSimplicialIsomorphismComponentPart
open DaggerActualSimplicialIsomorphismComponentMaps
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualIsomorphismPartLocalWeakInvariance
noncomputable section

local instance (C : SimplicialCat.{u, u}) :
    EnrichedCategory SSet.{u} (constant (componentObjects C)).Obj :=
  (constant (componentObjects C)).enriched

theorem inclusion_fibration (C : SimplicialCat.{u, u}) (x y : componentObjects C) :
    Fibration (homSubcomplex C x y).ι :=
  DaggerNativeConstantProjectionSubcomplexFibration.fibration (homSubcomplex C x y)
    ((projection C).map x y) (setOf (fun a : (x ⟶ y) ↦ IsIso a)) (fun _ _ ↦ Iff.rfl)

theorem mem_iff {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) (x y : componentObjects C)
    (q : SimplexCategoryᵒᵖ) (s : (C.enriched.Hom x y).obj q) :
    s ∈ (homSubcomplex C x y).obj q ↔
      (F.map x y).app q s ∈ (homSubcomplex D (F.obj x) (F.obj y)).obj q := by
  let h := componentFunctorFullyFaithful F hF
  have : (componentFunctor F).Full := h.full
  have : (componentFunctor F).Faithful := h.faithful
  change IsIso (((projection C).map x y).app q s) ↔
    IsIso (((projection D).map (F.obj x) (F.obj y)).app q ((F.map x y).app q s))
  rw [projection_map_apply]
  constructor
  · intro hs
    have := hs
    infer_instance
  · intro hs
    have := hs
    exact isIso_of_reflects_iso _ (componentFunctor F)

theorem hom_weak {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) (x y : componentObjects C) :
    WeakEquivalence ((map F).map x y) := by
  have := inclusion_fibration D (F.obj x) (F.obj y)
  have := hF x y
  exact DaggerNativeSubcomplexWeakRestriction.weakEquivalence (F.map x y)
    (homSubcomplex C x y) (homSubcomplex D (F.obj x) (F.obj y)) ((map F).map x y)
    rfl (mem_iff F hF x y)

end
end DaggerActualIsomorphismPartLocalWeakInvariance
