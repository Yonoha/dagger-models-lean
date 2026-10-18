import ActualGeneralRightConeKan

/-! The exact right-cone/opposite-left ISO respects ALL original target maps. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalCounitRightCone
open DaggerActualGeneralRightConeMapping DaggerNativeOppositeLeftMappingSimplex
open DaggerActualQuasicategoryMappingFibres
universe u
namespace DaggerActualGeneralRightConeKan
noncomputable section

def oppositeMap {X Y : SSet.{u}} (f : X ⟶ Y) (a b : X.obj (op ⦋0⦌)) :
    oppositeLeft X a b ⟶ oppositeLeft Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b) :=
  SSet.opFunctor.map (DaggerActualQuasicategoryMappingFibres.map (SSet.opFunctor.map f)
    ⦋0⦌ (SSet.opObjEquiv.symm b) (SSet.opObjEquiv.symm a))

theorem raw_target_natural {X Y : SSet.{u}} (f : X ⟶ Y) (a b : X.obj (op ⦋0⦌))
    (q : SimplexCategoryᵒᵖ) (s : (oppositeLeft X a b).obj q) :
    raw Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b) q ((oppositeMap f a b).app q s) =
      f.app (op ⦋q.unop.len + 1⦌) (raw X a b q s) := by
  exact (congrFun (f.naturality (DaggerNativeVertexJoinReversal.joinIso q.unop).inv.op)
    (rawLeft X a b q s)).symm

theorem inv_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (a b : X.obj (op ⦋0⦌)) :
    oppositeMap f a b ≫ (comparisonIso Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b)).inv =
      (comparisonIso X a b).inv ≫ DaggerActualGeneralRightConeMapping.map f a b := by
  apply NatTrans.ext
  funext q s
  apply Subtype.ext
  apply pushout.hom_ext
  · change simplexIncl q.unop.len ≫
        ((comparisonIso Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b)).inv.app q
          ((oppositeMap f a b).app q s)).val =
      simplexIncl q.unop.len ≫ (((comparisonIso X a b).inv.app q s).val ≫ f)
    calc
      _ = SSet.yonedaEquiv.symm (raw Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b) q
          ((oppositeMap f a b).app q s)) := inv_simplex_value _ _ _ q _
      _ = SSet.yonedaEquiv.symm (f.app (op ⦋q.unop.len + 1⦌) (raw X a b q s)) :=
        congrArg SSet.yonedaEquiv.symm (raw_target_natural f a b q s)
      _ = SSet.yonedaEquiv.symm (raw X a b q s) ≫ f :=
        (SSet.yonedaEquiv_symm_comp _ f).symm
      _ = (simplexIncl q.unop.len ≫ ((comparisonIso X a b).inv.app q s).val) ≫ f :=
        congrArg (fun h ↦ h ≫ f) (inv_simplex_value X a b q s).symm
      _ = _ := Category.assoc _ _ _
  · change baseIncl q.unop.len ≫
        ((comparisonIso Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b)).inv.app q
          ((oppositeMap f a b).app q s)).val =
      baseIncl q.unop.len ≫ (((comparisonIso X a b).inv.app q s).val ≫ f)
    rw [DaggerNativeRightConeSimplexPresentation.base_leg, ← Category.assoc,
      DaggerNativeRightConeSimplexPresentation.base_leg]
    exact (SSet.const_comp a f).symm

theorem hom_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (a b : X.obj (op ⦋0⦌)) :
    DaggerActualGeneralRightConeMapping.map f a b ≫
        (comparisonIso Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b)).hom =
      (comparisonIso X a b).hom ≫ oppositeMap f a b := by
  apply (cancel_mono (comparisonIso Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b)).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.assoc, inv_naturality,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end
end DaggerActualGeneralRightConeKan
