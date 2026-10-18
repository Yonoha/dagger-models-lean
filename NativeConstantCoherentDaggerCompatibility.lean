import NativeOrdinaryDaggerNerve

/-! The OLD constant coherent-nerve inverse intertwines the SAME original dagger. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerActualConstantCoherentNerve DaggerNativeOrdinaryDaggerNerve
universe u
namespace DaggerNativeConstantCoherentDaggerCompatibility
noncomputable section
variable (A : Type u) [Category.{u} A] [DaggerCategory A]

/-- Both full maps are the old coherent inverse and the native reversed ordinary chain. -/
theorem inverse_comm :
    (coherentNerveIso A).inv ≫
        (DaggerNerve.daggerCoherentNerve.obj (DaggerUnitaryDiscrete.ordinaryEnrichment A)).dagger =
      reversal A ≫ SSet.opFunctor.map (coherentNerveIso A).inv := by
  apply NatTrans.ext
  funext q F
  apply ULift.ext
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro i j
  simp only [eqToHom_refl, Category.comp_id]

/-- The same full intertwining equality evaluated on an arbitrary original chain. -/
theorem inverse_reversal (n : SimplexCategoryᵒᵖ) (F : (nerve A).obj n) :
    (coherentNerveIso A).inv.app n (SSet.opObjEquiv ((reversal A).app n F)) =
      SSet.opObjEquiv
        ((DaggerNerve.daggerCoherentNerve.obj
          (DaggerUnitaryDiscrete.ordinaryEnrichment A)).dagger.app n
            ((coherentNerveIso A).inv.app n F)) :=
  (congrFun (NatTrans.congr_app (inverse_comm A) n) F).symm

end
end DaggerNativeConstantCoherentDaggerCompatibility
