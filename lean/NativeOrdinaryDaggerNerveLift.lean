import NativeConstantCoherentDaggerCompatibility

/-! Lift the OLD constant coherent/ordinary nerve isomorphism to original dagger sets. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerNativeOrdinaryDaggerNerve DaggerActualConstantCoherentNerve
open DaggerNativeConstantCoherentDaggerCompatibility
universe u
namespace DaggerNativeOrdinaryDaggerNerveLift
noncomputable section
variable (A : Type u) [Category.{u} A] [DaggerCategory A]

/-- The ordinary dagger nerve has the SAME native ordinary nerve and reversed dagger chain. -/
def daggerNerve : DaggerSSet.{u} where
  toSSet := nerve A
  dagger := reversal A
  involutive n x := by
    have hinj : Function.Injective ((coherentNerveIso A).inv.app (op ⦋n⦌)) :=
      ((isIso_iff_bijective _).mp inferInstance).1
    apply hinj
    rw [inverse_reversal, inverse_reversal]
    exact (DaggerNerve.daggerCoherentNerve.obj
      (DaggerUnitaryDiscrete.ordinaryEnrichment A)).involutive n _
  fixedVertices x := by
    have hinj : Function.Injective ((coherentNerveIso A).inv.app (op ⦋0⦌)) :=
      ((isIso_iff_bijective _).mp inferInstance).1
    apply hinj
    rw [inverse_reversal]
    exact (DaggerNerve.daggerCoherentNerve.obj
      (DaggerUnitaryDiscrete.ordinaryEnrichment A)).fixedVertices _

/-- The whole OLD inverse now preserves the independently specified original dagger. -/
def inverse : daggerNerve A ⟶
    DaggerNerve.daggerCoherentNerve.obj (DaggerUnitaryDiscrete.ordinaryEnrichment A) where
  hom := (coherentNerveIso A).inv
  comm := inverse_comm A

/-- The whole OLD forward map also preserves that same dagger. -/
def forward :
    DaggerNerve.daggerCoherentNerve.obj (DaggerUnitaryDiscrete.ordinaryEnrichment A) ⟶
      daggerNerve A where
  hom := (coherentNerveIso A).hom
  comm := by
    let e := coherentNerveIso A
    apply (cancel_epi e.inv).mp
    change e.inv ≫ (e.hom ≫ reversal A) =
      e.inv ≫ ((DaggerNerve.daggerCoherentNerve.obj
        (DaggerUnitaryDiscrete.ordinaryEnrichment A)).dagger ≫ SSet.opFunctor.map e.hom)
    simp only [← Category.assoc, e.inv_hom_id, Category.id_comp]
    rw [inverse_comm, Category.assoc, ← SSet.opFunctor.map_comp, e.inv_hom_id]
    rfl

/-- No component of the old ordinary/coherent comparison is changed. -/
def comparisonIso :
    DaggerNerve.daggerCoherentNerve.obj (DaggerUnitaryDiscrete.ordinaryEnrichment A) ≅
      daggerNerve A where
  hom := forward A
  inv := inverse A
  hom_inv_id := by apply DaggerSSet.Hom.ext; exact (coherentNerveIso A).hom_inv_id
  inv_hom_id := by apply DaggerSSet.Hom.ext; exact (coherentNerveIso A).inv_hom_id

end
end DaggerNativeOrdinaryDaggerNerveLift
