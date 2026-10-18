import OriginalRealizedParameterActionCofibrations
import OriginalEC2ProductUnderlyingCofibrations

/-!
# Borel cofibrations of the literal original EC₂ generator products

Braiding identifies the native parameter-first action tensor with the
original EC₂-first ordinary product, including the original parameter arrow.
The proved Borel cofibrancy of the original EC₂ and the relative-function
lifting theorem give actual Borel cofibrations of the boundary and horn
products. The horn product is also the previously proved weak equivalence.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open scoped TopCat.modelCategory DaggerOriginalBorelModelCategory
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2RealizationAction
open DaggerOriginalEquivariantParameterTensor DaggerOriginalLocallyCompactTensorAdjunction
open DaggerOriginalLocallyCompactActionTensorAdjunction
open DaggerOriginalRealizedRelativeFunctionTrivialFibrations
open DaggerOriginalRealizedParameterActionCofibrations DaggerOriginalBorelModelConsequences
open DaggerOriginalBorelModelCategory DaggerOriginalTopCatProductDeformationRetract

universe u

namespace DaggerOriginalEC2ProductBorelCofibrations

noncomputable section

/-- Braiding retains the original first-factor action and trivial parameter action. -/
def parameterActionTensorIso (E : ContAction TopCat.{u} C2.{u})
    (K : LocallyCompactTopCat.{u}) :
    (locallyCompactActionTensor.obj K).obj E.obj ≅ parameterTensor E K.obj :=
  Action.mkIso (β_ K.obj E.obj.V) (by
    intro g
    apply ConcreteCategory.hom_ext
    intro p
    rfl)

/-- The braiding compares exactly the original parameter arrows in the action category. -/
def parameterActionTensorArrowIso (E : ContAction TopCat.{u} C2.{u})
    {A B : LocallyCompactTopCat.{u}} (i : A ⟶ B) :
    Arrow.mk ((locallyCompactActionTensor.map i).app E.obj) ≅
      Arrow.mk (parameterTensorMap E i.hom) :=
  Arrow.isoMk (parameterActionTensorIso E A) (parameterActionTensorIso E B) (by
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro p
    rfl)

/-- The literal original EC₂ parameter inclusion is Borel cofibrant as an action arrow. -/
theorem actualEC2ParameterProduct_cofibration {Y : SSet.{u}} (B : Y.Subcomplex)
    [LocallyCompactSpace (SSet.toTop.obj Y)]
    [LocallyCompactSpace (SSet.toTop.obj B.toSSet)] :
    Cofibration (parameterTensorMap realizedEC2ContinuousAction.{u} (SSet.toTop.map B.ι)) := by
  have : IsCofibrant realizedEC2ContinuousAction.{u}.obj := actualRealizedEC2_isCofibrant
  have h := realizedParameterTensor_cofibration B realizedEC2ContinuousAction.obj
  rw [cofibration_iff] at h ⊢
  exact (MorphismProperty.arrow_mk_iso_iff _
    (parameterActionTensorArrowIso realizedEC2ContinuousAction
      (realizedParameterInclusion B))).1 h

/-- The original EC₂ boundary product is a cofibration in the actual Borel action model. -/
theorem actualEC2BoundaryProduct_borelCofibration (n : ℕ) :
    Cofibration (parameterTensorMap realizedEC2ContinuousAction.{u}
      (SSet.toTop.map (SSet.boundary n).ι)) :=
  actualEC2ParameterProduct_cofibration _

/-- The original EC₂ horn product is a cofibration in the actual Borel action model. -/
theorem actualEC2HornProduct_borelCofibration (n : ℕ) (i : Fin (n + 2)) :
    Cofibration (parameterTensorMap realizedEC2ContinuousAction.{u}
      (SSet.toTop.map (SSet.horn (n + 1) i).ι)) :=
  actualEC2ParameterProduct_cofibration _

/-- The literal original EC₂ horn product is a Borel trivial cofibration. -/
theorem actualEC2HornProduct_borelTrivialCofibration (n : ℕ) (i : Fin (n + 2)) :
    trivialCofibrations (Action TopCat.{u} C2.{u})
      (parameterTensorMap realizedEC2ContinuousAction.{u}
        (SSet.toTop.map (SSet.horn (n + 1) i).ι)) :=
  (mem_trivialCofibrations_iff _).2
    ⟨actualEC2HornProduct_borelCofibration n i, actualEC2HornProduct_weakEquivalence n i⟩

end

end DaggerOriginalEC2ProductBorelCofibrations
