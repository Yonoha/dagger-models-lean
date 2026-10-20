import OriginalActionForgetCofreeAdjunction
import OriginalBorelFreeGenerators

/-!
# Underlying cofibrations for the original Borel lifting class

The forgetful/cofree adjunction and native lifting against products show that
an original Borel cofibration is an actual native TopCat cofibration. This does
not assume an action model structure or a right Quillen mapping-space functor.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MorphismProperty HomotopicalAlgebra
open scoped TopCat.modelCategory
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2BorelCofibrancy
open DaggerOriginalActionForgetCofreeAdjunction DaggerOriginalBorelFreeGenerators

universe u

namespace DaggerOriginalBorelUnderlyingCofibrations

noncomputable section

/-- The cofree action on an underlying boundary-right-lifting map is Borel trivial fibrant. -/
theorem cofree_map_borelTrivialFibration {A B : TopCat.{u}} (p : A ⟶ B)
    (hp : TopCat.modelCategory.I.rlp p) :
    borelTrivialFibrations ((cofreeActionFunctor TopCat C2).map p) := by
  change TopCat.modelCategory.I.rlp ((cofreeActionFunctor TopCat C2).map p).hom
  rw [cofreeAction_map_hom]
  intro X Y i hi
  have : HasLiftingProperty i p := hp i hi
  exact inferInstance

/-- Every original Borel cofibration is an underlying native TopCat cofibration. -/
theorem borelCofibration_underlying {X Y : Action TopCat.{u} C2.{u}}
    (i : X ⟶ Y) (hi : borelCofibrations i) : Cofibration i.hom := by
  rw [cofibration_iff]
  change TopCat.modelCategory.I.rlp.llp i.hom
  intro A B p hp
  rw [forget_lifting_iff TopCat C2 i p]
  exact hi _ (cofree_map_borelTrivialFibration p hp)

/-- Every free-boundary generated cofibration is an underlying native TopCat cofibration. -/
theorem I_rlp_llp_underlying {X Y : Action TopCat.{u} C2.{u}}
    (i : X ⟶ Y) (hi : I.rlp.llp i) : Cofibration i.hom := by
  apply borelCofibration_underlying i
  rwa [I_rlp_llp_eq_borelCofibrations] at hi

/-- Every free-horn generated cofibration is an underlying native TopCat cofibration. -/
theorem J_rlp_llp_underlying {X Y : Action TopCat.{u} C2.{u}}
    (i : X ⟶ Y) (hi : J.rlp.llp i) : Cofibration i.hom :=
  I_rlp_llp_underlying i ((antitone_llp I_rlp_le_J_rlp) i hi)

end

end DaggerOriginalBorelUnderlyingCofibrations
