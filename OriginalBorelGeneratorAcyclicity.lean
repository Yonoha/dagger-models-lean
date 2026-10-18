import OriginalBorelUnderlyingCofibrations
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Actual underlying acyclicity of the free-horn lifting class

The cofree action preserves the underlying native fibration class. Consequently,
every map with left lifting against the free-horn right class is an underlying
native trivial cofibration, without assuming the Borel model structure.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MorphismProperty HomotopicalAlgebra
open scoped TopCat.modelCategory
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalBorelFreeGenerators
open DaggerOriginalActionForgetCofreeAdjunction

universe u

namespace DaggerOriginalBorelGeneratorAcyclicity

noncomputable section

/-- Cofree actions preserve the literal underlying native fibration class. -/
theorem cofree_map_J_rlp {A B : TopCat.{u}} (p : A ⟶ B)
    (hp : TopCat.modelCategory.J.rlp p) :
    J.rlp ((cofreeActionFunctor TopCat C2).map p) := by
  rw [J_rlp_iff, cofreeAction_map_hom]
  intro X Y i hi
  have : HasLiftingProperty i p := hp i hi
  exact inferInstance

/-- Left lifting against free-horn right lifting gives an underlying native trivial cofibration. -/
theorem J_rlp_llp_underlying_trivialCofibration {X Y : Action TopCat.{u} C2.{u}}
    (i : X ⟶ Y) (hi : J.rlp.llp i) :
    (trivialCofibrations TopCat.{u}) i.hom := by
  rw [TopCat.modelCategory.trivialCofibrations_eq_llp_rlp]
  intro A B p hp
  rw [forget_lifting_iff TopCat C2 i p]
  exact hi _ (cofree_map_J_rlp p hp)

/-- In particular the free-horn generated left class is an actual underlying weak equivalence. -/
theorem J_rlp_llp_underlying_weakEquivalence {X Y : Action TopCat.{u} C2.{u}}
    (i : X ⟶ Y) (hi : J.rlp.llp i) : WeakEquivalence i.hom :=
  (mem_trivialCofibrations_iff i.hom).1 (J_rlp_llp_underlying_trivialCofibration i hi) |>.2

end

end DaggerOriginalBorelGeneratorAcyclicity
