import NativeRelativeInnerHornNerveLifting
import NativeInnerHornFactorization
import OriginalOrdinaryLocalFibrations
import OriginalOrdinaryHornObjectBijections
import OriginalOrdinaryHornLeftClassAnodyneReconciled
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-! Original rigidification sends full inner-left maps to the original enriched horn left class. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerNativeInnerHornFactorization
open scoped Simplicial SSet.modelCategoryQuillen
universe u
namespace DaggerActualInnerAnodyneRigidification
noncomputable section

theorem nerve_map_innerFibration {C B : SimplicialCat.{u, u}} (p : C ⟶ B)
    (hp : ∀ x y : C.Obj, Fibration (p.map x y)) : innerFibrations (coherentNerve.map p) := by
  rw [innerFibrations_iff]
  intro n i h0 hn
  exact DaggerNativeRelativeInnerHornNerveLifting.innerHorn_lifting
    (n := n + 1) ⟨i, h0, hn⟩ p hp

theorem rigidification_lifting {X Y : SSet.{u}} (i : X ⟶ Y) (hi : innerAnodyne i)
    {C B : SimplicialCat.{u, u}} (p : C ⟶ B)
    (hp : ∀ x y : C.Obj, Fibration (p.map x y)) :
    HasLiftingProperty (rigidification.map i) p :=
  (rigidificationCoherentNerveAdjunction.hasLiftingProperty_iff i p).2
    (hi (coherentNerve.map p) (nerve_map_innerFibration p hp))

theorem rigidification_hornLeft {X Y : SSet.{u}} (i : X ⟶ Y) (hi : innerAnodyne i) :
    OriginalOrdinaryHornGenerators.generators.rlp.llp (rigidification.map i) := by
  intro C B p hp
  exact rigidification_lifting i hi p
    ((OriginalOrdinaryLocalFibrations.generators_rlp_iff p).1 hp)

theorem hom_anodyne {X Y : SSet.{u}} (i : X ⟶ Y) (hi : innerAnodyne i)
    (a b : (rigidification.obj X).Obj) :
    SSet.anodyneExtensions ((rigidification.map i).map a b) :=
  OriginalOrdinaryHornLeftClassAnodyne.hornLeft_hom_anodyne _
    (rigidification_hornLeft i hi) a b

theorem hom_mono {X Y : SSet.{u}} (i : X ⟶ Y) (hi : innerAnodyne i)
    (a b : (rigidification.obj X).Obj) : Mono ((rigidification.map i).map a b) :=
  OriginalOrdinaryHornLeftClassAnodyne.hornLeft_hom_mono _
    (rigidification_hornLeft i hi) a b

theorem hom_weak {X Y : SSet.{u}} (i : X ⟶ Y) (hi : innerAnodyne i)
    (a b : (rigidification.obj X).Obj) :
    WeakEquivalence ((rigidification.map i).map a b) :=
  ((mem_trivialCofibrations_iff _).1
    ((DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).1
      (hom_anodyne i hi a b))).2

theorem object_bijective {X Y : SSet.{u}} (i : X ⟶ Y) (hi : innerAnodyne i) :
    Function.Bijective (rigidification.map i).obj :=
  OriginalOrdinaryHornObjectBijections.object_bijective_of_generators_rlp_llp _
    (rigidification_hornLeft i hi)

end
end DaggerActualInnerAnodyneRigidification
