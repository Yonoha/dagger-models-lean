import ActualRightConeTrivialBoundaryLifting
import NativeJoyalWeakTrivialFibrationSpan

/-! The SAME native right mapping spaces preserve weak equivalences between ALL quasi-categories. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerActualGeneralRightConeMapping
open DaggerActualRightConeTrivialBoundaryLifting
open DaggerNativeJoyalMappingTest DaggerNativeJoyalWeakTrivialFibrationSpan
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualRightMappingWeakInvariance
noncomputable section

def mapTo {X Y : SSet.{u}} (f : X ⟶ Y) (a b : X.obj (op ⦋0⦌))
    (c d : Y.obj (op ⦋0⦌)) (hc : f.app (op ⦋0⦌) a = c) (hd : f.app (op ⦋0⦌) b = d) :
    rightMapping X a b ⟶ rightMapping Y c d where
  app q s := ⟨s.val ≫ f,
    (congrArg (f.app (op ⦋0⦌)) s.property.1).trans hc,
    (congrArg (f.app (op ⦋0⦌)) s.property.2).trans hd⟩
  naturality q r α := by
    funext s
    apply Subtype.ext
    exact Category.assoc _ _ _

theorem mapTo_weak_of_mono_rlp {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : (MorphismProperty.monomorphisms SSet.{u}).rlp f)
    (a b : X.obj (op ⦋0⦌)) (c d : Y.obj (op ⦋0⦌))
    (hc : f.app (op ⦋0⦌) a = c) (hd : f.app (op ⦋0⦌) b = d) :
    WeakEquivalence (mapTo f a b c d hc hd) := by
  subst c
  subst d
  change WeakEquivalence (DaggerActualGeneralRightConeMapping.map f a b)
  exact ((mem_trivialFibrations_iff _).mp (map_trivial_fibration f a b hf)).2

theorem map_weak_of_categorical_weak {X Y : SSet.{u}}
    [X.Quasicategory] [Y.Quasicategory] (f : X ⟶ Y)
    (hf : weakCategoricalEquivalences f) (a b : X.obj (op ⦋0⦌)) :
    WeakEquivalence (DaggerActualGeneralRightConeMapping.map f a b) := by
  let d := fromWeak f hf
  let a' := d.inclusion.app (op ⦋0⦌) a
  let b' := d.inclusion.app (op ⦋0⦌) b
  have hpa : d.left.app (op ⦋0⦌) a' = a :=
    congrFun (NatTrans.congr_app d.inclusion_left (op ⦋0⦌)) a
  have hpb : d.left.app (op ⦋0⦌) b' = b :=
    congrFun (NatTrans.congr_app d.inclusion_left (op ⦋0⦌)) b
  have hqa : d.right.app (op ⦋0⦌) a' = f.app (op ⦋0⦌) a :=
    congrFun (NatTrans.congr_app d.inclusion_right (op ⦋0⦌)) a
  have hqb : d.right.app (op ⦋0⦌) b' = f.app (op ⦋0⦌) b :=
    congrFun (NatTrans.congr_app d.inclusion_right (op ⦋0⦌)) b
  let J := DaggerActualGeneralRightConeMapping.map d.inclusion a b
  let P := mapTo d.left a' b' a b hpa hpb
  let Q := mapTo d.right a' b' (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b) hqa hqb
  have : WeakEquivalence P :=
    mapTo_weak_of_mono_rlp d.left d.left_mono_rlp a' b' a b hpa hpb
  have : WeakEquivalence Q :=
    mapTo_weak_of_mono_rlp d.right d.right_mono_rlp a' b'
      (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b) hqa hqb
  have hleft : J ≫ P = 𝟙 (rightMapping X a b) := by
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    change (s.val ≫ d.inclusion) ≫ d.left = s.val
    rw [Category.assoc, d.inclusion_left, Category.comp_id]
  have hright : J ≫ Q = DaggerActualGeneralRightConeMapping.map f a b := by
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    change (s.val ≫ d.inclusion) ≫ d.right = s.val ≫ f
    rw [Category.assoc, d.inclusion_right]
  have : WeakEquivalence J := weakEquivalence_of_postcomp_of_fac hleft
  rw [← hright]
  infer_instance

end
end DaggerActualRightMappingWeakInvariance
