import NativeSimplicialPushoutTensorMono

/-! The SAME native relative internal Hom sends a mono parameter and a native
trivial-fibration target map to a trivial fibration, by the original pushout-tensor lifting.
-/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeRelativeIhomTrivialFibration
noncomputable section

theorem mono_left_trivial_right {K L X Y : SSet.{u}} (j : K ⟶ L) (p : X ⟶ Y)
    [Mono j] [Fibration p] [WeakEquivalence p] (r : SSet.PullbackIhom j p) :
    trivialFibrations SSet.{u} r.π := by
  rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
  rintro A B f ⟨n⟩
  let t : SSet.PushoutTensor j (SSet.boundary n).ι :=
    Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) j (SSet.boundary n).ι
  have : Mono t.ι := DaggerNativeSimplicialPushoutTensorMono.mono_ι j (SSet.boundary n).ι t
  have : Cofibration t.ι := (SSet.modelCategoryQuillen.cofibration_iff t.ι).mpr inferInstance
  exact (SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom t r).mp inferInstance

end
end DaggerNativeRelativeIhomTrivialFibration
