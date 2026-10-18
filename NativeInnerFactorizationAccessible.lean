import NativeSSetLocallyPresentable
import NativeInnerHornFactorization
import OriginalSOAFactorizationRecovered

/-!
# The original whole inner-horn factorization is finitely accessible

Both ends of every actual inner-horn generator are finitely presentable.
The retained generic small-object accessibility theorem applies to the exact
existing factorization, definitionally, with the original aleph-zero iteration.
-/
set_option autoImplicit false
open CategoryTheory DaggerNativeInnerHornFactorization
universe u
namespace DaggerNativeInnerFactorizationAccessible
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0
attribute [local instance] DaggerModels.SmallObjectFiniteDomains.aleph0OrdOrderBot

theorem generators_target_finitePresentable {A B : SSet.{u}} (i : A ⟶ B)
    (hi : generators i) : IsFinitelyPresentable.{u} B := by
  obtain ⟨a⟩ := hi
  infer_instance

instance sourcePresentable (r : generators.{u}.toSet) :
    IsCardinalPresentable r.val.left Cardinal.aleph0.{u} :=
  generators_domain_finitePresentable r.val.hom r.property

instance targetPresentable (r : generators.{u}.toSet) :
    IsCardinalPresentable r.val.right Cardinal.aleph0.{u} :=
  generators_target_finitePresentable r.val.hom r.property

instance factorizationAccessible : factorization.{u}.Z.IsCardinalAccessible Cardinal.aleph0.{u} :=
  DaggerSOAStepAccessible.factorization_Z_accessible generators Cardinal.aleph0.{u}

instance rightFactorAccessible :
    (DaggerSOAAccessible.rightFactor factorization.{u}).IsCardinalAccessible Cardinal.aleph0.{u} :=
  DaggerSOAStepAccessible.property_rightFactor_accessible generators Cardinal.aleph0.{u}

end
end DaggerNativeInnerFactorizationAccessible
