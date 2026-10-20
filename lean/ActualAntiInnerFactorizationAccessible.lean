import ActualAntiInnerHornFactorization
import ActualAntiInvolutivePresentable
import OriginalSOAFactorizationRecovered

/-!
# The original actual anti-inner-horn factorization is finitely accessible

Use the actual free adjunction for both finite-presentability conditions,
the proved local finite presentability of the actual anti category, and the
retained small-object theorem for the exact existing factorization.
-/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerModels.OriginalTaggedReverseFreeCompletion
open DaggerActualAntiInnerHornFactorization
universe u
namespace DaggerActualAntiInnerFactorizationAccessible
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0
attribute [local instance] DaggerModels.SmallObjectFiniteDomains.aleph0OrdOrderBot

theorem generators_target_finitePresentable {A B : AntiInvolutiveSSet.{u}} (i : A ⟶ B)
    (hi : generators i) : IsFinitelyPresentable.{u} B := by
  obtain ⟨a⟩ := hi
  exact freeAntiAdjunction.isCardinalPresentable_leftAdjoint_obj Cardinal.aleph0 _

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
end DaggerActualAntiInnerFactorizationAccessible
