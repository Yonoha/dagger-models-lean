import ActualAntiInvolutiveLimits
import DaggerModels.Presentable
import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Local finite presentability of the original anti-involutive category

Use the same native free-Yoneda singleton strong generator as the original
reversal-presheaf proof, and transport it through the actual tagged equivalence.
-/
set_option autoImplicit false
open CategoryTheory Limits DaggerModels
open DaggerModels.OriginalTaggedReverseSimplex
universe u
namespace DaggerActualAntiInvolutivePresentable
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0

instance taggedPresheavesLocallyFinitelyPresentable :
    IsLocallyFinitelyPresentable.{u} (TaggedReverseSimplexᵒᵖ ⥤ Type u) := by
  let P : ObjectProperty (Type u) := ObjectProperty.singleton PUnit
  let G := ObjectProperty.ofObj
    (fun T : TaggedReverseSimplex × Subtype P ↦ Presheaf.freeYoneda T.1 T.2.1)
  apply (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator.{u, u, u + 1}
    (TaggedReverseSimplexᵒᵖ ⥤ Type u) Cardinal.aleph0.{u}).2
  refine ⟨G, inferInstance, Presheaf.isStrongGenerator (P := P) typeUnitStrongGenerator.{u}
    TaggedReverseSimplex, ?_⟩
  rintro _ ⟨⟨n, M, hM⟩⟩
  have hM' : IsCardinalPresentable M Cardinal.aleph0.{u} := by
    have hunit : IsCardinalPresentable (PUnit : Type u) Cardinal.aleph0.{u} :=
      HasCardinalLT.isCardinalPresentable
        (hasCardinalLT_of_finite PUnit Cardinal.aleph0.{u} le_rfl)
    have hEq : PUnit = M := (ObjectProperty.singleton_iff _ _).mp hM
    exact hEq ▸ hunit
  rw [isCardinalPresentable_iff]
  infer_instance

instance antiLocallyFinitelyPresentable :
    IsLocallyFinitelyPresentable.{u} AntiInvolutiveSSet.{u} :=
  antiInvolutiveEquivalence.symm.isCardinalLocallyPresentable Cardinal.aleph0.{u}

instance antiLocallyPresentable : IsLocallyPresentable.{u} AntiInvolutiveSSet.{u} where
  exists_cardinal := ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance⟩

end
end DaggerActualAntiInvolutivePresentable
