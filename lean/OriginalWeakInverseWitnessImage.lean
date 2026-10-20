import SimplexInverseWitnessCategory
import OriginalQuasiReplacementsAccessible

/-!
# Both original full weak classes are the exact images of the witness projections

Objects carry a whole inverse and all actual edges and cancellation triangles
after the unchanged original replacement. Morphisms preserve all these data.
The projections are faithful, but are not asserted full or accessible.
-/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerModels.OriginalTaggedReverseFreeCompletion
open DaggerNativeJoyalWeakSimplexInverse DaggerSimplexInverseWitnessCategory
open DaggerNativeJoyalMappingTest DaggerActualAntiJoyalMappingWeakProperties
universe u
namespace DaggerOriginalWeakInverseWitnessImage
noncomputable section

abbrev NativeWitness := Witness DaggerNativeInnerHornFactorization.replacement.{u}

abbrev nativeForget : NativeWitness.{u} ⥤ Arrow SSet.{u} :=
  forget DaggerNativeInnerHornFactorization.replacement

abbrev actualUnderlyingReplacement : AntiInvolutiveSSet.{u} ⥤ SSet.{u} :=
  DaggerActualAntiInnerHornFactorization.replacement ⋙ antiForget

abbrev ActualWitness := Witness actualUnderlyingReplacement.{u}

abbrev actualForget : ActualWitness.{u} ⥤ Arrow AntiInvolutiveSSet.{u} :=
  forget actualUnderlyingReplacement

theorem native_obj_weak (X : NativeWitness.{u}) : weakCategoricalEquivalences X.arrow.hom :=
  (weak_iff_replacement_simplex_inverse _).2 ⟨X.data⟩

theorem actual_obj_weak (X : ActualWitness.{u}) : weakEquivalences X.arrow.hom :=
  (actual_weak_iff_replacement_underlying_simplex_inverse _).2 ⟨X.data⟩

theorem native_weak_iff_image (f : Arrow SSet.{u}) :
    weakCategoricalEquivalences f.hom ↔ ∃ X : NativeWitness.{u}, nativeForget.obj X = f := by
  constructor
  · intro hf
    obtain ⟨d⟩ := (weak_iff_replacement_simplex_inverse f.hom).1 hf
    exact ⟨⟨f, d⟩, rfl⟩
  · rintro ⟨X, rfl⟩
    exact native_obj_weak X

theorem actual_weak_iff_image (f : Arrow AntiInvolutiveSSet.{u}) :
    weakEquivalences f.hom ↔ ∃ X : ActualWitness.{u}, actualForget.obj X = f := by
  constructor
  · intro hf
    obtain ⟨d⟩ := (actual_weak_iff_replacement_underlying_simplex_inverse f.hom).1 hf
    exact ⟨⟨f, d⟩, rfl⟩
  · rintro ⟨X, rfl⟩
    exact actual_obj_weak X

theorem native_weak_iff_essImage (f : Arrow SSet.{u}) :
    weakCategoricalEquivalences f.hom ↔ nativeForget.essImage f := by
  constructor
  · intro hf
    obtain ⟨X, rfl⟩ := (native_weak_iff_image f).1 hf
    exact nativeForget.obj_mem_essImage X
  · rintro ⟨X, ⟨e⟩⟩
    exact weakCategoricalEquivalences.of_retract (Retract.ofIso e.symm) (native_obj_weak X)

theorem actual_weak_iff_essImage (f : Arrow AntiInvolutiveSSet.{u}) :
    weakEquivalences f.hom ↔ actualForget.essImage f := by
  constructor
  · intro hf
    obtain ⟨X, rfl⟩ := (actual_weak_iff_image f).1 hf
    exact actualForget.obj_mem_essImage X
  · rintro ⟨X, ⟨e⟩⟩
    exact weakEquivalences.of_retract (Retract.ofIso e.symm) (actual_obj_weak X)

end
end DaggerOriginalWeakInverseWitnessImage
