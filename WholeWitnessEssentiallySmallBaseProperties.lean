import WholeWitnessSmallBaseProperties
import WholeWitnessIsoInverses

/-! All whole witnesses above an essentially small base property are essentially small. -/
set_option autoImplicit false
open CategoryTheory
open DaggerSimplexInverseWitnessCategory
universe u v w
namespace DaggerWholeWitnessEssentiallySmallBaseProperties
noncomputable section
variable {C : Type w} [Category.{v} C] (R : C ⥤ SSet.{u})

theorem inverseImageEssentiallySmall (P : ObjectProperty (Arrow C))
    [ObjectProperty.EssentiallySmall.{u} P] :
    ObjectProperty.EssentiallySmall.{u} (P.inverseImage (forget R)) where
  exists_small_le' := by
    obtain ⟨Q, hQ, _, hP⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{u} P
    have : ObjectProperty.Small.{u} Q := hQ
    refine ⟨Q.inverseImage (forget R),
      DaggerWholeWitnessSmallBaseProperties.inverseImageSmall R Q, ?_⟩
    intro X hX
    obtain ⟨a, ha, ⟨e⟩⟩ := hP X.arrow hX
    exact ⟨DaggerWholeWitnessIsoTransport.witness R X e, ha,
      ⟨DaggerWholeWitnessIsoInverses.transportedIso R X e⟩⟩

end
end DaggerWholeWitnessEssentiallySmallBaseProperties
