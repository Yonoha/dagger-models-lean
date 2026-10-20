import SmallWholeWitnessFibers

/-! Every full witness above a small property of original arrows forms a small family. -/
set_option autoImplicit false
open CategoryTheory
open DaggerSimplexInverseWitnessCategory DaggerNativeJoyalWeakSimplexInverse
universe u v w
namespace DaggerWholeWitnessSmallBaseProperties

variable {C : Type w} [Category.{v} C] (R : C ⥤ SSet.{u})

theorem inverseImageSmall (P : ObjectProperty (Arrow C)) [ObjectProperty.Small.{u} P] :
    ObjectProperty.Small.{u} (P.inverseImage (forget R)) := by
  let I := Σ a : Subtype P, SimplexInverseData (R.map a.val.hom)
  let f : I → Subtype (P.inverseImage (forget R)) :=
    fun i ↦ ⟨⟨i.1.val, i.2⟩, i.1.property⟩
  apply small_of_surjective (f := f)
  rintro ⟨⟨a, d⟩, ha⟩
  exact ⟨⟨⟨a, ha⟩, d⟩, rfl⟩

end DaggerWholeWitnessSmallBaseProperties
