import OriginalRealizedPushoutTensorCofibrations
import TopCatModelCategory.TopCat.CompactOpen

/-!
# The native tensor adjunction restricted to locally compact parameters

Only the parameter category is restricted. The second variable and the target
remain arbitrary native TopCat spaces. The right adjoints and precomposition
are the existing monoidal-closed constructions at the locally compact
parameter objects, so no closed structure on all TopCat spaces is asserted.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite

universe u

namespace DaggerOriginalLocallyCompactTensorAdjunction

noncomputable section

/-- Native locally compact TopCat objects as a full subcategory. -/
def locallyCompactObjects : ObjectProperty TopCat.{u} := fun X ↦ LocallyCompactSpace X

/-- The parameter category retains every map between the original locally compact spaces. -/
abbrev LocallyCompactTopCat := locallyCompactObjects.{u}.FullSubcategory

instance (X : LocallyCompactTopCat.{u}) : LocallyCompactSpace X.obj := X.property

/-- The native tensor bifunctor with its first variable restricted to locally compact spaces. -/
def locallyCompactTensor : LocallyCompactTopCat.{u} ⥤ TopCat.{u} ⥤ TopCat.{u} :=
  locallyCompactObjects.ι ⋙ curriedTensor TopCat

/-- The existing right adjoints with their native contravariant precomposition. -/
def locallyCompactIhom : LocallyCompactTopCat.{u}ᵒᵖ ⥤ TopCat.{u} ⥤ TopCat.{u} where
  obj X := ihom X.unop.obj
  map f := MonoidalClosed.pre f.unop.hom
  map_id X := by simp
  map_comp f g := by simp

/-- The native adjunctions are natural in the original locally compact parameter. -/
def locallyCompactAdjunction : locallyCompactTensor.{u} ⊣₂ locallyCompactIhom.{u} :=
  ParametrizedAdjunction.mk' (fun X ↦ ihom.adjunction X.obj) (by
    intro X Y f E Z g
    exact (MonoidalClosed.curry_pre_app f.hom g).symm)

end

end DaggerOriginalLocallyCompactTensorAdjunction
