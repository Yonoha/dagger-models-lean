import OriginalDaggerCoreCandidate
import OriginalOrdinaryKanCoreCandidateFunctor

/-!
# The exact dagger core candidate as a functor with its natural inclusion

The object is the original ordinary core candidate with the restricted original
dagger. The map is the already proved restriction of the original simplicial map.
No Kan property or derived recognition theorem is assumed or asserted here.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalDaggerCoreCandidate

universe u

namespace DaggerOriginalDaggerCoreCandidateFunctor

noncomputable section

/-- The original core candidate with its original restricted dagger is functorial. -/
def daggerCoreFunctor : DaggerSSet.{u} ⥤ DaggerSSet.{u} where
  obj X := daggerCoreCandidate X
  map f := daggerCoreMap f
  map_id X := by
    apply DaggerSSet.Hom.ext
    exact ordinaryCoreCandidateFunctor.map_id X.toSSet
  map_comp f g := by
    apply DaggerSSet.Hom.ext
    exact ordinaryCoreCandidateFunctor.map_comp f.hom g.hom

/-- The literal subcomplex inclusions form a natural dagger-preserving transformation. -/
def daggerCoreNaturalInclusion : daggerCoreFunctor.{u} ⟶ 𝟭 DaggerSSet.{u} where
  app X := daggerCoreInclusion X
  naturality X Y f := by
    apply DaggerSSet.Hom.ext
    exact daggerCoreMap_comp_inclusion f

/-- The object keeps exactly the original ordinary core subcomplex as its underlying set. -/
theorem daggerCoreFunctor_obj_toSSet (X : DaggerSSet.{u}) :
    (daggerCoreFunctor.obj X).toSSet = (ordinaryCoreCandidate X.toSSet : SSet.{u}) := rfl

/-- The underlying natural inclusion is exactly the original subcomplex inclusion. -/
theorem daggerCoreNaturalInclusion_hom (X : DaggerSSet.{u}) :
    (daggerCoreNaturalInclusion.app X).hom = (ordinaryCoreCandidate X.toSSet).ι := rfl

end

end DaggerOriginalDaggerCoreCandidateFunctor
