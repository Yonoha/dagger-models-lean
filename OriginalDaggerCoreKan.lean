import OriginalOrdinaryCoreKan
import OriginalDaggerCoreCandidateFunctor

/-!
# The original restricted dagger core is the actual greatest Kan core

The dagger, original involution, fixed vertex labels and natural inclusion
are already those of the original core candidate. The verified full ordinary
Kan theorem now applies to that exact underlying simplicial set. No new
dagger, fixed-point interpretation or replacement subcomplex is introduced.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalInnerHornFillers DaggerOriginalOrdinaryCoreKan
open DaggerOriginalDaggerCoreCandidate DaggerOriginalDaggerCoreCandidateFunctor

universe u

namespace DaggerOriginalDaggerCoreKan

/-- The exact restricted original dagger core has a native Kan underlying simplicial set. -/
theorem daggerCoreCandidate_kan (X : DaggerSSet.{u}) (hX : innerHornFillers X.toSSet) :
    (daggerCoreCandidate X).toSSet.KanComplex := ordinaryCoreCandidate_kan X.toSSet hX

/-- The previously defined original dagger core functor now produces native Kan objects. -/
theorem daggerCoreFunctor_obj_kan (X : DaggerSSet.{u}) (hX : innerHornFillers X.toSSet) :
    (daggerCoreFunctor.obj X).toSSet.KanComplex := daggerCoreCandidate_kan X hX

/-- The exact underlying original subcomplex is the greatest native Kan subcomplex. -/
theorem daggerCore_isGreatestKanSubcomplex (X : DaggerSSet.{u})
    (hX : innerHornFillers X.toSSet) :
    IsGreatest {A : X.toSSet.Subcomplex | (A : SSet.{u}).KanComplex}
      (DaggerOriginalOrdinaryKanCoreSubcomplex.ordinaryCoreCandidate X.toSSet) :=
  ordinaryCoreCandidate_isGreatestKanSubcomplex X.toSSet hX

/-- Native quasi-categories in universe zero retain the same all-dimensional dagger Kan core. -/
theorem daggerCoreCandidate_kan_of_native_quasicategory (X : DaggerSSet.{0})
    [X.toSSet.Quasicategory] : (daggerCoreCandidate X).toSSet.KanComplex :=
  daggerCoreCandidate_kan X ((innerHornFillers_iff_native_quasicategory X.toSSet).mpr
    inferInstance)

end DaggerOriginalDaggerCoreKan
