import NativeKanSourceOriginalCoreFactor
import NativeKanSimplicialOpposite

/-! A native quasi-category whose original homotopy category has only isomorphisms is Kan. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerNativeKanSourceOriginalCoreFactor
open DaggerOriginalOrdinaryKanCoreNerveMembership
universe u
namespace DaggerNativeQuasicategoryGroupoidKan
noncomputable section

theorem core_eq_top (X : SSet.{u})
    (hX : ∀ {x y : SSet.hoFunctor.obj X} (f : x ⟶ y), IsIso f) :
    ordinaryCoreCandidate X = ⊤ := by
  apply le_antisymm le_top
  intro q s _
  apply (mem_ordinaryCoreCandidate_iff_unit_arrows_iso X _ s).mpr
  intro i j f
  exact hX _

theorem kan (X : SSet.{u}) [X.Quasicategory]
    (hX : ∀ {x y : SSet.hoFunctor.obj X} (f : x ⟶ y), IsIso f) : X.KanComplex := by
  have := native_quasi_core_kan X
  exact DaggerNativeKanSimplicialOpposite.kan_of_iso
    (SSet.Subcomplex.isoOfEq (core_eq_top X hX) ≪≫ SSet.Subcomplex.topIso X)

end
end DaggerNativeQuasicategoryGroupoidKan
