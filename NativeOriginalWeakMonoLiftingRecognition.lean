import NativeWeakMonoWholeRestriction
import NativeBoundaryHoEquivalence
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-! The unchanged full weak mono class is an intersection with a literal left lifting class. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MorphismProperty Simplicial
open DaggerNativeJoyalMappingTest DaggerNativeInnerJoyalMappingWeak
open DaggerNativeWeakMonoWholeRestriction DaggerNativeBoundaryJoyalMappingWeak
universe u
namespace DaggerNativeOriginalWeakMonoLiftingRecognition
noncomputable section

theorem swap_restriction_lifting {A B K L : SSet.{u}} (i : A ⟶ B) (j : K ⟶ L)
    (Z : SSet.{u}) :
    HasLiftingProperty j ((MonoidalClosed.pre i).app Z) ↔
      HasLiftingProperty i ((MonoidalClosed.pre j).app Z) := by
  let sq : SSet.PushoutTensor i j := Functor.PushoutObjObj.ofHasPushout _ _ _
  have h1 : HasLiftingProperty sq.ι (terminal.from Z) ↔
      HasLiftingProperty j ((MonoidalClosed.pre i).app Z) := by
    simpa only [terminalPullback_π] using
      SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom sq (terminalPullback i Z)
  have h2 : HasLiftingProperty sq.flip.ι (terminal.from Z) ↔
      HasLiftingProperty i ((MonoidalClosed.pre j).app Z) := by
    simpa only [terminalPullback_π] using
      SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom sq.flip (terminalPullback j Z)
  exact h1.symm.trans
    ((HasLiftingProperty.iff_of_arrow_iso_left sq.flipArrowIso (terminal.from Z)).symm.trans h2)

def TestIndex : Type (u + 1) := ℕ × {Z : SSet.{u} // Z.Quasicategory}

def test (a : TestIndex.{u}) :
    (ihom (Δ[a.1] : SSet.{u})).obj a.2.val ⟶
      (ihom (SSet.boundary a.1).toSSet).obj a.2.val :=
  (MonoidalClosed.pre (SSet.boundary a.1).ι).app a.2.val

def tests : MorphismProperty SSet.{u} := ofHoms test

theorem tests_left_of_weak_mono {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (hi : weakCategoricalEquivalences i) : tests.llp i := by
  intro E X p hp
  obtain ⟨a⟩ := hp
  have : a.2.val.Quasicategory := a.2.property
  exact (swap_restriction_lifting i (SSet.boundary a.1).ι a.2.val).mp
    (restriction_boundary i hi a.2.val a.1)

theorem weak_of_tests_left {A B : SSet.{u}} (i : A ⟶ B) (hi : tests.llp i) :
    weakCategoricalEquivalences i := by
  intro Z _
  apply DaggerNativeBoundaryHoEquivalence.monoRight_ho_isEquivalence
  apply boundary_rlp_monomorphisms
  intro n
  exact (swap_restriction_lifting i (SSet.boundary n).ι Z).mpr
    (hi (test ⟨n, ⟨Z, inferInstance⟩⟩) (ofHoms.mk _))

theorem weak_mono_eq :
    monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences =
      monomorphisms SSet.{u} ⊓ tests.llp := by
  ext A B i
  constructor
  · intro h
    have : Mono i := h.1
    exact ⟨h.1, tests_left_of_weak_mono i h.2⟩
  · intro h
    exact ⟨h.1, weak_of_tests_left i h.2⟩

end
end DaggerNativeOriginalWeakMonoLiftingRecognition
