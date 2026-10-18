import OriginalUnitaryCoreComponentSurjectivity
import OriginalOrdinaryCoreHomotopyInclusion

/-!
# Original unitary-component surjectivity gives ordinary essential surjectivity

Native π₀ equality in the exact original core gives an isomorphism in its
native homotopy groupoid. The actual core inclusion sends that isomorphism
to the original ambient homotopy category. Applying the already proved
component-surjectivity theorem proves essential surjectivity of the actual
native homotopy functor of the original dagger map. The target retains its
original inner-horn hypothesis; no intrinsic equivalence recognition is assumed.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalInnerHornFillers DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryCorePathGroupoid DaggerOriginalOrdinaryCoreHomotopyInclusion
open DaggerOriginalDaggerCoreCandidate DaggerOriginalUnitaryCoreConstruction
open DaggerOriginalUnitaryCoreComponentSurjectivity

universe u

namespace DaggerOriginalUnitaryCoreOrdinaryEssentialSurjectivity

noncomputable section

/-- Native component equality gives a native original-core homotopy-category isomorphism. -/
theorem core_homotopy_iso_of_pi0_eq (X : SSet.{u}) (hX : innerHornFillers X)
    {x y : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋0⦌)}
    (h : SSet.π₀.mk x = SSet.π₀.mk y) :
    Nonempty (SSet.Truncated.HomotopyCategory.mk
      (V := (SSet.truncation 2).obj (ordinaryCoreCandidate X : SSet.{u})) x ≅
      SSet.Truncated.HomotopyCategory.mk
        (V := (SSet.truncation 2).obj (ordinaryCoreCandidate X : SSet.{u})) y) := by
  have he := (SSet.π₀.mk_eq_mk_iff x y).1 h
  clear h
  induction he with
  | rel a b hab =>
      obtain ⟨s, rfl, rfl⟩ := hab
      let e := SSet.Edge.mk s rfl rfl
      have : IsIso (SSet.Truncated.HomotopyCategory.homMk e) := core_homMk_isIso X hX e
      exact ⟨asIso (SSet.Truncated.HomotopyCategory.homMk e)⟩
  | refl a => exact ⟨Iso.refl _⟩
  | symm a b hab ih =>
      obtain ⟨e⟩ := ih
      exact ⟨e.symm⟩
  | trans a b c hab hbc ihab ihbc =>
      obtain ⟨e⟩ := ihab
      obtain ⟨d⟩ := ihbc
      exact ⟨e ≪≫ d⟩

/-- The actual native homotopy functor of the original dagger map is essentially surjective. -/
theorem ordinary_essSurj_of_unitary_pi0_surjective {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (hY : innerHornFillers Y.toSSet)
    (h : Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f))) :
    ((SSet.hoFunctor.map f.hom).toFunctor).EssSurj where
  mem_essImage z := by
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective z
    obtain ⟨x, hx⟩ := core_canonical_component_surjectivity f h y
    obtain ⟨e⟩ := core_homotopy_iso_of_pi0_eq Y.toSSet hY hx
    refine ⟨SSet.Truncated.HomotopyCategory.mk
      (V := (SSet.truncation 2).obj X.toSSet) x, ?_⟩
    exact ⟨(coreHomotopyInclusion Y.toSSet).mapIso e⟩

end

end DaggerOriginalUnitaryCoreOrdinaryEssentialSurjectivity
