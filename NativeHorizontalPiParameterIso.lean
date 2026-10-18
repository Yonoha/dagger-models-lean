import NativeHorizontalPiRestriction
import NativePartialFaceUnionGeometry

/-! Canonical original pi-family comparison transfers along actual parameter isomorphisms. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite SSet.KanComplex
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeHorizontalPiCompatibility
open DaggerNativeHorizontalPiSections DaggerNativeHorizontalPiRestriction
open DaggerNativePartialFaceUnionGeometry
universe u
namespace DaggerNativeHorizontalPiParameterIso
noncomputable section

def parameterIso {K L : SSet.{u}} (e : K ≅ L) (X : BiSSet.{u}) :
    horizontalMapping L X ≅ horizontalMapping K X where
  hom := horizontalPre e.hom X
  inv := horizontalPre e.inv X
  hom_inv_id := by
    rw [← horizontalPre_comp, e.inv_hom_id, horizontalPre_id]
  inv_hom_id := by
    rw [← horizontalPre_comp, e.hom_inv_id, horizontalPre_id]

theorem piComparison_bijective_of_parameter_iso {K L : SSet.{u}} (e : K ≅ L)
    (X : BiSSet.{u}) (t : ℕ) (v : (horizontalMapping L X) _⦋0⦌)
    (hK : Function.Bijective (piComparison K X t (restrictedVertex e.hom X v))) :
    Function.Bijective (piComparison L X t v) := by
  let E := mapπEquivOfIso (parameterIso e X) t v (restrictedVertex e.hom X v) rfl
  constructor
  · intro s r he
    apply E.injective
    apply hK.1
    exact (piComparison_restrict e.hom X t v s).trans
      ((congrArg (restrictFamily e.hom X t v) he).trans
        (piComparison_restrict e.hom X t v r).symm)
  · intro r
    obtain ⟨s, hs⟩ := hK.2 (restrictFamily e.hom X t v r)
    obtain ⟨z, hz⟩ := E.surjective s
    refine ⟨z, familyMap_injective L X t v ?_⟩
    apply (cancel_epi e.hom).1
    have hh : restrictFamily e.hom X t v (piComparison L X t v z) =
        restrictFamily e.hom X t v r :=
      (piComparison_restrict e.hom X t v z).symm.trans
        ((congrArg (piComparison K X t (restrictedVertex e.hom X v)) hz).trans hs)
    exact (familyMap_restrict e.hom X t v (piComparison L X t v z)).symm.trans
      ((congrArg (familyMap K X t (restrictedVertex e.hom X v)) hh).trans
        (familyMap_restrict e.hom X t v r))

theorem faceUnion_singleton {n : ℕ} (i : Fin (n + 1)) :
    faceUnion.{u} {i} = SSet.stdSimplex.face {i}ᶜ := Finset.sup_singleton

def singletonFaceIso (n : ℕ) (i : Fin (n + 2)) :
    (Δ[n] : SSet.{u}) ≅ (faceUnion.{u} {i} : SSet.{u}) :=
  SSet.stdSimplex.faceSingletonComplIso i ≪≫
    SSet.Subcomplex.eqToIso (faceUnion_singleton i).symm

theorem singletonFace_piComparison_bijective (n : ℕ) (i : Fin (n + 2))
    (X : BiSSet.{u}) (t : ℕ) (v : (horizontalMapping (faceUnion.{u} {i}) X) _⦋0⦌) :
    Function.Bijective (piComparison (faceUnion.{u} {i}) X t v) :=
  piComparison_bijective_of_parameter_iso (singletonFaceIso n i) X t v
    (simplex_piComparison_bijective X n t _)

end
end DaggerNativeHorizontalPiParameterIso
