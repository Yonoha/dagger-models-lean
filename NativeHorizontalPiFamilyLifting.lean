import NativeHorizontalPiRestriction

/-! The native based-pi Kan condition extends actual compatible families along anodyne maps. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite SSet.KanComplex
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeHorizontalPiCompatibility
open DaggerNativeHorizontalPiSections DaggerNativeHorizontalPiRestriction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeHorizontalPiFamilyLifting
noncomputable section

variable {K L : SSet.{u}} (i : K ⟶ L) (X : BiSSet.{u}) (t : ℕ)
  (a : (horizontalMapping L X) _⦋0⦌)

theorem restrictFamily_surjective [Cofibration i] [WeakEquivalence i]
    [Fibration (C := SSet.{u}) (rowProjection X t)] :
    Function.Surjective (restrictFamily i X t a) := by
  intro s
  let sq : CommSq (familyMap K X t (restrictedVertex i X a) s) i
      (rowProjection X t) (vertexMap L X a) := ⟨rfl⟩
  let z : PiSection L X t a := ⟨sq.lift, sq.fac_right⟩
  let r := sectionFamily L X t a z
  have hr : familyMap L X t a r = sq.lift :=
    congrArg Subtype.val ((familySectionEquiv L X t a).apply_symm_apply z)
  refine ⟨r, familyMap_injective K X t (restrictedVertex i X a) ?_⟩
  rw [familyMap_restrict, hr]
  exact sq.fac_left

theorem restriction_mapπ_surjective [Cofibration i] [WeakEquivalence i]
    [Fibration (C := SSet.{u}) (rowProjection X t)]
    (hL : Function.Surjective (piComparison L X t a))
    (hK : Function.Injective (piComparison K X t (restrictedVertex i X a))) :
    Function.Surjective
      (mapπ (horizontalPre i X) t a (restrictedVertex i X a) rfl) := by
  intro s
  obtain ⟨r, hr⟩ := restrictFamily_surjective i X t a
    (piComparison K X t (restrictedVertex i X a) s)
  obtain ⟨z, hz⟩ := hL r
  refine ⟨z, hK ?_⟩
  rw [piComparison_restrict, hz, hr]

theorem simplex_restriction_mapπ_surjective {m : ℕ} (j : K ⟶ (Δ[m] : SSet.{u}))
    [Cofibration j] [WeakEquivalence j] [Fibration (C := SSet.{u}) (rowProjection X t)]
    (v : (horizontalMapping (Δ[m] : SSet.{u}) X) _⦋0⦌)
    (hK : Function.Injective (piComparison K X t (restrictedVertex j X v))) :
    Function.Surjective
      (mapπ (horizontalPre j X) t v (restrictedVertex j X v) rfl) :=
  restriction_mapπ_surjective j X t v (simplex_piComparison_surjective X m t v) hK

end
end DaggerNativeHorizontalPiFamilyLifting
