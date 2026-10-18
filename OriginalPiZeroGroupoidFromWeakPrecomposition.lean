import OriginalSimplicialPiZeroFunctor
import OriginalSimplicialCategoryVertexComposition
import OriginalAmbientDaggerPiZeroGroupoid

/-! Original weak vertex precompositions force the exact original component category groupoid. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite DaggerModels
open DaggerOriginalSimplicialPiZeroCategory DaggerOriginalSimplicialPiZeroWeakEquivalence
open DaggerOriginalSimplicialCategoryVertexComposition DaggerOriginalAmbientDaggerPiZeroGroupoid
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalPiZeroGroupoidFromWeakPrecomposition
noncomputable section

theorem mapPiZero_precomposeVertex (C : SimplicialCat.{u, u}) {x y : componentObjects C}
    (a : (C.enriched.Hom x y) _⦋0⦌) (z : componentObjects C) (b : y ⟶ z) :
    SSet.mapπ₀ (precomposeVertex C a z) b = (SSet.π₀.mk a : x ⟶ y) ≫ b := by
  obtain ⟨b, rfl⟩ := SSet.π₀.mk_surjective b
  rw [SSet.mapπ₀_mk, precomposeVertex_apply, vertexPoint_zero]
  rfl

theorem groupoid_of_weak_precomposition (C : SimplicialCat.{u, u})
    (hC : ∀ (x y : C.Obj) (a : (C.enriched.Hom x y) _⦋0⦌) (z : C.Obj),
      WeakEquivalence (precomposeVertex C a z)) : HasActualComponentGroupoid C := by
  refine ⟨Groupoid.ofIsIso (fun {x y} a ↦ ?_), rfl⟩
  obtain ⟨av, rfl⟩ := SSet.π₀.mk_surjective a
  have hb (z : componentObjects C) :
      Function.Bijective (fun b : y ⟶ z ↦ (SSet.π₀.mk av : x ⟶ y) ≫ b) := by
    have : WeakEquivalence (precomposeVertex C av z) := hC x y av z
    have he : SSet.mapπ₀ (precomposeVertex C av z) =
        (fun b : y ⟶ z ↦ (SSet.π₀.mk av : x ⟶ y) ≫ b) :=
      funext (mapPiZero_precomposeVertex C av z)
    rw [← he]
    exact bijective_mapPiZero _
  obtain ⟨b, hab⟩ := (hb x).surjective (𝟙 x)
  change (SSet.π₀.mk av : x ⟶ y) ≫ b = 𝟙 x at hab
  have hba : b ≫ (SSet.π₀.mk av : x ⟶ y) = 𝟙 y := by
    apply (hb y).injective
    change (SSet.π₀.mk av : x ⟶ y) ≫ (b ≫ SSet.π₀.mk av) = SSet.π₀.mk av ≫ 𝟙 y
    rw [← Category.assoc, hab, Category.id_comp, Category.comp_id]
  exact ⟨⟨b, hab, hba⟩⟩

end
end DaggerOriginalPiZeroGroupoidFromWeakPrecomposition
