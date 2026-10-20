import OriginalBorelWeakEquivalenceClasses

/-!
# Closed T₁ embeddings in the actual free-action cell filtration

The forgotten free generator is the literal coproduct of its original map.
The native TopCat coproduct, pushout and cell-complex results therefore give a
closed T₁ embedding filtration for every free-boundary/free-horn cell complex.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MorphismProperty HomotopicalAlgebra
open scoped TopCat.modelCategory
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalBorelFreeGenerators

universe u

namespace DaggerOriginalBorelClosedCellFiltration

noncomputable section

/-- The forgotten free map is the literal constant C₂-indexed coproduct map. -/
theorem free_map_hom {A B : TopCat.{u}} (i : A ⟶ B) :
    (free.map i).hom = Limits.Sigma.map (fun (_ : C2.{u}) ↦ i) := rfl

/-- Free maps preserve the native closed T₁ embedding property on underlying maps. -/
theorem free_map_closedT₁Embedding {A B : TopCat.{u}} (i : A ⟶ B)
    (hi : TopCat.closedT₁Embeddings i) : TopCat.closedT₁Embeddings (free.map i).hom := by
  rw [free_map_hom]
  exact TopCat.closedT₁Embeddings.isClosedT₁Embedding_of_isColimit_cofan
    (fun (_ : C2.{u}) ↦ i) (colimit.isColimit _) (colimit.isColimit _) _
      (fun _ ↦ colimit.ι_desc _ _) (fun _ ↦ hi)

/-- Free boundaries have underlying closed T₁ embeddings. -/
theorem I_le_closedUnderlying : I.{u} ≤
    TopCat.closedT₁Embeddings.inverseImage (Action.forget TopCat.{u} C2.{u}) := by
  rintro A B i ⟨n⟩
  exact free_map_closedT₁Embedding _ (TopCat.modelCategory.I_le_t₁Inclusions _ ⟨n⟩)

/-- Free horns have underlying closed T₁ embeddings. -/
theorem J_le_closedUnderlying : J.{u} ≤
    TopCat.closedT₁Embeddings.inverseImage (Action.forget TopCat.{u} C2.{u}) := by
  intro A B i hi
  simp only [J, iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  apply free_map_closedT₁Embedding
  apply TopCat.modelCategory.J_le_t₁Inclusions
  simp only [TopCat.modelCategory.J, iSup_iff]
  exact ⟨n, ⟨k⟩⟩

/-- The actual forgotten filtration consists of native closed T₁ embedding steps. -/
def underlyingClosedCellFiltration {X Y : Action TopCat.{u} C2.{u}}
    (f : X ⟶ Y)
    (hf : RelativeCellComplex.{u} (fun (_ : ℕ) ↦ (I.{u} ⊔ J.{u}).homFamily) f) :
    TopCat.closedT₁Embeddings.TransfiniteCompositionOfShape ℕ f.hom := by
  have : PreservesWellOrderContinuousOfShape ℕ (Action.forget TopCat.{u} C2.{u}) :=
    ⟨fun _ _ ↦ inferInstance⟩
  refine (hf.map (Action.forget TopCat C2)).transfiniteCompositionOfShape.ofLE ?_
  simp only [pushouts_le_iff, coproducts_le_iff]
  rintro A B i ⟨t⟩
  exact (sup_le I_le_closedUnderlying J_le_closedUnderlying) _ t.property

end

end DaggerOriginalBorelClosedCellFiltration
