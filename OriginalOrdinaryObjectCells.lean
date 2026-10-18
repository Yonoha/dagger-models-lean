import DaggerModels.SimplicialObjectAdjunctions
import DaggerModels.OrdinaryTwoObjectCell
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
The object part of ordinary two-object cell attachments. This records the
object-bijection closure needed in the T05 cell argument; it makes no claim
about the mapping spaces or the local Kan condition.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty DaggerModels

universe u w w'

namespace DaggerOriginalOrdinaryObjectCells

/-- Enriched functors whose actual object functions are bijective. -/
def objectBijections : MorphismProperty SimplicialCat.{u, u} :=
  (isomorphisms (Type u)).inverseImage SimplicialCat.objects

theorem objectBijections_iff {C D : SimplicialCat.{u, u}} (f : C ⟶ D) :
    objectBijections f ↔ Function.Bijective f.obj := by
  change IsIso (SimplicialCat.objects.map f) ↔ Function.Bijective f.obj
  exact isIso_iff_bijective _

/-- The one-edge map acts as the identity on its two objects. -/
theorem ordinaryMap_objectBijections {K L : SSet.{u}} (j : K ⟶ L) :
    objectBijections (OrdinaryTwoObjectCell.functor.map j) := by
  rw [objectBijections_iff]
  have h : (OrdinaryTwoObjectCell.functor.map j).obj =
      (id : TwoObjectDaggerGraph.Vertex.{u} → TwoObjectDaggerGraph.Vertex.{u}) := by
    funext x
    rcases x with ⟨b⟩
    cases b <;> rfl
  rw [h]
  exact Function.bijective_id

/-- An arbitrary family of actual ordinary one-edge maps lies in the object class. -/
theorem ordinaryCellFamily_le_objectBijections {I : Type u}
    {K L : I → SSet.{u}} (j : ∀ i, K i ⟶ L i) :
    MorphismProperty.ofHoms
      (fun i ↦ OrdinaryTwoObjectCell.functor.map (j i)) ≤ objectBijections := by
  rintro _ _ _ ⟨i⟩
  exact ordinaryMap_objectBijections (j i)

instance objectBijections_isMultiplicative : objectBijections.{u}.IsMultiplicative := by
  change ((isomorphisms (Type u)).inverseImage SimplicialCat.objects).IsMultiplicative
  infer_instance

instance objectBijections_respectsIso : objectBijections.{u}.RespectsIso := by
  change ((isomorphisms (Type u)).inverseImage SimplicialCat.objects).RespectsIso
  infer_instance

instance objectBijections_isStableUnderCobaseChange :
    objectBijections.{u}.IsStableUnderCobaseChange where
  of_isPushout sq hf := by
    letI : PreservesColimitsOfSize.{0, 0} SimplicialCat.objects.{u, u} :=
      SimplicialCat.objectsPreservesColimitsOfSize
    exact (isomorphisms (Type u)).of_isPushout
      (sq.map SimplicialCat.objects) hf

instance objectBijections_isStableUnderColimitsOfShape (J : Type w) [Category.{w'} J] :
    objectBijections.{u}.IsStableUnderColimitsOfShape J where
  condition X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ := by
    letI : PreservesColimitsOfSize.{w', w} SimplicialCat.objects.{u, u} :=
      SimplicialCat.objectsPreservesColimitsOfSize
    change (isomorphisms (Type u)) (SimplicialCat.objects.map φ)
    apply (isomorphisms (Type u)).colimitsOfShape_le (J := J)
    refine MorphismProperty.colimitsOfShape.mk'
      (X₁ ⋙ SimplicialCat.objects) (X₂ ⋙ SimplicialCat.objects)
      (SimplicialCat.objects.mapCocone c₁) (SimplicialCat.objects.mapCocone c₂)
      (isColimitOfPreserves _ h₁) (isColimitOfPreserves _ h₂)
      (Functor.whiskerRight f _) (fun j ↦ hf j) _ ?_
    intro j
    simpa only [Functor.mapCocone_ι_app, Functor.map_comp] using
      congrArg SimplicialCat.objects.map (hφ j)

instance objectBijections_isStableUnderCoproducts :
    IsStableUnderCoproducts.{u} objectBijections.{u} where
  isStableUnderCoproductsOfShape J := objectBijections_isStableUnderColimitsOfShape (Discrete J)

instance objectBijections_isStableUnderFilteredColimits :
    IsStableUnderFilteredColimits.{u, u} objectBijections.{u} where
  isStableUnderColimitsOfShape J := objectBijections_isStableUnderColimitsOfShape J

instance objectBijections_isStableUnderTransfiniteComposition :
    IsStableUnderTransfiniteComposition.{u} objectBijections.{u} :=
  inferInstance

/-- Every transfinite composite of pushouts of coproducts of ordinary
two-object cells has a bijective function on objects. -/
theorem cellClosure_object_bijective {C D : SimplicialCat.{u, u}} (f : C ⟶ D)
    (hf : MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.pushouts
        (MorphismProperty.coproducts.{u} objectBijections.{u})) f) :
    Function.Bijective f.obj := by
  apply (objectBijections_iff f).mp
  have hcop : MorphismProperty.coproducts.{u} objectBijections.{u} ≤ objectBijections :=
    objectBijections.coproducts_le
  have hpush : MorphismProperty.pushouts
      (MorphismProperty.coproducts.{u} objectBijections.{u}) ≤ objectBijections :=
    le_trans (pushouts_monotone hcop) objectBijections.pushouts_le
  exact (le_trans (transfiniteCompositions_monotone hpush)
    objectBijections.transfiniteCompositions_le) f hf

/-- The actual ordinary one-edge family retains a bijective object map after
coproducts, pushouts, and transfinite composition. -/
theorem ordinaryCellFamily_closure_object_bijective {I : Type u}
    {K L : I → SSet.{u}} (j : ∀ i, K i ⟶ L i)
    {C D : SimplicialCat.{u, u}} (f : C ⟶ D)
    (hf : MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.pushouts
        (MorphismProperty.coproducts.{u}
          (MorphismProperty.ofHoms
            (fun i ↦ OrdinaryTwoObjectCell.functor.map (j i))))) f) :
    Function.Bijective f.obj := by
  apply cellClosure_object_bijective f
  exact (transfiniteCompositions_monotone
    (pushouts_monotone
      (coproducts_monotone (ordinaryCellFamily_le_objectBijections j)))) f hf

end DaggerOriginalOrdinaryObjectCells
