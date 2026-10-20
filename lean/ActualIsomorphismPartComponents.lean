import ActualIsomorphismPartFibrancy
import OriginalFullVertexWeakEquivalenceRestriction
import OriginalAmbientDaggerPiZeroGroupoid
import OriginalLocalKanReplacementDiagonalWeak

/-! The ALL-isomorphism-component part of a locally Kan category has a groupoid of components. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerOriginalSimplicialPiZeroCategory DaggerActualSimplicialIsomorphismComponentPart
open DaggerActualSimplicialIsomorphismComponentMaps DaggerOriginalFullVertexSubcomplex
open DaggerOriginalAmbientDaggerPiZeroGroupoid OriginalOrdinaryLocalKanReplacement
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualIsomorphismPartComponents
noncomputable section

theorem hom_eq_fullVertex (C : SimplicialCat.{u, u}) (x y : componentObjects C) :
    homSubcomplex C x y = fullVertexSubcomplex (C.enriched.Hom x y)
      ((homSubcomplex C x y).obj (op ⦋0⦌)) := by
  ext q s
  change (s ∈ (homSubcomplex C x y).obj q) ↔
    ∀ φ : ⦋0⦌ ⟶ q.unop,
      (C.enriched.Hom x y).map φ.op s ∈ (homSubcomplex C x y).obj (op ⦋0⦌)
  constructor
  · intro hs φ
    exact (mem_iff_vertex C x y q s φ).mp hs
  · intro hs
    let φ : ⦋0⦌ ⟶ q.unop := SimplexCategory.const _ _ 0
    exact (mem_iff_vertex C x y q s φ).mpr (hs φ)

theorem inclusion_components_injective (C : SimplicialCat.{u, u})
    (x y : componentObjects C) [SSet.KanComplex (C.enriched.Hom x y)] :
    Function.Injective (SSet.mapπ₀ (homSubcomplex C x y).ι) := by
  rw [hom_eq_fullVertex]
  exact DaggerOriginalFullVertexWeakEquivalenceRestriction.inclusion_mapπ₀_injective _

def inclusion_component_faithful (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y)) :
    (componentFunctor (inclusion C)).Faithful := by
  refine ⟨?_⟩
  intro x y f g h
  have := hC x y
  exact inclusion_components_injective C x y h

theorem image_isIso (C : SimplicialCat.{u, u}) {x y : componentObjects (part C)}
    (f : x ⟶ y) : IsIso ((componentFunctor (inclusion C)).map f) := by
  obtain ⟨s, rfl⟩ := SSet.π₀.mk_surjective f
  change IsIso (C := componentObjects C) (X := x) (Y := y) (SSet.π₀.mk s.val)
  exact (hom_vertex_iff C _ _ s.val).mp s.property

theorem lift_isIso (C : SimplicialCat.{u, u}) {x y : componentObjects (part C)}
    (a : (componentFunctor (inclusion C)).obj x ⟶ (componentFunctor (inclusion C)).obj y)
    [IsIso a] : ∃ f : x ⟶ y, (componentFunctor (inclusion C)).map f = a := by
  obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective a
  refine ⟨SSet.π₀.mk ⟨v, ?_⟩, rfl⟩
  exact (hom_vertex_iff C _ _ v).mpr inferInstance

theorem component_isIso (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y))
    {x y : componentObjects (part C)} (f : x ⟶ y) : IsIso f := by
  let F := componentFunctor (inclusion C)
  have : F.Faithful := inclusion_component_faithful C hC
  have : IsIso (F.map f) := image_isIso C f
  obtain ⟨g, hg⟩ := lift_isIso C (inv (F.map f))
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply F.map_injective
    rw [F.map_comp, F.map_id, hg]
    exact IsIso.hom_inv_id (F.map f)
  · apply F.map_injective
    rw [F.map_comp, F.map_id, hg]
    exact IsIso.inv_hom_id (F.map f)

theorem component_groupoid (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y)) :
    HasActualComponentGroupoid (part C) :=
  ⟨Groupoid.ofIsIso (fun f ↦ component_isIso C hC f), rfl⟩

theorem replacement_part_groupoid (C : SimplicialCat.{u, u}) :
    HasActualComponentGroupoid (part (replacement.obj C)) :=
  component_groupoid _ (replacement_locallyKan C)

end
end DaggerActualIsomorphismPartComponents
