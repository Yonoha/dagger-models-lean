import ActualRigidificationDirectedCylinderHom

/-! A relative directed homotopy compares the literal rigidification Hom maps. -/

set_option autoImplicit false
open CategoryTheory EnrichedCategory MonoidalCategory CartesianMonoidalCategory
open Opposite Simplicial HomotopicalAlgebra
open DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryRigidification.RigidificationVertices
open DaggerOrdinaryPiZeroCategory DaggerOrdinaryTranslation DaggerSSetGluing
open DaggerOriginalCounitRightConeRelativeHomotopy DaggerOriginalEnrichedHomTransport
open DaggerActualRigidificationDirectedIntervalObjects
open DaggerActualRigidificationDirectedCylinderHom
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualRigidificationRelativeDirectedHomotopy

noncomputable section

/-- Each actual time slice is a section of the first simplicial projection. -/
theorem timeSlice_fst (X : SSet.{u}) (t : Fin 2) :
    timeSlice X t ≫ fst X (Δ[1] : SSet.{u}) = 𝟙 X := rfl

/-- The same-endpoint Hom of either actual time slice is geometrically weak. -/
theorem endpoint_hom_GW (X : SSet.{u}) (t : Fin 2)
    (a b : (rigidification.obj X).Obj) : GW ((rigidification.map (timeSlice X t)).map a b) := by
  have h : rigidification.map (timeSlice X t) ≫
      rigidification.map (fst X (Δ[1] : SSet.{u})) = 𝟙 (rigidification.obj X) := by
    rw [← Functor.map_comp, timeSlice_fst, CategoryTheory.Functor.map_id]
  have hid : GW (𝟙 (a ⟶[SSet.{u}] b)) := (weakEquivalence_iff_GW _).1 inferInstance
  have hc := (GW_functorHom_congr h a b).2 hid
  have : WeakEquivalence ((rigidification.map (fst X (Δ[1] : SSet.{u}))).map
      ((rigidification.map (timeSlice X t)).obj a)
      ((rigidification.map (timeSlice X t)).obj b)) :=
    (weakEquivalence_iff_GW _).2 (timeSlice_projection_GW X a b t t le_rfl)
  have : WeakEquivalence ((rigidification.map (timeSlice X t)).map a b ≫
      (rigidification.map (fst X (Δ[1] : SSet.{u}))).map
        ((rigidification.map (timeSlice X t)).obj a)
        ((rigidification.map (timeSlice X t)).obj b)) := (weakEquivalence_iff_GW _).2 hc
  exact (weakEquivalence_iff_GW _).1
    (weakEquivalence_of_postcomp ((rigidification.map (timeSlice X t)).map a b)
      ((rigidification.map (fst X (Δ[1] : SSet.{u}))).map
        ((rigidification.map (timeSlice X t)).obj a)
        ((rigidification.map (timeSlice X t)).obj b)))

/-- Fixed images of the two vertical lines compare the original endpoint Hom maps. -/
theorem homotopy_endpoint_GW_iff {X Y : SSet.{u}} (H : X ⊗ Δ[1] ⟶ Y)
    (a b : (rigidification.obj X).Obj) (v w : Y.obj (op ⦋0⦌))
    (ha : vertexLine X a ≫ H = SSet.const v)
    (hb : vertexLine X b ≫ H = SSet.const w) :
    GW ((rigidification.map H).map ((rigidification.map (timeSlice X 0)).obj a)
      ((rigidification.map (timeSlice X 0)).obj b)) ↔
    GW ((rigidification.map H).map ((rigidification.map (timeSlice X 1)).obj a)
      ((rigidification.map (timeSlice X 1)).obj b)) := by
  have := verticalEdge_image_class_isIso (fst X (Δ[1] : SSet.{u})) a
    ((vertexEquiv X).symm a) (vertexLine_fst X a)
  have := verticalEdge_image_class_isIso (fst X (Δ[1] : SSet.{u})) b
    ((vertexEquiv X).symm b) (vertexLine_fst X b)
  have := verticalEdge_image_class_isIso H a v ha
  have := verticalEdge_image_class_isIso H b w hb
  exact DaggerActualEnrichedDirectedCylinder.endpoint_map_GW_iff
    (rigidification.map (fst X (Δ[1] : SSet.{u}))) (rigidification.map H)
    (verticalEdge X a) (verticalEdge X b)
    (timeSlice_projection_GW X a b 0 0 le_rfl)
    (timeSlice_projection_GW X a b 0 1 (by decide))
    (timeSlice_projection_GW X a b 1 1 le_rfl)

/-- A directed deformation from the identity, relative to both vertices, gives the actual Hom W. -/
theorem endomorphism_GW (X : SSet.{u}) (H : X ⊗ Δ[1] ⟶ X) (t : X ⟶ X)
    (h₀ : timeSlice X 0 ≫ H = 𝟙 X) (h₁ : timeSlice X 1 ≫ H = t)
    (a b : (rigidification.obj X).Obj)
    (ha : vertexLine X a ≫ H = SSet.const ((vertexEquiv X).symm a))
    (hb : vertexLine X b ≫ H = SSet.const ((vertexEquiv X).symm b)) :
    GW ((rigidification.map t).map a b) := by
  have heq₀ : rigidification.map (timeSlice X 0) ≫ rigidification.map H =
      𝟙 (rigidification.obj X) := by rw [← Functor.map_comp, h₀, CategoryTheory.Functor.map_id]
  have hid : GW (𝟙 (a ⟶[SSet.{u}] b)) := (weakEquivalence_iff_GW _).1 inferInstance
  have hc₀ := (GW_functorHom_congr heq₀ a b).2 hid
  have : WeakEquivalence ((rigidification.map (timeSlice X 0)).map a b) :=
    (weakEquivalence_iff_GW _).2 (endpoint_hom_GW X 0 a b)
  have : WeakEquivalence ((rigidification.map (timeSlice X 0)).map a b ≫
      (rigidification.map H).map ((rigidification.map (timeSlice X 0)).obj a)
        ((rigidification.map (timeSlice X 0)).obj b)) := (weakEquivalence_iff_GW _).2 hc₀
  have hf₀ := (weakEquivalence_iff_GW _).1
    (weakEquivalence_of_precomp ((rigidification.map (timeSlice X 0)).map a b)
      ((rigidification.map H).map ((rigidification.map (timeSlice X 0)).obj a)
        ((rigidification.map (timeSlice X 0)).obj b)))
  have hf₁ := (homotopy_endpoint_GW_iff H a b _ _ ha hb).1 hf₀
  have : WeakEquivalence ((rigidification.map H).map
      ((rigidification.map (timeSlice X 1)).obj a)
      ((rigidification.map (timeSlice X 1)).obj b)) := (weakEquivalence_iff_GW _).2 hf₁
  have : WeakEquivalence ((rigidification.map (timeSlice X 1)).map a b) :=
    (weakEquivalence_iff_GW _).2 (endpoint_hom_GW X 1 a b)
  have heq₁ : rigidification.map (timeSlice X 1) ≫ rigidification.map H =
      rigidification.map t := by rw [← Functor.map_comp, h₁]
  apply (GW_functorHom_congr heq₁ a b).1
  apply (weakEquivalence_iff_GW _).1
  change WeakEquivalence ((rigidification.map (timeSlice X 1)).map a b ≫
    (rigidification.map H).map ((rigidification.map (timeSlice X 1)).obj a)
      ((rigidification.map (timeSlice X 1)).obj b))
  infer_instance

end
end DaggerActualRigidificationRelativeDirectedHomotopy
