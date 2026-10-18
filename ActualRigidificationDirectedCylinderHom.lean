import ActualRigidificationDirectedIntervalObjects

/-! Hom comparison for the actual directed standard-interval cylinder. -/

set_option autoImplicit false
open CategoryTheory EnrichedCategory MonoidalCategory CartesianMonoidalCategory
open Opposite Simplicial HomotopicalAlgebra
open DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryRigidification.RigidificationVertices
open DaggerChosenRigidificationNecklace hiding thickeningUnit
open DaggerOrdinaryPiZeroCategory DaggerOrdinaryTranslation DaggerSSetGluing
open DaggerOriginalCounitRightConeRelativeHomotopy DaggerOriginalEnrichedHomTransport
open DaggerActualRigidificationDirectedIntervalObjects
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualRigidificationDirectedCylinderHom

noncomputable section

/-- Factoring through the actual rigidification of the point makes the edge image invertible. -/
theorem constant_edge_class_isIso {Y : SSet.{u}} (v : Y.obj (op ⦋0⦌)) :
    IsIso (classOfVertex (rigidification.obj Y)
      (((rigidification.map (SSet.const v : (Δ[1] : SSet.{u}) ⟶ Y)).map
        (endpoint 0) (endpoint 1)).app (op ⦋0⦌) edge)) := by
  have h : rigidification.map (SSet.const v : (Δ[1] : SSet.{u}) ⟶ Y) =
      rigidification.map (SSet.stdSimplex.isTerminalObj₀.from Δ[1]) ≫
        rigidification.map (SSet.const v : (Δ[0] : SSet.{u}) ⟶ Y) := by
    rw [← Functor.map_comp]
    rfl
  rw [h]
  let w := ((rigidification.map (SSet.stdSimplex.isTerminalObj₀.from Δ[1])).map
    (endpoint 0) (endpoint 1)).app (op ⦋0⦌) edge
  have : IsIso (classOfVertex (rigidification.obj Δ[0]) w) := point_vertex_class_isIso w
  change IsIso ((hFunctor
    (rigidification.map (SSet.const v : (Δ[0] : SSet.{u}) ⟶ Y))).map
      (classOfVertex (rigidification.obj Δ[0]) w))
  infer_instance

/-- Equality transports before an enriched map preserve invertibility of its vertex image. -/
theorem transported_image_class_isIso {A B : DaggerModels.SimplicialCat.{u, u}}
    (F : EnrichedFunctor SSet.{u} A.Obj B.Obj) {a b c d : A.Obj}
    (ha : a = c) (hb : b = d) (v : (a ⟶[SSet.{u}] b).obj (op ⦋0⦌))
    [IsIso (classOfVertex B ((F.map a b).app (op ⦋0⦌) v))] :
    IsIso (classOfVertex B
      ((targetHomTransport ha hb ≫ F.map c d).app (op ⦋0⦌) v)) := by
  cases ha
  cases hb
  simpa only [targetHomTransport, eqToHom_refl, Category.id_comp]
    using (inferInstanceAs (IsIso (classOfVertex B ((F.map a b).app (op ⦋0⦌) v))))

/-- A constant image of the literal vertical line supplies invertibility after the two casts. -/
theorem verticalEdge_image_class_isIso {X Y : SSet.{u}} (f : X ⊗ Δ[1] ⟶ Y)
    (a : (rigidification.obj X).Obj) (v : Y.obj (op ⦋0⦌))
    (h : vertexLine X a ≫ f = SSet.const v) :
    IsIso (classOfVertex (rigidification.obj Y)
      (((rigidification.map f).map
        ((rigidification.map (timeSlice X 0)).obj a)
        ((rigidification.map (timeSlice X 1)).obj a)).app (op ⦋0⦌) (verticalEdge X a))) := by
  have hc : rigidification.map (vertexLine X a) ≫ rigidification.map f =
      rigidification.map (SSet.const v : Δ[1] ⟶ Y) := by rw [← Functor.map_comp, h]
  have hi : IsIso (classOfVertex (rigidification.obj Y)
      (((rigidification.map (vertexLine X a) ≫ rigidification.map f).map
        (endpoint 0) (endpoint 1)).app (op ⦋0⦌) edge)) := by
    rw [hc]
    exact constant_edge_class_isIso v
  change IsIso (classOfVertex (rigidification.obj Y)
    (((rigidification.map f).map
      ((rigidification.map (vertexLine X a)).obj (endpoint 0))
      ((rigidification.map (vertexLine X a)).obj (endpoint 1))).app (op ⦋0⦌)
        (((rigidification.map (vertexLine X a)).map
          (endpoint 0) (endpoint 1)).app (op ⦋0⦌) edge))) at hi
  letI := hi
  exact transported_image_class_isIso (rigidification.map f)
    (vertexLine_endpoint X a 0) (vertexLine_endpoint X a 1)
      (((rigidification.map (vertexLine X a)).map
        (endpoint 0) (endpoint 1)).app (op ⦋0⦌) edge)

/-- The projection sends the whole vertical line to the actual constant simplex. -/
theorem vertexLine_fst (X : SSet.{u}) (a : (rigidification.obj X).Obj) :
    vertexLine X a ≫ fst X (Δ[1] : SSet.{u}) = SSet.const ((vertexEquiv X).symm a) := by
  simp only [vertexLine, CartesianMonoidalCategory.lift_fst]

/-- The second projection retains the exact time endpoint. -/
theorem timeSlice_snd_obj (X : SSet.{u}) (a : (rigidification.obj X).Obj) (t : Fin 2) :
    (rigidification.map (snd X (Δ[1] : SSet.{u}))).obj
      ((rigidification.map (timeSlice X t)).obj a) = endpoint t := by
  calc
    _ = (rigidification.map (snd X (Δ[1] : SSet.{u}))).obj
        ((rigidification.map (timeSlice X t)).obj
          (vertexEquiv X ((vertexEquiv X).symm a))) := by
      rw [(vertexEquiv X).apply_symm_apply]
    _ = vertexEquiv Δ[1] ((snd X (Δ[1] : SSet.{u})).app (op ⦋0⦌)
        ((timeSlice X t).app (op ⦋0⦌) ((vertexEquiv X).symm a))) := by
      rw [vertexEquiv_naturality, vertexEquiv_naturality]
    _ = endpoint t := rfl

/-- The actual first Hom projection is weak for each ordered pair of time endpoints. -/
theorem timeSlice_projection_GW (X : SSet.{u}) (a b : (rigidification.obj X).Obj)
    (s t : Fin 2) (h : s ≤ t) :
    GW ((rigidification.map (fst X (Δ[1] : SSet.{u}))).map
      ((rigidification.map (timeSlice X s)).obj a)
      ((rigidification.map (timeSlice X t)).obj b)) := by
  apply DaggerActualRigidificationSimplexHomContractibility.simplex_product_projection_GW
  rw [timeSlice_snd_obj, timeSlice_snd_obj]
  fin_cases s <;> fin_cases t
  · exact ⟨idVertex (rigidification.obj Δ[1]) (endpoint 0)⟩
  · exact ⟨edge⟩
  · exact False.elim ((by decide : ¬ ((1 : Fin 2) ≤ 0)) h)
  · exact ⟨idVertex (rigidification.obj Δ[1]) (endpoint 1)⟩

end
end DaggerActualRigidificationDirectedCylinderHom
