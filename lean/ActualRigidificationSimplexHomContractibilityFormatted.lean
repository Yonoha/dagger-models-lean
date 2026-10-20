import ActualThickeningPathContractibilityFormatted

/-! Nonempty Hom spaces of the actual rigidified simplex are weakly contractible. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory DaggerModels
open DaggerModels.OrdinaryRigidification
open DaggerOriginalProductGadget DaggerOriginalFlagFlankification
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualRigidificationSimplexHomContractibility

noncomputable section

/-- The two literal terminal targets give equivalent weak-contractibility predicates. -/
theorem point_GW_toUnit {X : SSet.{u}} (h : DaggerSSetGluing.GW (pointMap X)) :
    DaggerSSetGluing.GW (toUnit X) := by
  let e : constantSSet PUnit.{u + 1} ≅ 𝟙_ (SSet.{u}) :=
    pointIsTerminal.uniqueUpToIso
      (SemiCartesianMonoidalCategory.isTerminalTensorUnit (C := SSet.{u}))
  have : WeakEquivalence (pointMap X) := (DaggerSSetGluing.weakEquivalence_iff_GW _).2 h
  have hf : pointMap X ≫ e.hom = toUnit X :=
    (SemiCartesianMonoidalCategory.isTerminalTensorUnit (C := SSet.{u})).hom_ext _ _
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).1
  rw [← hf]
  infer_instance

/-- A vertex in an original simplex Hom supplies the ordering needed for its contraction. -/
theorem simplex_hom_toUnit_GW (n : ℕ)
    (a b : (rigidification.obj (Δ[n] : SSet.{u})).Obj)
    (h : Nonempty ((a ⟶[SSet.{u}] b).obj (op ⦋0⦌))) :
    DaggerSSetGluing.GW (toUnit (a ⟶[SSet.{u}] b)) := by
  let e := rigidificationSimplexIso.{u}.app ⦋n⦌
  let p := e.hom.map a b
  let Y : SSet.{u} := (e.hom.obj a ⟶[SSet.{u}] e.hom.obj b)
  have : IsIso p := inferInstance
  have : WeakEquivalence p := inferInstance
  obtain ⟨v⟩ := h
  have hij : (e.hom.obj a).as ≤ (e.hom.obj b).as :=
    SimplicialThickening.Path.le ((p.app (op ⦋0⦌) v).obj 0)
  have hy : DaggerSSetGluing.GW (pointMap Y) :=
    DaggerActualThickeningPathContractibility.path_point_GW _ _ hij
  have : WeakEquivalence (toUnit Y) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).2 (point_GW_toUnit hy)
  have hf : p ≫ toUnit Y = toUnit (a ⟶[SSet.{u}] b) :=
    (SemiCartesianMonoidalCategory.isTerminalTensorUnit (C := SSet.{u})).hom_ext _ _
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).1
  rw [← hf]
  infer_instance

/-- The actual product projection is weak on every Hom with a nonempty simplex Hom factor. -/
theorem simplex_product_projection_GW (X : SSet.{u}) (n : ℕ)
    (z w : (rigidification.obj (X ⊗ (Δ[n] : SSet.{u}))).Obj)
    (h : Nonempty (((rigidification.map (snd X (Δ[n] : SSet.{u}))).obj z ⟶[SSet.{u}]
      (rigidification.map (snd X (Δ[n] : SSet.{u}))).obj w).obj (op ⦋0⦌))) :
    DaggerSSetGluing.GW ((rigidification.map (fst X (Δ[n] : SSet.{u}))).map z w) :=
  DaggerActualRigidificationProductHomProjection.projection_GW z w
    (simplex_hom_toUnit_GW n _ _ h)

end
end DaggerActualRigidificationSimplexHomContractibility
