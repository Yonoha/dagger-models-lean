import ActualInnerConeIntervalComparison
import ActualRightConeObjectClassification
import NativeThinNerveVertexExt
import ActualGeneralRightConeKan

/-! The SAME inner-cone right mapping fibre is Kan and has weak collapse, independently of RigHom.
-/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory
open DaggerOriginalCounitRightCone DaggerActualGeneralRightConeMapping
open DaggerActualInnerConeIntervalComparison DaggerNativeInnerHornFactorization
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualInnerConeRightMappingContractible
noncomputable section

theorem maps_to_simplex_ext (n : ℕ) {X : SSet.{u}}
    (f g : X ⟶ (Δ[n] : SSet.{u}))
    (h : ∀ x : X.obj (op ⦋0⦌), f.app (op ⦋0⦌) x = g.app (op ⦋0⦌) x) : f = g := by
  let e := SSet.stdSimplex.isoNerve.{u} n
  apply (cancel_mono e.hom).mp
  apply DaggerNativeThinNerveVertexExt.nerveMap_ext_of_vertices (ULift.{u} (Fin (n + 1)))
  intro x
  exact congrArg (e.hom.app (op ⦋0⦌)) (h x)

instance mappingComponentSubsingleton (n : ℕ) (a b : (Δ[n] : SSet.{u}).obj (op ⦋0⦌))
    (q : SimplexCategoryᵒᵖ) : Subsingleton ((rightMapping (Δ[n] : SSet.{u}) a b).obj q) where
  allEq s t := by
    apply Subtype.ext
    apply maps_to_simplex_ext n
    intro x
    rcases DaggerActualRightConeObjectClassification.vertex_cases q.unop.len x with rfl | rfl
    · exact s.property.1.trans t.property.1.symm
    · exact s.property.2.trans t.property.2.symm

private abbrev intervalMapping : SSet.{u} := rightMapping (Δ[1] : SSet.{u}) zeroVertex oneVertex

def pointMap : intervalMapping.{u} ⟶ (Δ[0] : SSet.{u}) :=
  SSet.stdSimplex.isTerminalObj₀.from _

def fromPoint : (Δ[0] : SSet.{u}) ⟶ intervalMapping.{u} where
  app q _ := ⟨DaggerOriginalCounitRightConeContractibilityRetraction.projection q.unop.len,
    projection_alpha_value q.unop.len, projection_omega_value q.unop.len⟩
  naturality q r α := by
    funext s
    exact Subsingleton.elim _ _

def intervalMappingIso : intervalMapping.{u} ≅ (Δ[0] : SSet.{u}) where
  hom := pointMap
  inv := fromPoint
  hom_inv_id := by
    apply NatTrans.ext
    funext q s
    exact Subsingleton.elim _ _
  inv_hom_id := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

theorem interval_pointMap_weak : WeakEquivalence pointMap.{u} := by
  change WeakEquivalence intervalMappingIso.hom
  infer_instance

theorem innerCone_mapping_kan (n : ℕ) :
    (rightMapping (replacement.obj (cone.{u} n)) (sourceAlpha n) (sourceOmega n)).KanComplex :=
  DaggerActualGeneralRightConeKan.rightMapping_kan _ _ _

theorem innerCone_mapping_point_weak (n : ℕ) : WeakEquivalence
    (SSet.stdSimplex.isTerminalObj₀.from
      (rightMapping (replacement.obj (cone.{u} n)) (sourceAlpha n) (sourceOmega n))) := by
  have : WeakEquivalence (mappingComparison.{u} n) := mappingComparison_weak n
  have : WeakEquivalence pointMap.{u} := interval_pointMap_weak
  have h : mappingComparison.{u} n ≫ pointMap = SSet.stdSimplex.isTerminalObj₀.from _ :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [← h]
  infer_instance

theorem innerCone_mapping_toUnit_weak (n : ℕ) : WeakEquivalence
    (toUnit (rightMapping (replacement.obj (cone.{u} n)) (sourceAlpha n) (sourceOmega n))) := by
  let E := rightMapping (replacement.obj (cone.{u} n)) (sourceAlpha n) (sourceOmega n)
  let e := SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso (isTerminalTensorUnit (C := SSet.{u}))
  have : WeakEquivalence (SSet.stdSimplex.isTerminalObj₀.from E) := innerCone_mapping_point_weak n
  have h : SSet.stdSimplex.isTerminalObj₀.from E ≫ e.hom = toUnit E :=
    isTerminalTensorUnit.hom_ext _ _
  rw [← h]
  infer_instance

end
end DaggerActualInnerConeRightMappingContractible
