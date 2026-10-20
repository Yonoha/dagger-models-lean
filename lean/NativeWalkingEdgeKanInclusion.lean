import ActualTaggedWalkingIsoSourceHomotopyReconciled
import NativeStandardSimplexContraction
import NativeWalkingSimplexWords

/-! The original directed edge embeds in the original J by a Kan trivial cofibration. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerActualWalkingIsoCategoricalCylinder
open DaggerActualTaggedWalkingIsoSourceHomotopy DaggerNativeStandardSimplexContraction
open DaggerNativeSSetRawHomotopyEquivalenceWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeWalkingEdgeKanInclusion
noncomputable section

def edgeInclusion : (Δ[1] : SSet.{u}) ⟶ J.{u} where
  app q s :=
    { obj := fun i ↦ parameterObject (decide ((SSet.stdSimplex.objEquiv s).toOrderHom i = 1))
      map := fun _ ↦ ⟨⟨⟩⟩
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
  naturality _ _ _ := by
    funext s
    apply nerve.ext_of_isThin
    rfl

theorem edgeInclusion_mono : Mono edgeInclusion.{u} := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro q
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro s t h
  ext i
  have hi := congrArg (fun z ↦ (ULift.down (z.obj i)).as) h
  change decide ((SSet.stdSimplex.objEquiv s).toOrderHom i = 1) =
    decide ((SSet.stdSimplex.objEquiv t).toOrderHom i = 1) at hi
  have hinj : ∀ a b : Fin 2, decide (a = 1) = decide (b = 1) → a = b := by decide
  exact congrArg Fin.val (hinj _ _ hi)

theorem zero_edgeInclusion :
    SSet.stdSimplex.δ 1 ≫ edgeInclusion.{u} = zeroInclusion.{u} := by
  apply NatTrans.ext
  funext q s
  apply nerve.ext_of_isThin
  funext i
  change parameterObject (decide ((SSet.stdSimplex.objEquiv
    ((SSet.stdSimplex.δ 1).app q s)).toOrderHom i = 1)) = parameterObject false
  congr 1
  change decide ((SimplexCategory.δ (1 : Fin 2)).toOrderHom
    ((SSet.stdSimplex.objEquiv s).toOrderHom i) = 1) = false
  have hz : (SSet.stdSimplex.objEquiv s).toOrderHom i = (0 : Fin 1) :=
    Subsingleton.elim (α := Fin 1) _ _
  rw [hz]
  rfl

theorem edge_collapse_zero :
    edgeInclusion.{u} ≫ collapse.{u} ≫ SSet.stdSimplex.δ 1 =
      SSet.const (firstVertex.{u} 1) := by
  apply NatTrans.ext
  funext q s
  ext i
  rfl

def edgeHomotopyEquiv : SSet.HomotopyEquiv (Δ[1] : SSet.{u}) J.{u} where
  hom := edgeInclusion
  inv := collapse ≫ SSet.stdSimplex.δ 1
  homInvId := (simplexContractible 1).h.congr edge_collapse_zero.symm rfl
  invHomId := by
    simpa only [Category.assoc, zero_edgeInclusion] using contraction.{u}

theorem edgeInclusion_weak : WeakEquivalence edgeInclusion.{u} :=
  rawHomotopyEquiv_weakEquivalence edgeHomotopyEquiv

theorem edgeInclusion_trivial_cofibration :
    trivialCofibrations SSet.{u} edgeInclusion.{u} := by
  have : Mono edgeInclusion.{u} := edgeInclusion_mono
  exact (mem_trivialCofibrations_iff _).mpr
    ⟨(SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance, edgeInclusion_weak⟩

end
end DaggerNativeWalkingEdgeKanInclusion
