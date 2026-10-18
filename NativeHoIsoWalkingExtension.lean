import OriginalOrdinaryCoreKan
import OriginalOrdinaryCoreHomotopyInclusion
import NativeHoIsoTriangles
import NativeWalkingEdgeKanInclusion

/-! Invertible native edges extend to the entire original walking-isomorphism nerve. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerActualWalkingIsoCategoricalCylinder
open DaggerNativeWalkingEdgeKanInclusion DaggerNativeHoIsoTriangles
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerOriginalOrdinaryCoreKan
open DaggerOriginalOrdinaryCoreHomotopyInclusion
open DaggerOriginalOrdinaryKanCoreEdgeMaximality
open DaggerOriginalOrdinaryKanCoreKanInverseEdges
open DaggerOriginalQuasicategoryInverseEdgeRepresentatives
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeHoIsoWalkingExtension
noncomputable section

theorem kan_edge_extension (Z : SSet.{u}) [Z.KanComplex] (a : (Δ[1] : SSet.{u}) ⟶ Z) :
    ∃ H : J.{u} ⟶ Z, edgeInclusion.{u} ≫ H = a := by
  have ht := edgeInclusion_trivial_cofibration.{u}
  have : Cofibration edgeInclusion.{u} := (mem_trivialCofibrations_iff _).mp ht |>.1
  have : WeakEquivalence edgeInclusion.{u} := (mem_trivialCofibrations_iff _).mp ht |>.2
  let sq : CommSq a edgeInclusion.{u} (terminal.from Z) (terminal.from J.{u}) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_left⟩

theorem invertible_edge_extension (X : SSet.{u}) [X.Quasicategory]
    {x y : X _⦋0⦌} (e : SSet.Edge x y)
    [IsIso (SSet.Truncated.HomotopyCategory.homMk e)] :
    ∃ H : J.{u} ⟶ X, edgeInclusion.{u} ≫ H = SSet.yonedaEquiv.symm e.edge := by
  have : (ordinaryCoreCandidate X : SSet.{u}).KanComplex :=
    ordinaryCoreCandidate_kan X (native_inner_fillers X)
  have hm : e.edge ∈ (ordinaryCoreCandidate X).obj (op ⦋1⦌) :=
    (mem_ordinaryCoreCandidate_one_iff X e.edge).mpr
      ((edgeIsInvertible_iff_original_homMk_isIso X e).mpr inferInstance)
  let xK : (ordinaryCoreCandidate X : SSet.{u}) _⦋0⦌ :=
    ⟨x, vertex_mem_ordinaryCoreCandidate X x⟩
  let yK : (ordinaryCoreCandidate X : SSet.{u}) _⦋0⦌ :=
    ⟨y, vertex_mem_ordinaryCoreCandidate X y⟩
  let eK : SSet.Edge xK yK := SSet.Edge.mk ⟨e.edge, hm⟩
    (by apply Subtype.ext; exact e.src_eq) (by apply Subtype.ext; exact e.tgt_eq)
  obtain ⟨H, hH⟩ := kan_edge_extension (ordinaryCoreCandidate X : SSet.{u})
    (SSet.yonedaEquiv.symm eK.edge)
  refine ⟨H ≫ (ordinaryCoreCandidate X).ι, ?_⟩
  rw [← Category.assoc, hH]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

def oneInclusion : (Δ[0] : SSet.{u}) ⟶ J.{u} :=
  SSet.const (ComposableArrows.mk₀ (parameterObject true))

theorem one_edgeInclusion : SSet.stdSimplex.δ 0 ≫ edgeInclusion.{u} = oneInclusion.{u} := by
  apply NatTrans.ext
  funext q s
  apply nerve.ext_of_isThin
  funext i
  change parameterObject (decide ((SimplexCategory.δ (0 : Fin 2)).toOrderHom
    ((SSet.stdSimplex.objEquiv s).toOrderHom i) = 1)) = parameterObject true
  have hz : (SSet.stdSimplex.objEquiv s).toOrderHom i = (0 : Fin 1) :=
    Subsingleton.elim (α := Fin 1) _ _
  rw [hz]
  rfl

theorem edge_map_src {X : SSet.{u}} {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    SSet.stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm e.edge = SSet.yonedaEquiv.symm x := by
  apply SSet.yonedaEquiv.injective
  rw [yonedaEquiv_coface, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact e.src_eq

theorem edge_map_tgt {X : SSet.{u}} {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    SSet.stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm e.edge = SSet.yonedaEquiv.symm y := by
  apply SSet.yonedaEquiv.injective
  rw [yonedaEquiv_coface, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact e.tgt_eq

theorem iso_endpoint_extension (X : SSet.{u}) [X.Quasicategory]
    (x y : X _⦋0⦌)
    (e : SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) x ≅
      SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) y) :
    ∃ H : J.{u} ⟶ X, zeroInclusion.{u} ≫ H = SSet.yonedaEquiv.symm x ∧
      oneInclusion.{u} ≫ H = SSet.yonedaEquiv.symm y := by
  let xK : (ordinaryCoreCandidate X : SSet.{u}) _⦋0⦌ :=
    ⟨x, vertex_mem_ordinaryCoreCandidate X x⟩
  let yK : (ordinaryCoreCandidate X : SSet.{u}) _⦋0⦌ :=
    ⟨y, vertex_mem_ordinaryCoreCandidate X y⟩
  obtain ⟨k, hk⟩ := core_edge_preimage_of_isIso X (native_inner_fillers X)
    (x := xK) (y := yK) e.hom
  let a := k.map (ordinaryCoreCandidate X).ι
  have ha : IsIso (SSet.Truncated.HomotopyCategory.homMk a) := by
    change IsIso ((coreHomotopyInclusion X).map (SSet.Truncated.HomotopyCategory.homMk k))
    rw [hk]
    infer_instance
  obtain ⟨H, hH⟩ := invertible_edge_extension X a
  refine ⟨H, ?_, ?_⟩
  · rw [← zero_edgeInclusion, Category.assoc, hH]
    exact edge_map_src a
  · rw [← one_edgeInclusion, Category.assoc, hH]
    exact edge_map_tgt a

theorem ho_iso_endpoint_extension (X : SSet.{u}) [X.Quasicategory]
    (x y : SSet.hoFunctor.obj X) (e : x ≅ y) :
    ∃ H : J.{u} ⟶ X,
      zeroInclusion.{u} ≫ H = SSet.yonedaEquiv.symm (SSet.hoFunctor.obj.equiv X x) ∧
      oneInclusion.{u} ≫ H = SSet.yonedaEquiv.symm (SSet.hoFunctor.obj.equiv X y) := by
  obtain ⟨a, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective x
  obtain ⟨b, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective y
  exact iso_endpoint_extension X a b e

theorem edgeInclusion_eq_yoneda : edgeInclusion.{u} = SSet.yonedaEquiv.symm
    (DaggerNativeWalkingSimplexWords.parameterSimplex.{u}
      (fun i : Fin 2 ↦ decide (i = 1))) := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply nerve.ext_of_isThin
  rfl

end
end DaggerNativeHoIsoWalkingExtension
