import NativeDaggerUnderlyingIso
import ActualRigHomWeakCoreRigidification
import ActualRightLeftOppositeWeakTransfer
import NativePrefixMappingWeakIsoSquare

/-! Native DS and the ORIGINAL dagger ISO transfer original Rig-Hom local weakness
onto the SAME original LEFT mapping maps, for ALL original dagger quasi-category inputs.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerActualQuasicategoryMappingFibres DaggerNativePrefixMappingTransportIso
open DaggerNativePrefixMappingWeakIsoSquare DaggerNativeDaggerUnderlyingIso
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualDaggerRigLocalLeftWeak
noncomputable section

theorem left_map_weak {X Y : DaggerSSet.{u}} [X.toSSet.Quasicategory] [Y.toSSet.Quasicategory]
    (f : X ⟶ Y)
    (hf : ∀ a b : (rigidification.obj X.toSSet).Obj,
      WeakEquivalence ((rigidification.map f.hom).map a b))
    (x y : X.toSSet.obj (op ⦋0⦌)) : WeakEquivalence (map f.hom ⦋0⦌ x y) := by
  let g := SSet.opFunctor.map f.hom
  have hAll (a b : (SSet.opFunctor.obj X.toSSet).obj (op ⦋0⦌)) :
      WeakEquivalence (map g ⦋0⦌ a b) :=
    DaggerActualRightLeftOppositeWeakTransfer.left_op_map_weak_of_RigHom_weak
      f.hom hf (SSet.opObjEquiv b) (SSet.opObjEquiv a)
  have hTo (a b : (SSet.opFunctor.obj X.toSSet).obj (op ⦋0⦌))
      (c d : (SSet.opFunctor.obj Y.toSSet).obj (op ⦋0⦌))
      (hc : g.app (op ⦋0⦌) a = c) (hd : g.app (op ⦋0⦌) b = d) :
      WeakEquivalence (mapTo g ⦋0⦌ a b c d hc hd) := by
    subst c
    subst d
    exact hAll a b
  have hs : (daggerIso X).hom ≫ g = f.hom ≫ (daggerIso Y).hom := f.comm.symm
  apply (map_weak_iff f.hom g (daggerIso X) (daggerIso Y) hs ⦋0⦌ x y).mpr
  exact hTo _ _ _ _ _ _

theorem mapTo_weak_iff {X Y : SSet.{u}} (f : X ⟶ Y) (k : SimplexCategory)
    (σ : X.obj (op k)) (b : X.obj (op ⦋0⦌)) (τ : Y.obj (op k))
    (c : Y.obj (op ⦋0⦌)) (hσ : f.app (op k) σ = τ) (hb : f.app (op ⦋0⦌) b = c) :
    WeakEquivalence (mapTo f k σ b τ c hσ hb) ↔ WeakEquivalence (map f k σ b) := by
  subst τ
  subst c
  rfl

theorem left_op_weak_of_left_maps_weak {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (hf : ∀ x y : X.toSSet.obj (op ⦋0⦌), WeakEquivalence (map f.hom ⦋0⦌ x y))
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    WeakEquivalence (map (SSet.opFunctor.map f.hom) ⦋0⦌
      (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)) := by
  let g := SSet.opFunctor.map f.hom
  let eX := daggerIso X
  let eY := daggerIso Y
  have hs : eX.hom ≫ g = f.hom ≫ eY.hom := f.comm.symm
  have hw := (map_weak_iff f.hom g eX eY hs ⦋0⦌ y x).mp (hf y x)
  have hG := (mapTo_weak_iff g ⦋0⦌
    (eX.hom.app (op ⦋0⦌) y) (eX.hom.app (op ⦋0⦌) x)
    (eY.hom.app (op ⦋0⦌) (f.hom.app (op ⦋0⦌) y))
    (eY.hom.app (op ⦋0⦌) (f.hom.app (op ⦋0⦌) x))
    (congrFun (NatTrans.congr_app hs (op ⦋0⦌)) y)
    (congrFun (NatTrans.congr_app hs (op ⦋0⦌)) x)).mp hw
  have hy : eX.hom.app (op ⦋0⦌) y = SSet.opObjEquiv.symm y := vertex X y
  have hx : eX.hom.app (op ⦋0⦌) x = SSet.opObjEquiv.symm x := vertex X x
  rw [hy, hx] at hG
  exact hG

theorem rig_hom_weak_of_left_maps_weak {X Y : DaggerSSet.{u}}
    [X.toSSet.Quasicategory] [Y.toSSet.Quasicategory] (f : X ⟶ Y)
    (hf : ∀ x y : X.toSSet.obj (op ⦋0⦌), WeakEquivalence (map f.hom ⦋0⦌ x y))
    (a b : (rigidification.obj X.toSSet).Obj) :
    WeakEquivalence ((rigidification.map f.hom).map a b) := by
  obtain ⟨x, rfl⟩ := (RigidificationVertices.vertexEquiv X.toSSet).surjective a
  obtain ⟨y, rfl⟩ := (RigidificationVertices.vertexEquiv X.toSSet).surjective b
  apply (DaggerActualRigHomWeakCoreRigidification.homMap_weak_iff_raw f.hom x y).mp
  apply (DaggerActualGeneralIntrinsicLocalComparison.mapping_weak_iff_hom_weak f.hom x y).mp
  apply (DaggerActualRightLeftOppositeWeakTransfer.right_weak_iff_left_op_weak f.hom x y).mpr
  exact left_op_weak_of_left_maps_weak f hf x y

theorem rig_hom_weak_iff_left_maps_weak {X Y : DaggerSSet.{u}}
    [X.toSSet.Quasicategory] [Y.toSSet.Quasicategory] (f : X ⟶ Y) :
    (∀ a b : (rigidification.obj X.toSSet).Obj,
      WeakEquivalence ((rigidification.map f.hom).map a b)) ↔
      ∀ x y : X.toSSet.obj (op ⦋0⦌), WeakEquivalence (map f.hom ⦋0⦌ x y) := by
  constructor
  · exact fun hf x y ↦ left_map_weak f hf x y
  · exact rig_hom_weak_of_left_maps_weak f

end
end DaggerActualDaggerRigLocalLeftWeak
