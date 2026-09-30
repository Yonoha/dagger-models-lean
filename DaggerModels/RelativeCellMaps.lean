import DaggerModels.RelativeCellBoundary
import DaggerModels.RelativeSkeleton
import DaggerModels.FreeDaggerPushout

/-!
# Characteristic maps into relative dagger skeleta

For the relative boundary-cell construction in Part I, `dj.lem.free-cof`, a new
nondegenerate simplex gives a characteristic map into the next relative stage, while its
boundary maps into the current stage. The free--forgetful adjunction gives genuine dagger
cell maps and the attachment square commutes. No monicity of a characteristic map is assumed.
-/

open CategoryTheory Limits Simplicial Opposite

universe u

namespace DaggerModels.RelativeCellMaps

open DaggerSSet

variable {X Y : DaggerSSet.{u}} (i : X ⟶ Y) [Mono i]

local instance : Mono i.hom := (mono_iff_mono_hom i).1 inferInstance

/-- The actual Yoneda characteristic map of the chosen nondegenerate simplex. -/
def characteristicMap {n : ℕ} (σ : Y.toSSet.nonDegenerate n) :
    (Δ[n] : SSet.{u}) ⟶ Y.toSSet :=
  SSet.yonedaEquiv.symm σ.1

/-- The characteristic map factors through the actual next relative stage. -/
def cellLift {n : ℕ} (σ : Y.toSSet.nonDegenerate n) :
    (Δ[n] : SSet.{u}) ⟶ ((relativeSkeleton i).obj (n + 1)).toSSet :=
  SSet.Subcomplex.lift (characteristicMap σ) (by
    rw [SSet.Subcomplex.range_eq_ofSimplex, SSet.Subcomplex.ofSimplex_le_iff]
    simpa only [characteristicMap, Equiv.apply_symm_apply] using
      (SSet.mem_skeletonOfMono_obj_iff_of_nonDegenerate i.hom σ (n + 1)).mpr
        (Or.inr (Nat.lt_succ_self n)))

/-- The lifted cell retains its characteristic map after inclusion in the target. -/
@[reassoc (attr := simp)]
theorem cellLift_inclusion {n : ℕ} (σ : Y.toSSet.nonDegenerate n) :
    cellLift i σ ≫ ((relativeSkeletonInclusion i).app (n + 1)).hom =
      characteristicMap σ := rfl

/-- Every component of the lift has the specified ambient simplex as its value. -/
@[simp] theorem cellLift_app_val {n : ℕ} (σ : Y.toSSet.nonDegenerate n)
    (k : SimplexCategoryᵒᵖ) (a : (Δ[n] : SSet.{u}).obj k) :
    ((cellLift i σ).app k a).1 = Y.toSSet.map a.down.op σ.1 := rfl

/-- The boundary of a simplex outside the original image lies in the current relative stage. -/
def boundaryLift {n : ℕ} (σ : Y.toSSet.nonDegenerate n)
    (hσ : σ.1 ∉ Set.range (i.hom.app (op ⦋n⦌))) :
    (SSet.boundary.{u} n).toSSet ⟶ ((relativeSkeleton i).obj n).toSSet :=
  SSet.Subcomplex.lift ((SSet.boundary n).ι ≫ characteristicMap σ) (by
    intro k y hy
    obtain ⟨a, rfl⟩ := hy
    change a.1 ∈ ((SSet.skeletonOfMono i.hom n).preimage
      (SSet.yonedaEquiv.symm σ.1)).obj k
    rw [RelativeCellBoundary.characteristic_preimage_relativeSkeleton i.hom n σ hσ]
    exact a.2)

/-- The lifted boundary retains its original boundary characteristic map. -/
@[reassoc (attr := simp)]
theorem boundaryLift_inclusion {n : ℕ} (σ : Y.toSSet.nonDegenerate n)
    (hσ : σ.1 ∉ Set.range (i.hom.app (op ⦋n⦌))) :
    boundaryLift i σ hσ ≫ ((relativeSkeletonInclusion i).app n).hom =
      (SSet.boundary n).ι ≫ characteristicMap σ := rfl

/-- The boundary lift and the cell lift agree through the actual stage inclusion. -/
theorem boundaryLift_stageInclusion {n : ℕ} (σ : Y.toSSet.nonDegenerate n)
    (hσ : σ.1 ∉ Set.range (i.hom.app (op ⦋n⦌))) :
    boundaryLift i σ hσ ≫ ((relativeSkeleton i).map (homOfLE (Nat.le_succ n))).hom =
      (SSet.boundary n).ι ≫ cellLift i σ := by
  ext k a
  apply Subtype.ext
  rfl

variable (F : SSet.{u} ⥤ DaggerSSet.{u}) (adj : F ⊣ forget)

/-- Transpose the lifted characteristic map through the actual free adjunction. -/
noncomputable def cellMap {n : ℕ} (σ : Y.toSSet.nonDegenerate n) :
    F.obj (Δ[n] : SSet.{u}) ⟶ (relativeSkeleton i).obj (n + 1) :=
  (adj.homEquiv _ _).symm (cellLift i σ)

/-- Transpose the lifted boundary map through the same adjunction. -/
noncomputable def boundaryMap {n : ℕ} (σ : Y.toSSet.nonDegenerate n)
    (hσ : σ.1 ∉ Set.range (i.hom.app (op ⦋n⦌))) :
    F.obj (SSet.boundary.{u} n).toSSet ⟶ (relativeSkeleton i).obj n :=
  (adj.homEquiv _ _).symm (boundaryLift i σ hσ)

/-- Restriction of the free cell along the adjunction unit is the specified lift. -/
theorem cellMap_unit {n : ℕ} (σ : Y.toSSet.nonDegenerate n) :
    adj.unit.app (Δ[n] : SSet.{u}) ≫ (cellMap i F adj σ).hom = cellLift i σ := by
  change (adj.homEquiv (Δ[n] : SSet.{u}) ((relativeSkeleton i).obj (n + 1)))
    ((adj.homEquiv _ _).symm (cellLift i σ)) = cellLift i σ
  exact Equiv.apply_symm_apply _ _

/-- Restriction of the free boundary along the same unit is the specified boundary lift. -/
theorem boundaryMap_unit {n : ℕ} (σ : Y.toSSet.nonDegenerate n)
    (hσ : σ.1 ∉ Set.range (i.hom.app (op ⦋n⦌))) :
    adj.unit.app (SSet.boundary.{u} n).toSSet ≫ (boundaryMap i F adj σ hσ).hom =
      boundaryLift i σ hσ := by
  change (adj.homEquiv (SSet.boundary.{u} n).toSSet ((relativeSkeleton i).obj n))
    ((adj.homEquiv _ _).symm (boundaryLift i σ hσ)) = boundaryLift i σ hσ
  exact Equiv.apply_symm_apply _ _

/-- The genuine free boundary inclusion gives the commuting attachment square. -/
theorem cellMap_boundary {n : ℕ} (σ : Y.toSSet.nonDegenerate n)
    (hσ : σ.1 ∉ Set.range (i.hom.app (op ⦋n⦌))) :
    F.map (SSet.boundary n).ι ≫ cellMap i F adj σ =
      boundaryMap i F adj σ hσ ≫ (relativeSkeleton i).map (homOfLE (Nat.le_succ n)) := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [cellMap, boundaryMap, Equiv.apply_symm_apply]
  change (SSet.boundary n).ι ≫ cellLift i σ =
    boundaryLift i σ hσ ≫ ((relativeSkeleton i).map (homOfLE (Nat.le_succ n))).hom
  exact (boundaryLift_stageInclusion i σ hσ).symm

/-- Each simplex in the unit copy is sent to its prescribed ambient characteristic value. -/
theorem cellMap_unit_app_val {n : ℕ} (σ : Y.toSSet.nonDegenerate n)
    (k : SimplexCategoryᵒᵖ) (a : (Δ[n] : SSet.{u}).obj k) :
    ((cellMap i F adj σ).hom.app k ((adj.unit.app (Δ[n] : SSet.{u})).app k a)).1 =
      Y.toSSet.map a.down.op σ.1 := by
  exact congrArg Subtype.val (congrFun (NatTrans.congr_app (cellMap_unit i F adj σ) k) a)

/-- On the first explicit pushout copy the cell map is exactly the ordinary lift. -/
theorem cellMap_inl {n : ℕ} (σ : Y.toSSet.nonDegenerate n) :
    FreeDaggerPushout.inl (Δ[n] : SSet.{u}) ≫
      (cellMap i FreeDaggerPushout.functor FreeDaggerPushout.adjunction σ).hom =
        cellLift i σ :=
  cellMap_unit i FreeDaggerPushout.functor FreeDaggerPushout.adjunction σ

/-- On the second explicit copy the value is forced by the original restricted dagger. -/
theorem cellMap_inr {n : ℕ} (σ : Y.toSSet.nonDegenerate n) :
    FreeDaggerPushout.inr (Δ[n] : SSet.{u}) ≫
      (cellMap i FreeDaggerPushout.functor FreeDaggerPushout.adjunction σ).hom =
        SSet.opFunctor.map (cellLift i σ) ≫
          ((relativeSkeleton i).obj (n + 1)).daggerIso.inv := by
  rw [FreeDaggerPushout.inr_hom, cellMap_inl]

/-- The explicit adjunction's cell map is its actual pushout descent construction. -/
theorem cellMap_explicit_eq_desc {n : ℕ} (σ : Y.toSSet.nonDegenerate n) :
    cellMap i FreeDaggerPushout.functor FreeDaggerPushout.adjunction σ =
      FreeDaggerPushout.desc (cellLift i σ) := by
  apply (FreeDaggerPushout.homEquiv _ _).injective
  change FreeDaggerPushout.inl (Δ[n] : SSet.{u}) ≫
    (cellMap i FreeDaggerPushout.functor FreeDaggerPushout.adjunction σ).hom =
      FreeDaggerPushout.inl (Δ[n] : SSet.{u}) ≫
        FreeDaggerPushout.descUnderlying (cellLift i σ)
  rw [cellMap_inl, FreeDaggerPushout.inl_descUnderlying]

/-- A simplex in the first copy has the original characteristic value in the ambient target. -/
theorem cellMap_inl_app_val {n k : ℕ} (σ : Y.toSSet.nonDegenerate n)
    (α : ⦋k⦌ ⟶ ⦋n⦌) :
    ((cellMap i FreeDaggerPushout.functor FreeDaggerPushout.adjunction σ).hom.app
      (op ⦋k⦌) ((FreeDaggerPushout.inl (Δ[n] : SSet.{u})).app (op ⦋k⦌)
        (ULift.up α))).1 = Y.toSSet.map α.op σ.1 :=
  cellMap_unit_app_val i FreeDaggerPushout.functor FreeDaggerPushout.adjunction σ
    (op ⦋k⦌) (ULift.up α)

/-- A simplex in the second copy has the reversed pullback of the dagger of the chosen cell. -/
theorem cellMap_inr_app_val {n k : ℕ} (σ : Y.toSSet.nonDegenerate n)
    (α : ⦋k⦌ ⟶ ⦋n⦌) :
    ((cellMap i FreeDaggerPushout.functor FreeDaggerPushout.adjunction σ).hom.app
      (op ⦋k⦌) ((FreeDaggerPushout.inr (Δ[n] : SSet.{u})).app (op ⦋k⦌)
        (SSet.opObjEquiv.symm (ULift.up α)))).1 =
      Y.toSSet.map (SimplexCategory.rev.map α).op (Y.daggerSimplex σ.1) := by
  have h := congrArg Subtype.val (congrFun
    (NatTrans.congr_app (cellMap_inr i σ) (op ⦋k⦌))
      (SSet.opObjEquiv.symm (ULift.up α)))
  change ((cellMap i FreeDaggerPushout.functor FreeDaggerPushout.adjunction σ).hom.app
    (op ⦋k⦌) ((FreeDaggerPushout.inr (Δ[n] : SSet.{u})).app (op ⦋k⦌)
      (SSet.opObjEquiv.symm (ULift.up α)))).1 =
        Y.daggerSimplex (Y.toSSet.map α.op σ.1) at h
  exact h.trans (Y.dagger_map α σ.1)

end DaggerModels.RelativeCellMaps
