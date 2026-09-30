import DaggerModels.BoundaryCellTransport
import DaggerModels.CoproductAttachment
import DaggerModels.RelativeCellCoverage
import DaggerModels.RelativeCellIntersection
import DaggerModels.RelativeCellSeparation

/-!
# The relative free-boundary-cell presentation

This proves the cellular characterization in Part I, `dj.lem.free-cof`.
The genuine relative skeleton attaches one zero-cell per new vertex and
one free positive cell per new dagger orbit. The actual attachment squares,
source identification, and target colimit form a `RelativeCellComplex`.
The construction transports to any left adjoint of the original forgetful
functor, including the previously constructed canonical free functor.
-/

open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra

universe u

namespace DaggerModels

open DaggerSSet RelativeCellMaps

local instance : HasColimits DaggerSSet.{u} := daggerSSetHasColimits

/-- Every successor inclusion of the actual relative skeleton is monic. -/
theorem relativeSkeleton_step_mono {X Y : DaggerSSet.{u}} (i : X ⟶ Y) [Mono i] (n : ℕ) :
    Mono ((relativeSkeleton i).map (homOfLE (Nat.le_succ n))) := by
  let : Mono i.hom := (mono_iff_mono_hom i).1 inferInstance
  apply (mono_iff_mono_hom _).2
  change Mono (SSet.Subcomplex.homOfLE
    ((SSet.skeletonOfMono i.hom).monotone (Nat.le_succ n)))
  infer_instance

/-- Each actual relative skeletal step attaches precisely the chosen free boundary cells. -/
noncomputable def explicitRelativeSkeletonAttachCells {X Y : DaggerSSet.{u}}
    (i : X ⟶ Y) [Mono i] (n : ℕ) (c : CellReps i n) :
    AttachCells.{u}
      (fun m : ℕ ↦ FreeDaggerPushout.functor.map (SSet.boundary.{u} m).ι)
      ((relativeSkeleton i).map (homOfLE (Nat.le_succ n))) := by
  let : Mono ((relativeSkeleton i).map (homOfLE (Nat.le_succ n))) :=
    relativeSkeleton_step_mono i n
  let a := fun r : c.R ↦ boundaryMap i FreeDaggerPushout.functor
    FreeDaggerPushout.adjunction (c.rep r).1 (c.rep r).2
  let b := fun r : c.R ↦ cellMap i FreeDaggerPushout.functor
    FreeDaggerPushout.adjunction (c.rep r).1
  let g := FreeDaggerPushout.functor.map (SSet.boundary.{u} n).ι
  refine
    { ι := c.R
      π := fun _ ↦ n
      cofan₁ := Cofan.mk (∐ (fun _ : c.R ↦ FreeDaggerPushout.functor.obj
        (SSet.boundary.{u} n).toSSet)) (Sigma.ι _)
      cofan₂ := Cofan.mk (∐ (fun _ : c.R ↦ FreeDaggerPushout.functor.obj
        (Δ[n] : SSet.{u}))) (Sigma.ι _)
      isColimit₁ := coproductIsCoproduct _
      isColimit₂ := coproductIsCoproduct _
      m := Limits.Sigma.map (fun _ : c.R ↦ g)
      hm := Sigma.ι_map (fun _ : c.R ↦ g)
      g₁ := Sigma.desc a
      g₂ := Sigma.desc b
      isPushout := ?_ }
  apply isPushout_coproduct_of_complement g
    (freeDagger_map_freeCofibration FreeDaggerPushout.functor FreeDaggerPushout.adjunction _)
  · intro r
    exact (cellMap_boundary i FreeDaggerPushout.functor
      FreeDaggerPushout.adjunction (c.rep r).1 (c.rep r).2).symm
  · intro r k x hx
    exact (RelativeCellIntersection.cellMap_mem_stageInclusion_range_iff
      i (c.rep r).1 (c.rep r).2 (k := k.unop.len) x).1 hx
  · intro k x
    exact RelativeCellCoverage.stage_covered_by_cells i (k := k.unop.len) c x
  · intro r s k x y hx hy he
    exact RelativeCellSeparation.cellMap_separates c r s (k := k.unop.len) x y hx hy he

/-- Every free cofibration has an actual countable relative presentation by free boundaries. -/
noncomputable def relativeFreeBoundaryCellComplex
    (F : SSet.{u} ⥤ DaggerSSet.{u}) (adj : F ⊣ DaggerSSet.forget)
    {X Y : DaggerSSet.{u}} (i : X ⟶ Y) (hi : FreeCofibration i) :
    RelativeCellComplex.{u}
      (fun (_ : ℕ) ↦ fun n : ℕ ↦ F.map (SSet.boundary.{u} n).ι) i := by
  let : Mono i := hi.1
  exact
    { toTransfiniteCompositionOfShape := relativeSkeletonTransfiniteComposition i
      attachCells := fun n _ ↦ boundaryAttachmentOfAdjunction
        FreeDaggerPushout.functor F FreeDaggerPushout.adjunction adj
        (explicitRelativeSkeletonAttachCells i n (cellReps hi n)) }

/-- The relative-cell conclusion of Part I `dj.lem.free-cof`, with no cellularity premise. -/
theorem exists_relativeFreeBoundaryCellComplex
    (F : SSet.{u} ⥤ DaggerSSet.{u}) (adj : F ⊣ DaggerSSet.forget)
    {X Y : DaggerSSet.{u}} (i : X ⟶ Y) (hi : FreeCofibration i) :
    Nonempty (RelativeCellComplex.{u}
      (fun (_ : ℕ) ↦ fun n : ℕ ↦ F.map (SSet.boundary.{u} n).ι) i) :=
  ⟨relativeFreeBoundaryCellComplex F adj i hi⟩

/-- Free cofibrations are exactly the stated saturation of the actual free boundary inclusions. -/
theorem freeBoundarySaturation_eq
    (F : SSet.{u} ⥤ DaggerSSet.{u}) (adj : F ⊣ DaggerSSet.forget) :
    (MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u} (freeBoundaryGenerators F)).pushouts).retracts =
        DaggerSSet.freeCofibrations := by
  apply le_antisymm (freeBoundarySaturation_le F adj)
  intro X Y i hi
  exact freeBoundarySaturation_of_relativeCellComplexNat F
    (relativeFreeBoundaryCellComplex F adj i hi)

/-- The cellular characterization applies to the original canonical free dagger functor. -/
theorem canonical_freeBoundarySaturation_eq :
    (MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u} (freeBoundaryGenerators freeDagger.{u})).pushouts).retracts =
        DaggerSSet.freeCofibrations :=
  freeBoundarySaturation_eq freeDagger freeDaggerAdjunction

end DaggerModels
