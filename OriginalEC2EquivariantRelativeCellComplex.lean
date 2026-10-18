import OriginalEC2EquivariantSkeletalPushout
import TopCatModelCategory.CellComplex
import Mathlib.CategoryTheory.Limits.Lattice

/-!
# An exhaustive relative cell complex for the original simplicial C₂ action

The original skeletal inclusions exhaust the codiscrete nerve. At step n one
regular orbit of n-simplex boundary cells is attached. The entire structure
is then realized by the original realization functor on actions.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction
open DaggerOriginalEC2SkeletonAction DaggerOriginalEC2FreeCellAction
open DaggerOriginalEC2EquivariantAttachingLegs DaggerOriginalEC2EquivariantSkeletalPushout

universe u

namespace DaggerOriginalEC2EquivariantRelativeCellComplex

noncomputable section

private abbrev E : SSet.{u} := simplicialEC2.{u}

/-- The original zero skeleton is initial even as a C₂-action. -/
def skeletalZeroIsInitial : IsInitial (skeletonAction.{u} 0) := by
  let h0 : IsInitial (E.{u}.skeleton 0 : SSet.{u}) :=
    (SSet.Subcomplex.botIsInitial (X := E.{u})).ofIso
      (SSet.Subcomplex.isoOfEq E.{u}.skeleton_zero).symm
  refine IsInitial.ofUniqueHom
    (fun A ↦ { hom := h0.to A.V, comm g := h0.hom_ext _ _ }) ?_
  intro A f
  apply Action.Hom.ext
  exact h0.hom_ext _ _

private def inclusionOfLE {n m : ℕ} (hnm : n ≤ m) :
    skeletonAction.{u} n ⟶ skeletonAction.{u} m where
  hom := SSet.Subcomplex.homOfLE (E.{u}.skeleton.monotone hnm)
  comm g := by
    apply (cancel_mono (E.{u}.skeleton m).ι).1
    change ((skeletonAction.{u} n).ρ g ≫ SSet.Subcomplex.homOfLE _) ≫
        (E.{u}.skeleton m).ι =
      (SSet.Subcomplex.homOfLE _ ≫ (skeletonAction.{u} m).ρ g) ≫
        (E.{u}.skeleton m).ι
    have hn : (skeletonAction.{u} n).ρ g ≫ (E.{u}.skeleton n).ι =
        (E.{u}.skeleton n).ι ≫ (simplicialAction.{u}.ρ g).asHom :=
      (skeletonInclusion.{u} n).comm g
    have hm : (skeletonAction.{u} m).ρ g ≫ (E.{u}.skeleton m).ι =
        (E.{u}.skeleton m).ι ≫ (simplicialAction.{u}.ρ g).asHom :=
      (skeletonInclusion.{u} m).comm g
    rw [Category.assoc, SSet.Subcomplex.homOfLE_ι, Category.assoc, hm]
    rw [← Category.assoc, SSet.Subcomplex.homOfLE_ι]
    exact hn

/-- The literal skeletal filtration in the category of original C₂ actions. -/
def skeletalDiagram : ℕ ⥤ Action SSet.{u} C2.{u} where
  obj n := skeletonAction.{u} n
  map f := inclusionOfLE.{u} (leOfHom f)
  map_id _ := by apply Action.Hom.ext; rfl
  map_comp _ _ := by apply Action.Hom.ext; rfl

/-- All skeletal stages include into the same original simplicial action. -/
def skeletalCocone : Cocone skeletalDiagram.{u} where
  pt := simplicialAction.{u}
  ι :=
    { app n := skeletonInclusion.{u} n
      naturality _ _ _ := by apply Action.Hom.ext; rfl }

/-- The entire original simplicial action is the colimit of its skeleta. -/
def skeletalIsColimit : IsColimit skeletalCocone.{u} := by
  apply isColimitOfReflects (Action.forget SSet.{u} C2.{u})
  exact IsColimit.ofIsoColimit
    (isColimitOfPreserves SSet.Subcomplex.toPresheafFunctor
      ((CompleteLattice.colimitCocone E.{u}.skeleton.monotone.functor).isColimit))
    (Cocones.ext
      (SSet.Subcomplex.isoOfEq E.{u}.iSup_skeleton ≪≫ SSet.Subcomplex.topIso E.{u})
      (fun _ ↦ by rfl))

/-- The exhaustive original action is built by one regular boundary-cell orbit
at each step, with no model-category hypothesis. -/
def equivariantRelativeCellComplex :
    RelativeCellComplex.{0}
      (fun (n : ℕ) (_ : PUnit) ↦ boundaryHom.{u} n) (skeletonInclusion.{u} 0) where
  F := skeletalDiagram.{u}
  isoBot := Iso.refl _
  incl := skeletalCocone.{u}.ι
  isColimit := skeletalIsColimit.{u}
  fac := by
    apply Action.Hom.ext
    exact Category.id_comp (skeletonInclusion.{u} 0).hom
  attachCells n _ :=
    { ι := PUnit
      π _ := ⟨⟩
      cofan₁ := Cofan.mk _ (fun (_ : PUnit) ↦ 𝟙 _)
      cofan₂ := Cofan.mk _ (fun (_ : PUnit) ↦ 𝟙 _)
      isColimit₁ := Cofan.isColimitMkOfUnique (Iso.refl _) PUnit
      isColimit₂ := Cofan.isColimitMkOfUnique (Iso.refl _) PUnit
      m := boundaryHom.{u} n
      hm _ := by simp
      g₁ := attachingHom.{u} n
      g₂ := characteristicHom.{u} n
      isPushout := equivariantSkeletalPushout.{u} n }

/-- Realize the entire exhaustive action cell complex by the original functor. -/
def realizedEquivariantRelativeCellComplex :
    RelativeCellComplex.{0}
      (fun (n : ℕ) (_ : PUnit) ↦
        (SSet.toTop.{u}.mapAction C2.{u}).map (boundaryHom.{u} n))
      ((SSet.toTop.{u}.mapAction C2.{u}).map (skeletonInclusion.{u} 0)) := by
  let : PreservesWellOrderContinuousOfShape ℕ (SSet.toTop.{u}.mapAction C2.{u}) :=
    ⟨fun _ _ ↦ inferInstance⟩
  exact equivariantRelativeCellComplex.{u}.map (SSet.toTop.{u}.mapAction C2.{u})

end

end DaggerOriginalEC2EquivariantRelativeCellComplex
