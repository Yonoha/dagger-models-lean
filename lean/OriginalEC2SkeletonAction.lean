import OriginalEC2SimplicialAction
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-!
# The actual action on the codiscrete-nerve skeletal filtration

Restriction uses the original simplicial action. The skeletal inclusions and
successive-stage maps are morphisms of actions, with their literal underlying
subcomplex inclusions. This module does not assert an equivariant CW pushout.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction

universe u

namespace DaggerOriginalEC2SkeletonAction

noncomputable section

/-- Every simplicial map preserves the filtration generated in degrees `< n`. -/
theorem skeleton_image_le {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    (X.skeleton n).image f ≤ Y.skeleton n := by
  dsimp only [SSet.skeleton, OrderHom.coe_mk]
  rw [SSet.Subcomplex.image_iSup]
  refine iSup_le fun i ↦ ?_
  rw [SSet.Subcomplex.image_iSup]
  refine iSup_le fun x ↦ ?_
  rw [SSet.Subcomplex.image_ofSimplex]
  exact Y.ofSimplex_le_skeleton (f.app _ x.val) i.isLt

/-- The restriction of an actual simplicial map to the two actual skeleta. -/
def skeletonMap {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    (X.skeleton n : SSet.{u}) ⟶ (Y.skeleton n : SSet.{u}) :=
  (Y.skeleton n).lift ((X.skeleton n).ι ≫ f)
    (by rw [← SSet.Subcomplex.image_eq_range]; exact skeleton_image_le f n)

/-- Restriction followed by inclusion is the original map after inclusion. -/
theorem skeletonMap_ι {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    skeletonMap f n ≫ (Y.skeleton n).ι = (X.skeleton n).ι ≫ f := rfl

private theorem skeletonMap_id (X : SSet.{u}) (n : ℕ) :
    skeletonMap (𝟙 X) n = 𝟙 (X.skeleton n : SSet.{u}) := by
  apply (cancel_mono (X.skeleton n).ι).1
  simp only [skeletonMap_ι, Category.comp_id, Category.id_comp]

private theorem skeletonMap_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) : skeletonMap (f ≫ g) n = skeletonMap f n ≫ skeletonMap g n := by
  apply (cancel_mono (Z.skeleton n).ι).1
  simp only [skeletonMap_ι, Category.assoc]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ g) (skeletonMap_ι f n).symm

/-- The original `C₂` action restricted to the literal `n`th skeletal subcomplex. -/
def skeletonAction (n : ℕ) : Action SSet.{u} C2.{u} where
  V := (simplicialEC2.{u}).skeleton n
  ρ :=
    { toFun := fun g ↦ End.of (skeletonMap (simplicialAction.{u}.ρ g).asHom n)
      map_one' := by
        change skeletonMap (simplicialAction.{u}.ρ 1).asHom n = 𝟙 _
        rw [Action.ρ_one]
        exact skeletonMap_id _ n
      map_mul' := by
        intro g h
        change skeletonMap (simplicialAction.{u}.ρ (g * h)).asHom n =
          skeletonMap (simplicialAction.{u}.ρ h).asHom n ≫
            skeletonMap (simplicialAction.{u}.ρ g).asHom n
        rw [map_mul, End.mul_def]
        exact skeletonMap_comp _ _ n }

/-- Each skeletal inclusion is equivariant for the actual original action. -/
def skeletonInclusion (n : ℕ) : skeletonAction.{u} n ⟶ simplicialAction.{u} where
  hom := (simplicialEC2.{u}.skeleton n).ι
  comm g := skeletonMap_ι (simplicialAction.{u}.ρ g).asHom n

/-- The equivariant inclusion has exactly the original subcomplex inclusion. -/
theorem skeletonInclusion_hom (n : ℕ) :
    (skeletonInclusion.{u} n).hom = (simplicialEC2.{u}.skeleton n).ι := rfl

/-- The successive skeletal inclusion, as a morphism of the restricted actions. -/
def skeletonTransition (n : ℕ) : skeletonAction.{u} n ⟶ skeletonAction.{u} (n + 1) where
  hom := SSet.Subcomplex.homOfLE (simplicialEC2.{u}.skeleton.monotone (by omega))
  comm g := by
    apply (cancel_mono (simplicialEC2.{u}.skeleton (n + 1)).ι).1
    change (skeletonMap (simplicialAction.{u}.ρ g).asHom n ≫
        SSet.Subcomplex.homOfLE _) ≫ (simplicialEC2.{u}.skeleton (n + 1)).ι =
      (SSet.Subcomplex.homOfLE _ ≫
        skeletonMap (simplicialAction.{u}.ρ g).asHom (n + 1)) ≫
          (simplicialEC2.{u}.skeleton (n + 1)).ι
    simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι, skeletonMap_ι]
    simp only [← Category.assoc, SSet.Subcomplex.homOfLE_ι]
    exact skeletonMap_ι _ n

/-- Successive inclusion into the full action is the previous inclusion. -/
theorem skeletonTransition_inclusion (n : ℕ) :
    skeletonTransition.{u} n ≫ skeletonInclusion.{u} (n + 1) =
      skeletonInclusion.{u} n := by
  apply Action.Hom.ext
  rfl

end

end DaggerOriginalEC2SkeletonAction
