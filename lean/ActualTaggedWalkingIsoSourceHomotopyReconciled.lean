import OriginalFreeAntiSimplicialHomotopyEquivalence
import ActualTaggedWalkingIsoImageDKObstructionReconciled

/-!
# The literal tagged walking generator is normal with a raw underlying equivalence

The ordinary walking-isomorphism nerve has an explicit contraction in both
directions, coming from the two inverse natural transformations. The existing
actual free anti construction retains these contractions on its whole underlying
simplicial set. Native Kan--Quillen weakness is distinguished from DCH/Joyal
weakness; no DCH model construction or identification is supplied here.
-/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite DaggerModels HomotopicalAlgebra
open DaggerModels.OriginalWalkingIsoIntegerObstruction
open DaggerModels.OriginalAntiInvolutiveFreePairMono
open DaggerOriginalFreeAntiSimplicialHomotopyEquivalence
open DaggerActualFreeWalkingIsoIntegerObstruction
open DaggerActualTaggedWalkingIsoImageDKObstruction
universe u
namespace DaggerActualTaggedWalkingIsoSourceHomotopy
noncomputable section

private def homotopyOfEq {X Y : SSet.{u}} {f g : X ⟶ Y} (hfg : f = g) :
    SSet.Homotopy f g := by
  subst g
  exact SSet.Homotopy.mk (CartesianMonoidalCategory.fst X Δ[1] ≫ f) (by simp) (by simp)

/-- Retraction of the original walking nerve to the actual standard zero-simplex. -/
def collapse : J.{u} ⟶ (Δ[0] : SSet.{u}) := SSet.stdSimplex.isTerminalObj₀.from _

/-- The selected walking zero object as a constant ordinary functor. -/
def constantWalking : walkingIso.{u} ⥤ walkingIso.{u} :=
  (Functor.const walkingIso.{u}).obj walkingZero

/-- The actual unique ordinary isomorphisms give the forward natural transformation. -/
def constantToIdentity : constantWalking.{u} ⟶ 𝟭 walkingIso.{u} where
  app _ := ⟨⟨⟩⟩
  naturality _ _ _ := rfl

/-- Their actual inverses give the opposite natural transformation. -/
def identityToConstant : 𝟭 walkingIso.{u} ⟶ constantWalking.{u} where
  app _ := ⟨⟨⟩⟩
  naturality _ _ _ := rfl

/-- The selected vertex and terminal retraction form an exact retraction. -/
theorem zeroInclusion_collapse : zeroInclusion.{u} ≫ collapse.{u} = 𝟙 _ :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The opposite composite is precisely the nerve of the selected constant functor. -/
theorem nerve_constantWalking :
    nerveMap constantWalking.{u} = collapse.{u} ≫ zeroInclusion.{u} := by
  rw [zeroInclusion, SSet.comp_const]
  apply NatTrans.ext
  funext n s
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The ordinary identity nerve map is the literal simplicial identity. -/
theorem nerve_identityWalking : nerveMap (𝟭 walkingIso.{u}) = 𝟙 J.{u} := by
  apply NatTrans.ext
  funext n s
  exact Functor.comp_id s

/-- The contraction in the first direction retains the entire original nerve. -/
def contraction : SSet.Homotopy (collapse.{u} ≫ zeroInclusion.{u}) (𝟙 J.{u}) :=
  (DaggerNerveHomotopy.natTransHomotopy constantToIdentity.{u}).congr
    nerve_constantWalking nerve_identityWalking

/-- The inverse natural transformation gives a raw contraction in the other direction. -/
def reverseContraction : SSet.Homotopy (𝟙 J.{u}) (collapse.{u} ≫ zeroInclusion.{u}) :=
  (DaggerNerveHomotopy.natTransHomotopy identityToConstant.{u}).congr
    nerve_identityWalking nerve_constantWalking

/-- The forward map is literally the original zero-vertex inclusion. -/
def zeroInclusionHomotopyEquiv : SSet.HomotopyEquiv (Δ[0] : SSet.{u}) J.{u} where
  hom := zeroInclusion
  inv := collapse
  homInvId := homotopyOfEq zeroInclusion_collapse
  invHomId := contraction

/-- The actual free anti map has a raw homotopy inverse on its whole underlying SSet. -/
def taggedGeneratorHomotopyEquiv :
    SSet.HomotopyEquiv
      (OriginalTaggedReverseFreeCompletion.freeAnti.obj (Δ[0] : SSet.{u})).toSSet
      (OriginalTaggedReverseFreeCompletion.freeAnti.obj J.{u}).toSSet :=
  freeAntiHomotopyEquiv zeroInclusionHomotopyEquiv
    (homotopyOfEq zeroInclusion_collapse.symm) reverseContraction

/-- The entire forward map, rather than a point or one selected summand, is the generator. -/
theorem taggedGeneratorHomotopyEquiv_hom :
    taggedGeneratorHomotopyEquiv.{u}.hom = taggedGenerator.{u}.hom :=
  freeAntiHomotopyEquiv_hom _ _ _

/-- The original tagged walking generator is normal, including all new vertices. -/
theorem taggedGenerator_normal : AntiInvolutiveSSet.NormalMono taggedGenerator.{u} :=
  freeAnti_map_normal zeroInclusion.{u}

/-- The literal whole underlying arrow is weak in the native Kan--Quillen structure. -/
theorem taggedGenerator_underlying_kanWeak : WeakEquivalence taggedGenerator.{u}.hom := by
  rw [← taggedGeneratorHomotopyEquiv_hom]
  exact DaggerNativeSSetRawHomotopyEquivalenceWeak.rawHomotopyEquiv_weakEquivalence _

end
end DaggerActualTaggedWalkingIsoSourceHomotopy
