import OriginalAntiInvolutiveRelativeSkeleton
import OriginalAntiInvolutiveNormalGenerators
import DaggerModels.SSetBoundaryCellsAttachment

/-!
# Actual anti-involutive relative boundary attachments

For a normal monomorphism, each orbit of new nondegenerate simplices has a
chosen representative. The maps below attach the original free anti-involutive
boundary generator for each orbit to the actual relative skeletal stage.
The ordinary characteristic maps need not be monomorphisms.
-/

set_option autoImplicit false

open CategoryTheory Limits Simplicial Opposite

universe u

namespace DaggerModels.OriginalAntiInvolutiveRelativeCellAttachment

open DaggerModels.AntiInvolutiveSSet
open DaggerModels.OriginalAntiInvolutiveNormalGenerators
open DaggerModels.OriginalAntiInvolutiveFreePair
open DaggerModels.OriginalAntiInvolutiveRelativeSkeleton
open DaggerModels.SSetBoundaryCells

noncomputable section

variable {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y) [Mono f]

local instance : Mono f.hom :=
  (OriginalAntiInvolutiveNormalMonoClosure.mono_iff_mono_hom f).1 inferInstance

/-- The selected first-tag simplex in each actual reversal orbit. -/
def representative (hf : NormalMono f) (n : ℕ) (r : NewCellOrbit f n) :
    NewNonDegenerate f n := (newCellSplit hf n).symm (r, false)

/-- The actual coproduct of free boundary sources, represented by the concrete
left adjoint pair. The representative index is an orbit, including degree zero. -/
def boundarySource (n : ℕ) : AntiInvolutiveSSet.{u} :=
  pairObj (copies (NewCellOrbit f n) (SSet.boundary.{u} n).toSSet)

/-- The corresponding coproduct of full free cells. -/
def cellSource (n : ℕ) : AntiInvolutiveSSet.{u} :=
  pairObj (copies (NewCellOrbit f n) (Δ[n] : SSet.{u}))

/-- The coproduct map is the concrete presentation of the literal free-boundary
maps `freeAnti.map (SSet.boundary n).ι`. -/
def boundarySumMap (n : ℕ) : boundarySource f n ⟶ cellSource f n :=
  pairMap (copiesMap (NewCellOrbit f n) (SSet.boundary.{u} n).ι)

/-- Ordinary base attaching maps, one per chosen orbit representative. -/
def attachingBase (hf : NormalMono f) (n : ℕ) :
    copies (NewCellOrbit f n) (SSet.boundary.{u} n).toSSet ⟶
      (SSet.skeletonOfMono f.hom n).toSSet :=
  copiesDesc (fun r ↦ boundaryLift f.hom (representative f hf n r))

/-- Ordinary base characteristic maps, one per chosen orbit representative. -/
def characteristicBase (hf : NormalMono f) (n : ℕ) :
    copies (NewCellOrbit f n) (Δ[n] : SSet.{u}) ⟶
      (SSet.skeletonOfMono f.hom (n + 1)).toSSet :=
  copiesDesc (fun r ↦ cellLift f.hom (representative f hf n r).1)

/-- Anti-involutive attaching map from the free orbit-indexed boundary sources. -/
def attachingMap (hf : NormalMono f) (n : ℕ) :
    boundarySource f n ⟶ (relativeSkeleton f).obj n :=
  extend (attachingBase f hf n)

/-- Anti-involutive characteristic map from the free orbit-indexed cells. -/
def characteristicSum (hf : NormalMono f) (n : ℕ) :
    cellSource f n ⟶ (relativeSkeleton f).obj (n + 1) :=
  extend (characteristicBase f hf n)

/-- The specified anti-involutive square commutes on both tagged copies. -/
theorem attachment_commutes (hf : NormalMono f) (n : ℕ) :
    attachingMap f hf n ≫ (relativeSkeleton f).map (homOfLE (Nat.le_succ n)) =
      boundarySumMap f n ≫ characteristicSum f hf n := by
  apply (homEquiv
    (copies (NewCellOrbit f n) (SSet.boundary.{u} n).toSSet)
    ((relativeSkeleton f).obj (n + 1))).injective
  ext k a
  exact congrFun (NatTrans.congr_app
    (SSetBoundaryCells.boundaryLift_step f.hom (representative f hf n a.1)) k) a.2

end

end DaggerModels.OriginalAntiInvolutiveRelativeCellAttachment
