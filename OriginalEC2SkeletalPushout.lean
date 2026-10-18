import OriginalEC2NondegenerateFreeOrbit
import TopCatModelCategory.SSet.Skeleton

/-!
# The literal skeletal attachment of the codiscrete `EC₂` nerve

The retained relative-cell pushout is reindexed by the actual regular `C₂`
orbit in each dimension.  This is a simplicial-set pushout; its realized
equivariant CW interpretation is a subsequent step.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalEC2SimplicialAction
open DaggerOriginalEC2NondegenerateFreeOrbit

universe u

namespace DaggerOriginalEC2SkeletalPushout

noncomputable section

private abbrev E : SSet.{u} := simplicialEC2.{u}
private abbrev bottomInclusion : ((⊥ : E.{u}.Subcomplex) : SSet.{u}) ⟶ E.{u} :=
  (⊥ : E.{u}.Subcomplex).ι

/-- At the empty subcomplex the retained relative skeleton is the ordinary one. -/
theorem bottomSkeleton (n : ℕ) :
    SSet.skeletonOfMono bottomInclusion.{u} n = E.{u}.skeleton n := by
  simp [SSet.skeletonOfMono, bottomInclusion, Subfunctor.range_ι]

/-- The actual cells attached in degree `n` form the regular `C₂` orbit. -/
def attachingIndexEquiv (n : ℕ) :
    C2.{u} ≃ SSet.relativeCellComplexOfMono.ι bottomInclusion.{u} n where
  toFun g := ⟨orbitMap.{u} n g, by
    simp [bottomInclusion, Subfunctor.range_ι]⟩
  invFun s := (nondegenerateEquiv.{u} n).symm s.1
  left_inv g := (nondegenerateEquiv.{u} n).symm_apply_apply g
  right_inv s := by
    apply Subtype.ext
    exact (nondegenerateEquiv.{u} n).apply_symm_apply s.1

/-- Reindex the retained coproduct of literal simplex boundaries by `C₂`. -/
def boundaryCoproductIso (n : ℕ) :
    (∐ (fun (_ : C2.{u}) ↦ (SSet.boundary n : SSet.{u}))) ≅
      SSet.relativeCellComplexOfMono.A bottomInclusion.{u} n :=
  Limits.Sigma.reindex (attachingIndexEquiv.{u} n)
    (fun _ ↦ (SSet.boundary n : SSet.{u}))

/-- Reindex the retained coproduct of literal standard simplices by `C₂`. -/
def simplexCoproductIso (n : ℕ) :
    (∐ (fun (_ : C2.{u}) ↦ (Δ[n] : SSet.{u}))) ≅
      SSet.relativeCellComplexOfMono.B bottomInclusion.{u} n :=
  Sigma.reindex (attachingIndexEquiv.{u} n) (fun _ ↦ Δ[n])

/-- The reindexed left vertical map remains the coproduct of boundary inclusions. -/
def boundaryMap (n : ℕ) :
    (∐ (fun (_ : C2.{u}) ↦ (SSet.boundary n : SSet.{u}))) ⟶
      (∐ (fun (_ : C2.{u}) ↦ (Δ[n] : SSet.{u}))) :=
  Limits.Sigma.map (fun _ ↦ (SSet.boundary n).ι)

/-- The actual codiscrete-nerve skeletal attachment is a pushout with one
free `C₂` orbit of `n`-cells. The other legs are the retained `t`, `r`, `b`
maps, transported by the indicated index and subcomplex isomorphisms. -/
theorem skeletalPushout (n : ℕ) :
    IsPushout
      ((boundaryCoproductIso.{u} n).hom ≫
        SSet.relativeCellComplexOfMono.t bottomInclusion.{u} n)
      (boundaryMap.{u} n)
      (SSet.relativeCellComplexOfMono.r bottomInclusion.{u} n)
      ((simplexCoproductIso.{u} n).hom ≫
        SSet.relativeCellComplexOfMono.b bottomInclusion.{u} n) := by
  apply (SSet.relativeCellComplexOfMono.isPushout bottomInclusion.{u} n).of_iso'
    (boundaryCoproductIso.{u} n) (Iso.refl _)
    (simplexCoproductIso.{u} n) (Iso.refl _)
  · simp
  · apply Sigma.hom_ext
    intro g
    simp [boundaryCoproductIso, simplexCoproductIso, boundaryMap,
      SSet.relativeCellComplexOfMono.m]
    rw [← Category.assoc]
    erw [
      Limits.Sigma.ι_reindex_hom (attachingIndexEquiv.{u} n)
        (fun _ ↦ (SSet.boundary n : SSet.{u})) g]
    erw [
      Limits.Sigma.ι_reindex_hom (attachingIndexEquiv.{u} n)
        (fun _ ↦ (Δ[n] : SSet.{u})) g]
    exact Limits.Sigma.ι_map (fun _ ↦ (SSet.boundary n).ι)
      ((attachingIndexEquiv.{u} n) g)
  · simp
  · simp

end

end DaggerOriginalEC2SkeletalPushout
