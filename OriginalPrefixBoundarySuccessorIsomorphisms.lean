import OriginalPrefixBoundarySuccessorOverlap

/-!
# Exact smaller-simplex and smaller-boundary identifications in the successor pushout

The original coface is monic. Native range and image factorizations identify
the actual first face with the original smaller simplex, and the entire
actual overlap with the original smaller prefix boundary. All identification
maps retain their exact original ambient-inclusion equations.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalPrefixBoundarySuccessorShapes
open DaggerOriginalPrefixDeleteFirstCoface
open DaggerOriginalPrefixBoundarySuccessorOverlap

universe u

namespace DaggerOriginalPrefixBoundarySuccessorIsomorphisms

noncomputable section

/-- The actual first-prefix ordinal coface is monic. -/
theorem prefixDeleteFirstOperator_mono (k n : ℕ) : Mono (prefixDeleteFirstOperator k n) := by
  apply SimplexCategory.mono_iff_injective.mpr
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  rw [prefixDeleteFirstOperator_eval, prefixDeleteFirstOperator_eval] at hv
  omega

/-- Its actual standard-simplex map is monic in every degree. -/
theorem prefixDeleteFirstMap_mono (k n : ℕ) : Mono (prefixDeleteFirstMap.{u} k n) := by
  haveI := prefixDeleteFirstOperator_mono k n
  apply (NatTrans.mono_iff_mono_app _).2
  intro q
  apply (CategoryTheory.mono_iff_injective _).2
  intro a b h
  apply SSet.stdSimplex.objEquiv.injective
  apply (cancel_mono (prefixDeleteFirstOperator k n)).mp
  exact congrArg SSet.stdSimplex.objEquiv h

/-- The exact original smaller simplex identifies with the actual first omitted-prefix face. -/
def firstPrefixFaceIso (k n : ℕ) : (Δ[k + n + 1] : SSet.{u}) ≅ firstPrefixFace k n := by
  haveI := prefixDeleteFirstMap_mono.{u} k n
  exact asIso (SSet.Subcomplex.toRange (prefixDeleteFirstMap k n)) ≪≫
    SSet.Subcomplex.eqToIso (prefixDeleteFirstMap_range k n)

/-- The first-face identification has precisely the original coface as its ambient map. -/
theorem firstPrefixFaceIso_hom_comp (k n : ℕ) :
    (firstPrefixFaceIso.{u} k n).hom ≫ (firstPrefixFace k n).ι =
      prefixDeleteFirstMap k n := by
  change SSet.Subcomplex.toRange (prefixDeleteFirstMap k n) ≫
    SSet.Subcomplex.homOfLE (prefixDeleteFirstMap_range k n).le ≫
      (firstPrefixFace k n).ι = prefixDeleteFirstMap k n
  rw [SSet.Subcomplex.homOfLE_ι]
  rfl

/-- The actual restricted coface is monic on the entire original smaller boundary. -/
theorem prefixBoundary_toImage_mono (k n : ℕ) :
    Mono ((prefixBoundary.{u} k n).toImage (prefixDeleteFirstMap k n)) := by
  haveI := prefixDeleteFirstMap_mono.{u} k n
  haveI : Mono ((prefixBoundary.{u} k n).ι ≫ prefixDeleteFirstMap k n) := by infer_instance
  exact mono_of_mono_fac (SSet.Subcomplex.toImage_ι _ _)

/-- The original smaller boundary identifies with the entire actual first-face overlap. -/
def successorOverlapIso (k n : ℕ) : (prefixBoundary k n : SSet.{u}) ≅
    ((firstPrefixFace k n ⊓ restPrefixBoundary k n :
      (Δ[k + 1 + n + 1] : SSet.{u}).Subcomplex) : SSet.{u}) := by
  haveI := prefixBoundary_toImage_mono.{u} k n
  haveI : IsIso ((prefixBoundary.{u} k n).toImage (prefixDeleteFirstMap k n)) :=
    isIso_of_mono_of_epi _
  exact asIso ((prefixBoundary k n).toImage (prefixDeleteFirstMap k n)) ≪≫
    SSet.Subcomplex.eqToIso ((prefixDeleteFirst_boundary_image k n).trans (inf_comm _ _))

/-- The overlap identification has exactly the original restricted-coface ambient map. -/
theorem successorOverlapIso_hom_comp_inclusion (k n : ℕ) :
    (successorOverlapIso.{u} k n).hom ≫ (firstPrefixFace k n ⊓ restPrefixBoundary k n).ι =
      (prefixBoundary k n).ι ≫ prefixDeleteFirstMap k n := by
  change (prefixBoundary k n).toImage (prefixDeleteFirstMap k n) ≫
    SSet.Subcomplex.homOfLE ((prefixDeleteFirst_boundary_image k n).trans (inf_comm _ _)).le ≫
      (firstPrefixFace k n ⊓ restPrefixBoundary k n).ι =
    (prefixBoundary k n).ι ≫ prefixDeleteFirstMap k n
  rw [SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toImage_ι]

/-- Its first-face component is the original smaller boundary inclusion and first-face map. -/
theorem successorOverlapIso_hom_comp_first (k n : ℕ) :
    (successorOverlapIso.{u} k n).hom ≫ SSet.Subcomplex.homOfLE inf_le_left =
      (prefixBoundary k n).ι ≫ (firstPrefixFaceIso k n).hom := by
  apply (cancel_mono (firstPrefixFace k n).ι).mp
  rw [Category.assoc, SSet.Subcomplex.homOfLE_ι, successorOverlapIso_hom_comp_inclusion,
    Category.assoc, firstPrefixFaceIso_hom_comp]

/-- The exact original smaller boundary embedded into the remaining successor prefix faces. -/
def boundaryToRest (k n : ℕ) : (prefixBoundary k n : SSet.{u}) ⟶ restPrefixBoundary k n :=
  (successorOverlapIso k n).hom ≫ SSet.Subcomplex.homOfLE inf_le_right

/-- This embedding also has exactly the original restricted-coface ambient map. -/
theorem boundaryToRest_comp_inclusion (k n : ℕ) :
    boundaryToRest.{u} k n ≫ (restPrefixBoundary k n).ι =
      (prefixBoundary k n).ι ≫ prefixDeleteFirstMap k n := by
  dsimp only [boundaryToRest]
  rw [Category.assoc, SSet.Subcomplex.homOfLE_ι, successorOverlapIso_hom_comp_inclusion]

end

end DaggerOriginalPrefixBoundarySuccessorIsomorphisms
