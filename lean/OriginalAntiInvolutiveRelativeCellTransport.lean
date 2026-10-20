import OriginalAntiInvolutiveRelativeCellReindex

/-!
# Transport of characteristic and boundary maps across reversal reindexing

These equalities compare the actual anti-involutive orbit-indexed attaching
square, after forgetting, with the checked all-cell ordinary attaching square.
The true tag uses reversal on both the relative cell and its simplex parameter.
-/

set_option autoImplicit false

open CategoryTheory Simplicial Opposite

universe u

namespace DaggerModels.OriginalAntiInvolutiveRelativeCellTransport

open DaggerModels.AntiInvolutiveSSet
open DaggerModels.OriginalAntiInvolutiveNormalGenerators
open DaggerModels.OriginalAntiInvolutiveRelativeSkeleton
open DaggerModels.OriginalAntiInvolutiveRelativeCellAttachment
open DaggerModels.OriginalAntiInvolutiveRelativeCellReindex
open DaggerModels.OriginalAntiInvolutiveSimplexReversal

noncomputable section

variable {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y) (hf : NormalMono f)

local instance : Mono f :=
  (OriginalAntiInvolutiveNormalMonoClosure.mono_iff_mono_hom f).2 hf.1
local instance : Mono f.hom := hf.1

/-- The first tag is the chosen representative. -/
theorem orbitTagCell_false (n : ℕ) (r : NewCellOrbit f n) :
    orbitTagCellEquiv f hf n (r, false) = representative f hf n r := rfl

/-- The second tag is its actual reverse. -/
theorem orbitTagCell_true (n : ℕ) (r : NewCellOrbit f n) :
    orbitTagCellEquiv f hf n (r, true) =
      newDagger f n (representative f hf n r) := by
  apply (newCellSplit hf n).injective
  change (newCellSplit hf n) ((newCellSplit hf n).symm (r, true)) =
    (newCellSplit hf n) (newDagger f n (representative f hf n r))
  rw [Equiv.apply_symm_apply, newCellSplit_dagger]
  simp [representative]

/-- The orbit-indexed characteristic map becomes the ordinary all-cell
characteristic map after the necessary true-tag parameter reversal. -/
theorem characteristic_transport (n : ℕ) (k : SimplexCategoryᵒᵖ)
    (p : (cellSource f n).toSSet.obj k) :
    letI : Mono f :=
      (OriginalAntiInvolutiveNormalMonoClosure.mono_iff_mono_hom f).2 hf.1
    letI : Mono f.hom := hf.1
    (characteristicSum f hf n).hom.app k p =
      (SSetBoundaryCells.characteristicSum f.hom n).app k
        (fullCellEquiv f hf n k p) := by
  letI : Mono f :=
    (OriginalAntiInvolutiveNormalMonoClosure.mono_iff_mono_hom f).2 hf.1
  letI : Mono f.hom := hf.1
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = op ⦋m⦌ := ⟨k.unop.len, by simp⟩
  rcases p with ⟨⟨r, a⟩, b⟩
  cases b
  · rfl
  · apply Subtype.ext
    change Y.daggerSimplex
        (Y.toSSet.map (SSet.stdSimplex.objEquiv a).op
          (representative f hf n r).1.1) =
        Y.toSSet.map (SimplexCategory.rev.map
          (SSet.stdSimplex.objEquiv a)).op
          (orbitTagCellEquiv f hf n (r, true)).1.1
    rw [orbitTagCell_true]
    exact Y.dagger_map (SSet.stdSimplex.objEquiv a)
      (representative f hf n r).1.1

/-- Boundary attaching maps have the same pointwise comparison, including
true-tag reversal. -/
theorem attaching_transport (n : ℕ) (k : SimplexCategoryᵒᵖ)
    (p : (boundarySource f n).toSSet.obj k) :
    letI : Mono f :=
      (OriginalAntiInvolutiveNormalMonoClosure.mono_iff_mono_hom f).2 hf.1
    letI : Mono f.hom := hf.1
    (attachingMap f hf n).hom.app k p =
      (SSetBoundaryCells.attachingMap f.hom n).app k
        (boundaryCellEquiv f hf n k p) := by
  letI : Mono f :=
    (OriginalAntiInvolutiveNormalMonoClosure.mono_iff_mono_hom f).2 hf.1
  letI : Mono f.hom := hf.1
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = op ⦋m⦌ := ⟨k.unop.len, by simp⟩
  rcases p with ⟨⟨r, ⟨a, ha⟩⟩, b⟩
  cases b
  · rfl
  · apply Subtype.ext
    change Y.daggerSimplex
        (Y.toSSet.map (SSet.stdSimplex.objEquiv a).op
          (representative f hf n r).1.1) =
        Y.toSSet.map (SimplexCategory.rev.map
          (SSet.stdSimplex.objEquiv a)).op
          (orbitTagCellEquiv f hf n (r, true)).1.1
    rw [orbitTagCell_true]
    exact Y.dagger_map (SSet.stdSimplex.objEquiv a)
      (representative f hf n r).1.1

/-- The concrete free-boundary map corresponds to the ordinary coproduct of
literal boundary inclusions under the two pointwise bijections. -/
theorem boundary_transport (n : ℕ) (k : SimplexCategoryᵒᵖ)
    (p : (boundarySource f n).toSSet.obj k) :
    letI : Mono f :=
      (OriginalAntiInvolutiveNormalMonoClosure.mono_iff_mono_hom f).2 hf.1
    letI : Mono f.hom := hf.1
    fullCellEquiv f hf n k ((boundarySumMap f n).hom.app k p) =
      (SSetBoundaryCells.boundarySumMap f.hom n).app k
        (boundaryCellEquiv f hf n k p) := by
  letI : Mono f :=
    (OriginalAntiInvolutiveNormalMonoClosure.mono_iff_mono_hom f).2 hf.1
  letI : Mono f.hom := hf.1
  rcases p with ⟨⟨r, ⟨a, ha⟩⟩, b⟩
  cases b <;> rfl

end

end DaggerModels.OriginalAntiInvolutiveRelativeCellTransport
