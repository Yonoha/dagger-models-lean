import TopCatModelCategory.SSet.Skeleton

/-! Use the existing TopCatModelCategory relative cell complex as the full natural-number skeleton diagram. -/
set_option autoImplicit false
open CategoryTheory Limits
universe u
namespace DaggerNativeSimplicialSkeletonStages
noncomputable section

/-- The native relative cell complex of the empty subcomplex gives all skeleton stages. -/
abbrev stages (X : SSet.{u}) : ℕ ⥤ SSet.{u} :=
  (SSet.relativeCellComplex X).toTransfiniteCompositionOfShape.F

/-- The native stage retains precisely the original skeleton, without new cell data. -/
theorem stage_eq_skeleton (X : SSet.{u}) (n : ℕ) :
    (stages X).obj n = (X.skeleton n).toSSet := by
  change (SSet.skeletonOfMono (⊥ : X.Subcomplex).ι n).toSSet = _
  simp [SSet.skeletonOfMono]

/-- A native skeleton reaches the entire simplicial set at its dimension bound. -/
theorem skeleton_eq_top (X : SSet.{u}) (n : ℕ) [X.HasDimensionLT n] :
    X.skeleton n = ⊤ := by
  apply (SSet.Subcomplex.eq_top_iff_of_hasDimensionLT _ n).2
  intro d hd
  rw [SSet.skeleton_obj_eq_top X hd]
  exact Set.subset_univ _

/-- The actual stage is isomorphic to the original object at its dimension bound. -/
def stageIso (X : SSet.{u}) (n : ℕ) [X.HasDimensionLT n] :
    (stages X).obj n ≅ X :=
  eqToIso (stage_eq_skeleton X n) ≪≫
    SSet.Subcomplex.isoOfEq (skeleton_eq_top X n) ≪≫ SSet.Subcomplex.topIso X

/-- The full native skeleton cocone has the original object as its apex. -/
abbrev cocone (X : SSet.{u}) : Cocone (stages X) :=
  ⟨X, (SSet.relativeCellComplex X).toTransfiniteCompositionOfShape.incl⟩

/-- Reuse the native cell complex's actual colimit certificate. -/
def isColimit (X : SSet.{u}) : IsColimit (cocone X) :=
  (SSet.relativeCellComplex X).toTransfiniteCompositionOfShape.isColimit

/-- Every map in the native skeleton diagram is a monomorphism. -/
theorem stages_mono (X : SSet.{u}) {a b : ℕ} (f : a ⟶ b) : Mono ((stages X).map f) := by
  change Mono (SSet.Subcomplex.homOfLE
    ((SSet.skeletonOfMono (⊥ : X.Subcomplex).ι).monotone (leOfHom f)))
  exact inferInstance

end
end DaggerNativeSimplicialSkeletonStages
