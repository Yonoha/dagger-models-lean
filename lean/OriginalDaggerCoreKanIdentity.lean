import OriginalDaggerCoreCandidateFunctor

/-!
# The exact dagger core inclusion is an isomorphism on Kan inputs

An invertible underlying simplicial map has a dagger-preserving inverse by the
original commutation equation. The already proved top-core theorem for Kan inputs
therefore identifies the original dagger core inclusion as an actual isomorphism.
This does not assume or prove the candidate's Kan property for general quasi-categories.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreContainsKanSubcomplexes
open DaggerOriginalDaggerCoreCandidate

universe u

namespace DaggerOriginalDaggerCoreKanIdentity

noncomputable section

/-- The inverse of an invertible underlying map obeys the original dagger equation. -/
def daggerInverse {X Y : DaggerSSet.{u}} (f : X ⟶ Y) [IsIso f.hom] : Y ⟶ X where
  hom := inv f.hom
  comm := by
    apply (cancel_epi f.hom).mp
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    rw [f.comm, Category.assoc, ← SSet.opFunctor.map_comp, IsIso.hom_inv_id,
      SSet.opFunctor.map_id, Category.comp_id]

/-- An invertible underlying simplicial map is an isomorphism in the actual dagger category. -/
theorem dagger_isIso_of_isIso_hom {X Y : DaggerSSet.{u}} (f : X ⟶ Y) [IsIso f.hom] :
    IsIso f := by
  refine ⟨⟨daggerInverse f, ?_, ?_⟩⟩
  · apply DaggerSSet.Hom.ext
    exact IsIso.hom_inv_id f.hom
  · apply DaggerSSet.Hom.ext
    exact IsIso.inv_hom_id f.hom

/-- The literal underlying core inclusion is invertible when the original input is Kan. -/
theorem daggerCoreInclusion_hom_isIso_of_kan (X : DaggerSSet.{u}) [X.toSSet.KanComplex] :
    IsIso (daggerCoreInclusion X).hom := by
  change IsIso (ordinaryCoreCandidate X.toSSet).ι
  rw [ordinaryCoreCandidate_eq_top_of_kan]
  change IsIso (SSet.Subcomplex.topIso X.toSSet).hom
  infer_instance

/-- On Kan inputs the exact natural dagger core inclusion is already an isomorphism. -/
theorem daggerCoreInclusion_isIso_of_kan (X : DaggerSSet.{u}) [X.toSSet.KanComplex] :
    IsIso (daggerCoreInclusion X) := by
  have : IsIso (daggerCoreInclusion X).hom := daggerCoreInclusion_hom_isIso_of_kan X
  exact dagger_isIso_of_isIso_hom (daggerCoreInclusion X)

/-- The original Kan dagger simplicial set is recovered by its exact core inclusion. -/
def daggerCoreIsoOfKan (X : DaggerSSet.{u}) [X.toSSet.KanComplex] : daggerCoreCandidate X ≅ X := by
  have : IsIso (daggerCoreInclusion X) := daggerCoreInclusion_isIso_of_kan X
  exact asIso (daggerCoreInclusion X)

end

end DaggerOriginalDaggerCoreKanIdentity
