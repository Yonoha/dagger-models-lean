import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.CategoryTheory.LiftingProperties.Limits

/-! Boundary RLP implies Mathlib's actual Kan fibration predicate.
The missing face gives a pushout of a lower boundary inclusion. No model-category
structure or weak-equivalence characterization is assumed. -/

open CategoryTheory Limits Simplicial Opposite SSet

universe u

namespace DaggerModels.SSetBoundaryFibration

lemma succAbove_range_union_singleton_eq_univ_iff {n : ℕ} (i : Fin (n + 2))
    {α : Type*} (f : α → Fin (n + 1)) :
    Set.range (i.succAbove ∘ f) ∪ {i} = Set.univ ↔ Function.Surjective f := by
  constructor
  · intro h a
    have ha : i.succAbove a ∈ Set.range (i.succAbove ∘ f) ∪ {i} := by
      rw [h]
      trivial
    rcases ha with ⟨b, hb⟩ | ha
    · exact ⟨b, Fin.succAbove_right_injective hb⟩
    · exact (Fin.succAbove_ne i a ha).elim
  · intro h
    apply Set.eq_univ_of_forall
    intro b
    by_cases hb : b = i
    · exact Or.inr hb
    · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hb
      obtain ⟨c, rfl⟩ := h a
      exact Or.inl ⟨c, rfl⟩

/-- Restricting a horn to its missing face is exactly the lower boundary, including `n=0`. -/
lemma horn_preimage_δ (n : ℕ) (i : Fin (n + 2)) :
    (horn.{u} (n + 1) i).preimage (stdSimplex.δ i) = boundary n := by
  ext m s
  change (Set.range (i.succAbove ∘ stdSimplex.asOrderHom s) ∪ {i} ≠ Set.univ) ↔
    ¬ Function.Surjective (stdSimplex.asOrderHom s)
  exact not_congr (succAbove_range_union_singleton_eq_univ_iff i _)

/-- Adding the missing codimension-one face to a horn gives the upper boundary. -/
lemma horn_sup_missingFace (n : ℕ) (i : Fin (n + 2)) :
    horn.{u} (n + 1) i ⊔ stdSimplex.face {i}ᶜ = boundary (n + 1) := by
  rw [horn_eq_iSup, boundary_eq_iSup]
  apply le_antisymm
  · refine sup_le ?_ (le_iSup (fun j : Fin (n + 2) ↦ stdSimplex.face.{u} {j}ᶜ) i)
    apply iSup_le
    intro j
    exact le_iSup (fun k : Fin (n + 2) ↦ stdSimplex.face.{u} {k}ᶜ) j.val
  · apply iSup_le
    intro j
    by_cases hj : j = i
    · subst j
      exact le_sup_right
    · exact (le_iSup (fun k : ({i}ᶜ : Set (Fin (n + 2))) ↦
        stdSimplex.face.{u} {k.val}ᶜ) ⟨j, hj⟩).trans le_sup_left

/-- A general image/preimage identity, applied below to the actual coface map. -/
lemma image_preimage_eq_inf_range {X Y : SSet.{u}} (A : X.Subcomplex) (f : Y ⟶ X) :
    (A.preimage f).image f = A ⊓ Subcomplex.range f := by
  ext m s
  exact Set.ext_iff.mp Set.image_preimage_eq_inter_range s

/-- The image of the lower boundary is precisely the horn's intersection with its missing face. -/
lemma lowerBoundary_image (n : ℕ) (i : Fin (n + 2)) :
    (boundary.{u} n).image (stdSimplex.δ i) =
      horn (n + 1) i ⊓ stdSimplex.face {i}ᶜ := by
  rw [← horn_preimage_δ n i, image_preimage_eq_inf_range, stdSimplex.range_δ]

/-- The lattice square consisting of a horn and its missing face. -/
def missingFaceSq (n : ℕ) (i : Fin (n + 2)) :
    Lattice.BicartSq ((boundary.{u} n).image (stdSimplex.δ i))
      (horn (n + 1) i) (stdSimplex.face {i}ᶜ) (boundary (n + 1)) where
  sup_eq := horn_sup_missingFace n i
  inf_eq := (lowerBoundary_image n i).symm

noncomputable section

/-- The boundary of the missing face, mapped into the horn. -/
def boundaryToHorn (n : ℕ) (i : Fin (n + 2)) :
    (boundary.{u} n : SSet) ⟶ (horn (n + 1) i : SSet) :=
  (boundary n).toImage (stdSimplex.δ i) ≫ Subcomplex.homOfLE (missingFaceSq n i).le₁₂

/-- The canonical inclusion of a horn into the upper boundary. -/
def hornToBoundary (n : ℕ) (i : Fin (n + 2)) :
    (horn.{u} (n + 1) i : SSet) ⟶ (boundary (n + 1) : SSet) :=
  Subcomplex.homOfLE (missingFaceSq n i).le₂₄

/-- The missing face, included in the upper boundary. -/
def missingFaceToBoundary (n : ℕ) (i : Fin (n + 2)) :
    Δ[n] ⟶ (boundary.{u} (n + 1) : SSet) :=
  (stdSimplex.faceSingletonComplIso i).hom ≫ Subcomplex.homOfLE (missingFaceSq n i).le₃₄

/-- The coface induces an isomorphism onto the image of its lower boundary. -/
def lowerBoundaryImageIso (n : ℕ) (i : Fin (n + 2)) :
    (boundary.{u} n : SSet) ≅ ((boundary n).image (stdSimplex.δ i) : SSet) := by
  have : Mono (stdSimplex.δ.{u} i) := by
    rw [← stdSimplex.faceSingletonComplIso_hom_ι i]
    infer_instance
  have : Mono ((boundary.{u} n).toImage (stdSimplex.δ i)) :=
    mono_of_mono_fac (Subcomplex.toImage_ι _ _)
  have := isIso_of_mono_of_epi ((boundary.{u} n).toImage (stdSimplex.δ i))
  exact asIso ((boundary.{u} n).toImage (stdSimplex.δ i))

/-- A horn-to-boundary inclusion is a pushout of the lower boundary inclusion. -/
lemma missingFaceIsPushout (n : ℕ) (i : Fin (n + 2)) :
    IsPushout (boundaryToHorn.{u} n i) (boundary n).ι
      (hornToBoundary n i) (missingFaceToBoundary n i) := by
  apply (Subcomplex.BicartSq.isPushout (missingFaceSq n i)).of_iso'
    (lowerBoundaryImageIso n i) (Iso.refl _) (stdSimplex.faceSingletonComplIso i)
    (Iso.refl _)
  · simp only [lowerBoundaryImageIso, asIso_hom, Iso.refl_hom, Category.comp_id]
    rfl
  · apply (cancel_mono (stdSimplex.face {i}ᶜ).ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι,
      stdSimplex.faceSingletonComplIso_hom_ι, lowerBoundaryImageIso, asIso_hom,
      Subcomplex.toImage_ι]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, hornToBoundary]
  · simp only [Iso.refl_hom, Category.comp_id, missingFaceToBoundary]

@[reassoc (attr := simp)]
lemma hornToBoundary_ι (n : ℕ) (i : Fin (n + 2)) :
    hornToBoundary.{u} n i ≫ (boundary (n + 1)).ι = (horn (n + 1) i).ι :=
  Subcomplex.homOfLE_ι (missingFaceSq n i).le₂₄

/-- Lifting against all boundaries gives lifting against every positive-dimensional horn. -/
theorem horn_rlp_of_boundary_rlp {X Y : SSet.{u}} (p : X ⟶ Y)
    (h : ∀ n : ℕ, HasLiftingProperty (boundary.{u} n).ι p)
    (n : ℕ) (i : Fin (n + 2)) : HasLiftingProperty (horn (n + 1) i).ι p := by
  have := h n
  have := (missingFaceIsPushout n i).hasLiftingProperty p
  have := h (n + 1)
  rw [← hornToBoundary_ι n i]
  infer_instance

/-- The actual Mathlib boundary family has RLP contained in the actual horn family's RLP. -/
theorem boundary_rlp_le_horn_rlp :
    modelCategoryQuillen.I.{u}.rlp ≤ modelCategoryQuillen.J.rlp := by
  intro X Y p hp A B f hf
  simp only [modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  exact horn_rlp_of_boundary_rlp p
    (fun k ↦ hp _ (modelCategoryQuillen.boundary_ι_mem_I k)) n i

open modelCategoryQuillen in
/-- Boundary lifting implies the existing Mathlib Kan fibration class, without extra premises. -/
theorem fibration_of_boundary_rlp {X Y : SSet.{u}} (p : X ⟶ Y)
    (h : ∀ n : ℕ, HasLiftingProperty (boundary.{u} n).ι p) :
    HomotopicalAlgebra.Fibration p := by
  rw [modelCategoryQuillen.fibration_iff]
  apply boundary_rlp_le_horn_rlp
  rintro A B f ⟨n⟩
  exact h n

open modelCategoryQuillen in
/-- An inclusion into Mathlib's literal fibration property on simplicial sets. -/
theorem boundary_rlp_le_fibrations :
    modelCategoryQuillen.I.{u}.rlp ≤ HomotopicalAlgebra.fibrations SSet.{u} :=
  boundary_rlp_le_horn_rlp

end

end DaggerModels.SSetBoundaryFibration
