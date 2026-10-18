import ActualOriginalNecklaceSpineAttachment

/-! The SAME original necklace inclusion, including its original zero-length branch, is weak. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerNativeStandardSpineInner DaggerNativeStandardSpineGeometry
open DaggerNativeJoyalMappingTest DaggerChosenRigidificationNecklace
open DaggerNativeFiniteSubcomplexWeakGluing DaggerActualOriginalNecklaceSpineGeometry
open DaggerActualOriginalNecklaceSpineAttachment
universe u
namespace DaggerActualOriginalNecklaceInclusionWeak
noncomputable section

variable (T : NecklaceCode)

theorem finite_bead_union_eq [Fintype T.Bead] :
    spine.{u} T.len ⊔ Finset.univ.sup (NecklaceCode.Bead.face (T := T)) = T.complex := by
  apply le_antisymm
  · apply sup_le (spine_le_complex T)
    apply Finset.sup_le
    intro b _
    exact le_sup_of_le_right (le_iSup (fun c : T.Bead ↦ c.face) b)
  · apply sup_le
    · exact le_trans (vertexFace_le 0) le_sup_left
    · apply iSup_le
      intro b
      exact le_trans (Finset.le_sup (Finset.mem_univ b)) le_sup_right

theorem spine_to_complex_weak : weakCategoricalEquivalences
    (SSet.Subcomplex.homOfLE (spine_le_complex.{u} T)) := by
  classical
  letI : Fintype T.Bead := Fintype.ofFinite T.Bead
  have h := finite_union_weak (spine.{u} T.len) (NecklaceCode.Bead.face (T := T))
    Finset.univ (bead_overlap_le_spine T) (fun b ↦ intersection_categorical_weak b)
  exact (weak_inclusion_congr rfl (finite_bead_union_eq T) _ _).mp h

theorem complex_inclusion_weak :
    weakCategoricalEquivalences (NecklaceCode.complex.{u} T).ι := by
  let j := SSet.Subcomplex.homOfLE (spine_le_complex.{u} T)
  have hj : weakCategoricalEquivalences j := spine_to_complex_weak T
  have he : j ≫ T.complex.ι = (spine T.len).ι := SSet.Subcomplex.homOfLE_ι _
  exact weakCategoricalEquivalences.of_precomp j T.complex.ι hj
    (he.symm ▸ inclusion_categorical_weak T.len)

theorem original_inclusion_weak :
    weakCategoricalEquivalences (NecklaceCode.inclusion.{u} T) := by
  exact weakCategoricalEquivalences.comp_mem T.complexIso.hom T.complex.ι
    (MorphismProperty.of_isIso _ _) (complex_inclusion_weak T)

end
end DaggerActualOriginalNecklaceInclusionWeak
