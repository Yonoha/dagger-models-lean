import OriginalFlagOriginalNormalization

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

theorem wedge_joint_set (T U : NecklaceCode) :
    {v : Vertices.{u} (wedge T U) | v.down ∈ (wedge T U).joints} =
      mapVertices (wedgeιLeft T U) '' {v | v.down ∈ T.joints} ∪
        mapVertices (wedgeιRight T U) '' {v | v.down ∈ U.joints} := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hv
      left
      refine ⟨ULift.up w, hw, ?_⟩
      rw [wedgeιLeft_vertices]
      exact ULift.ext _ _ he
    · obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hv
      right
      refine ⟨ULift.up w, hw, ?_⟩
      rw [wedgeιRight_vertices]
      exact ULift.ext _ _ he
  · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
    · rw [wedgeιLeft_vertices]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨w.down, hw, rfl⟩))
    · rw [wedgeιRight_vertices]
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨w.down, hw, rfl⟩))

theorem wedgeMap_joint_image {T U T' U' : NecklaceCode}
    (f : NecklaceCode.Hom.{u} T T') (g : NecklaceCode.Hom.{u} U U')
    (hf : mapVertices f.map '' {v | v.down ∈ T.joints} = {v | v.down ∈ T'.joints})
    (hg : mapVertices g.map '' {v | v.down ∈ U.joints} = {v | v.down ∈ U'.joints}) :
    mapVertices (wedgeMap f g).map '' {v | v.down ∈ (wedge T U).joints} =
      {v | v.down ∈ (wedge T' U').joints} := by
  have hl := congrArg mapVertices (wedgeMap_left f g)
  have hr := congrArg mapVertices (wedgeMap_right f g)
  rw [mapVertices_comp, mapVertices_comp] at hl hr
  rw [wedge_joint_set, Set.image_union, ← Set.image_comp, ← Set.image_comp]
  rw [hl, hr, Set.image_comp, Set.image_comp, hf, hg, ← wedge_joint_set]

theorem singleOperatorHom_joint_image {m n : ℕ} (s : ⦋m⦌ ⟶ ⦋n⦌) [Epi s] :
    mapVertices (singleOperatorHom.{u} s).map '' {v | v.down ∈ (single m).joints} =
      {v | v.down ∈ (single n).joints} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases (mem_single_joints m w.down).mp hw with hw | hw
    · rw [singleOperatorHom_vertices, hw, simplex_epi_first]
      exact (single n).first_mem
    · rw [singleOperatorHom_vertices, hw, simplex_epi_last]
      exact (single n).last_mem
  · intro hv
    rcases (mem_single_joints n v.down).mp hv with hv | hv
    · refine ⟨ULift.up 0, (single m).first_mem, ?_⟩
      rw [singleOperatorHom_vertices, simplex_epi_first]
      exact ULift.ext _ _ hv.symm
    · refine ⟨ULift.up (Fin.last m), (single m).last_mem, ?_⟩
      rw [singleOperatorHom_vertices, simplex_epi_last]
      exact ULift.ext _ _ hv.symm

theorem orderedPrefix_joint_image (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code) :
    mapVertices (orderedPrefix P k hk).ν.hom.map ''
      {v | v.down ∈ (orderedPrefix P k hk).source.code.joints} =
      {v | v.down ∈ (orderedPrefix P k hk).normalized.code.joints} := by
  induction k with
  | zero =>
    change mapVertices (𝟙 NecklaceCode.point.toSSet) ''
      {v : Vertices.{u} NecklaceCode.point | v.down ∈ NecklaceCode.point.joints} = _
    rw [mapVertices_id]
    exact Set.image_id _
  | succ k ih =>
    let hp : k ≤ beadCount P.code := Nat.le_of_succ_le hk
    let c := jointBead P.code ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
    let d := normalizeBead P c
    letI := d.epi
    change mapVertices (wedgeMap (orderedPrefix P k hp).ν.hom
      (normalizedBeadHom P c d).hom).map '' _ = _
    exact wedgeMap_joint_image _ _ (ih hp) (singleOperatorHom_joint_image d.operator)

theorem assembledNormalization_joint_image (P : NecklacesOver X a b) :
    mapVertices (assembledNormalization P).hom.map ''
      {v | v.down ∈ (assembledSource P).code.joints} =
      {v | v.down ∈ (normOver P).code.joints} := orderedPrefix_joint_image P _ _

theorem sourceAssemblyInverse_joint_image (P : NecklacesOver X a b) :
    mapVertices (sourceAssemblyIso P).inv.hom.map '' {v | v.down ∈ P.code.joints} =
      {v | v.down ∈ (assembledSource P).code.joints} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    change mapVertices (sourceAssemblyCodeInverse P).map w ∈
      {v | v.down ∈ (assembledSource P).code.joints}
    rw [sourceAssemblyCodeInverse_vertices]
    exact (sourceAssembly_inverse_joint_iff P w.down).mpr hw
  · intro hv
    refine ⟨ULift.up (sourceAssemblyOrderIso P v.down),
      (sourceAssembly_joint_iff P v.down).mp hv, ?_⟩
    change mapVertices (sourceAssemblyCodeInverse P).map
      (ULift.up (sourceAssemblyOrderIso P v.down)) = v
    rw [sourceAssemblyCodeInverse_vertices]
    apply ULift.ext
    exact (sourceAssemblyOrderIso P).symm_apply_apply v.down

/-- BOTH images of the actual original joints and all collapsed joint repetitions are retained. -/
theorem originalNormalization_joint_image (P : NecklacesOver X a b) :
    mapVertices (originalNormalization P).hom.map '' {v | v.down ∈ P.code.joints} =
      {v | v.down ∈ (normOver P).code.joints} := by
  rw [originalNormalization_whole, mapVertices_comp, Set.image_comp,
    sourceAssemblyInverse_joint_image, assembledNormalization_joint_image]

theorem originalNormalizedFlag_flanked (P : NecklacesOver X a b) {n : ℕ}
    (F : Flag.{u} P.code n) (hF : Flanked F) : Flanked (originalNormalizedFlag P F) := by
  constructor
  · change mapVertices (originalNormalization P).hom.map '' F.chain 0 = _
    rw [hF.1, originalNormalization_joint_image]
  · change mapVertices (originalNormalization P).hom.map '' F.chain (Fin.last n) = Set.univ
    rw [hF.2, Set.image_univ]
    exact Set.range_eq_univ.mpr (originalNormalization_surjective P)

end

end DaggerOriginalFlagFlankification
