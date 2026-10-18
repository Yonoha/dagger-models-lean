import OriginalInnerHornFacetMaps

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.InnerHornFacetOverlap

noncomputable section

open BoundaryData PathFacets SimplicialThickening InnerHornFaces
open InnerHornFacetMaps

variable {n : ℕ} {A : SC.{u}}
variable (k : interior n)
variable (D : CompatibleFaceData (n + 1) A (Admissible k))

/-- Two ordered cuts use the same three original interval Hom maps. -/
theorem cut_overlap_component_lt (l m : interior n) (hlm : l.val < m.val)
    (q : SimplexCategoryᵒᵖ) (γ : (extremeHom.{u} n).obj q)
    (hl : ∀ t, ULift.up l.val ∈ (γ.obj t).I)
    (hm : ∀ t, ULift.up m.val ∈ (γ.obj t).I) :
    (cutEvaluation k D l).app q ⟨γ, hl⟩ =
      (cutEvaluation k D m).app q ⟨γ, hm⟩ := by
  rw [InnerHornFacetMaps.cutEvaluation_app, InnerHornFacetMaps.cutEvaluation_app,
    splitRight_double γ hl hm
      (show ULift.up.{u} l.val ≤ ULift.up m.val from hlm.le),
    splitLeft_double γ hl hm
      (show ULift.up.{u} l.val ≤ ULift.up m.val from hlm.le)]
  rw [evaluateProper_comp k D l.val m.val (Fin.last (n + 1))
      hlm.le (Fin.le_last _) (rightProper l) (middleProper l m) (rightProper m),
    evaluateProper_comp k D 0 l.val m.val (Fin.zero_le _) hlm.le
      (leftProper m) (leftProper l) (middleProper l m)]
  exact (element_assoc q _ _ _).symm

/-- Cut evaluations agree on their complete actual intersection. -/
theorem cut_overlap (l m : interior n) :
    SSet.Subcomplex.homOfLE
        (inf_le_left : extremeCut n l ⊓ extremeCut n m ≤ _) ≫
      cutEvaluation k D l =
        SSet.Subcomplex.homOfLE
          (inf_le_right : extremeCut n l ⊓ extremeCut n m ≤ _) ≫
            cutEvaluation k D m := by
  apply NatTrans.ext
  funext q γ
  rcases lt_trichotomy l.val m.val with h | h | h
  · exact cut_overlap_component_lt k D l m h q γ.val γ.property.1 γ.property.2
  · have e : l = m := Subtype.ext h
    cases e
    rfl
  · exact (cut_overlap_component_lt k D m l h q γ.val
      γ.property.2 γ.property.1).symm

/-- Omitted evaluations agree on the whole admitted common face. -/
theorem omitted_overlap (l m : interior n) (hlk : l ≠ k) (hmk : m ≠ k) :
    SSet.Subcomplex.homOfLE
        (inf_le_left : extremeOmitted n l ⊓ extremeOmitted n m ≤ _) ≫
      omittedEvaluation k D l hlk =
        SSet.Subcomplex.homOfLE
          (inf_le_right : extremeOmitted n l ⊓ extremeOmitted n m ≤ _) ≫
            omittedEvaluation k D m hmk := by
  let s := missingFace l.val ∩ missingFace m.val
  have hi : (0 : Fin (n + 2)) ∈ s :=
    Finset.mem_inter.mpr ⟨missingFace_zero l, missingFace_zero m⟩
  have hj : Fin.last (n + 1) ∈ s :=
    Finset.mem_inter.mpr ⟨missingFace_last l, missingFace_last m⟩
  have hs : s.Nonempty := ⟨0, hi⟩
  have hps : Admissible k s :=
    admissible_mono k (omittedAdmissible k l hlk) Finset.inter_subset_left
  have hUs : extremeOmitted.{u} n l ⊓ extremeOmitted n m ≤
      pathsInFace s 0 (Fin.last (n + 1)) := by
    intro q γ h t x hx
    have hl' := omitted_le_paths l.val 0 (Fin.last (n + 1)) q h.1
    have hm' := omitted_le_paths m.val 0 (Fin.last (n + 1)) q h.2
    exact Finset.mem_inter.mpr ⟨hl' t x hx, hm' t x hx⟩
  unfold InnerHornFacetMaps.omittedEvaluation
  rw [← Category.assoc, SSet.Subcomplex.homOfLE_comp,
    ← Category.assoc, SSet.Subcomplex.homOfLE_comp]
  rw [evaluation_from_common k D s (missingFace l.val) hs
      ⟨0, missingFace_zero l⟩ hps (omittedAdmissible k l hlk)
      Finset.inter_subset_left hi hj hUs,
    evaluation_from_common k D s (missingFace m.val) hs
      ⟨0, missingFace_zero m⟩ hps (omittedAdmissible k m hmk)
      Finset.inter_subset_right hi hj hUs]

/-- A distinct cut and admitted omitted face use one whole face composition. -/
theorem mixed_overlap_component_ne (l m : interior n)
    (hlk : l ≠ k) (hlm : l ≠ m) (q : SimplexCategoryᵒᵖ)
    (γ : (extremeHom.{u} n).obj q)
    (hl : ∀ t, ULift.up l.val ∉ (γ.obj t).I)
    (hm : ∀ t, ULift.up m.val ∈ (γ.obj t).I) :
    (omittedEvaluation k D l hlk).app q ⟨γ, hl⟩ =
      (cutEvaluation k D m).app q ⟨γ, hm⟩ := by
  let s := missingFace l.val
  have h0 := missingFace_zero l
  have hn := missingFace_last l
  have hmid : m.val ∈ s := (mem_missingFace l.val m.val).mpr
    (fun h ↦ hlm (Subtype.ext h.symm))
  have hs : s.Nonempty := ⟨0, h0⟩
  have hp := omittedAdmissible k l hlk
  let γs : (pathsInFace.{u} s 0 (Fin.last (n + 1))).toSSet.obj q :=
    ⟨γ, omitted_le_paths l.val 0 (Fin.last (n + 1)) q hl⟩
  let γl : (pathsInFace.{u} s 0 m.val).toSSet.obj q :=
    ⟨splitChainLeft ⟨γ, hm⟩, fun t x hx ↦ γs.property t x hx.1⟩
  let γr : (pathsInFace.{u} s m.val (Fin.last (n + 1))).toSSet.obj q :=
    ⟨splitChainRight ⟨γ, hm⟩, fun t x hx ↦ γs.property t x hx.1⟩
  have hc0 := congrFun (congrArg
    (fun f : (extremeCut.{u} n m).toSSet ⟶ (extremeCut.{u} n m).toSSet ↦ f.app q)
    (cutInverse_map (ULift.up 0) (ULift.up m.val) (ULift.up (Fin.last (n + 1)))))
      (⟨γ, hm⟩ : (extremeCut.{u} n m).toSSet.obj q)
  have he : (compose (ULift.up 0) (ULift.up m.val)
      (ULift.up (Fin.last (n + 1)))).app q (γl.val, γr.val) = γ :=
    congrArg Subtype.val hc0
  have hleft := congrFun (congrArg (fun f ↦ f.app q)
    (faceEvaluation_proper k D s hs hp 0 m.val h0 hmid (leftProper m))) γl
  have hright := congrFun (congrArg (fun f ↦ f.app q)
    (faceEvaluation_proper k D s hs hp m.val (Fin.last (n + 1))
      hmid hn (rightProper m))) γr
  change (InnerHornProperMaps.properMap k D 0 m.val (leftProper m)).app q γl.val =
    (D.faceEvaluation s hs hp 0 m.val h0 hmid).app q γl at hleft
  change (InnerHornProperMaps.properMap k D m.val
      (Fin.last (n + 1)) (rightProper m)).app q γr.val =
        (D.faceEvaluation s hs hp m.val (Fin.last (n + 1)) hmid hn).app q γr
          at hright
  rw [InnerHornFacetMaps.cutEvaluation_app]
  change (D.faceEvaluation s hs hp 0 (Fin.last (n + 1)) h0 hn).app q γs =
    elementComp q
      ((InnerHornProperMaps.properMap k D 0 m.val (leftProper m)).app q γl.val)
      ((InnerHornProperMaps.properMap k D m.val
        (Fin.last (n + 1)) (rightProper m)).app q γr.val)
  rw [hleft, hright]
  have hc := D.faceEvaluation_comp s hs hp 0 m.val (Fin.last (n + 1))
    h0 hmid hn q γl γr
  have hγ : (⟨(compose (ULift.up 0) (ULift.up m.val)
      (ULift.up (Fin.last (n + 1)))).app q (γl.val, γr.val),
        compose_mem_face s 0 m.val (Fin.last (n + 1)) q γl γr⟩ :
      (pathsInFace.{u} s 0 (Fin.last (n + 1))).toSSet.obj q) = γs := Subtype.ext he
  rw [hγ] at hc
  exact hc

/-- All mixed intersections, including the empty same-position intersection. -/
theorem mixed_overlap (l : interior n) (hlk : l ≠ k) (m : interior n) :
    SSet.Subcomplex.homOfLE
        (inf_le_left : extremeOmitted n l ⊓ extremeCut n m ≤ _) ≫
      omittedEvaluation k D l hlk =
        SSet.Subcomplex.homOfLE
          (inf_le_right : extremeOmitted n l ⊓ extremeCut n m ≤ _) ≫
            cutEvaluation k D m := by
  apply NatTrans.ext
  funext q γ
  by_cases hlm : l = m
  · subst m
    exact False.elim (γ.property.1 0 (γ.property.2 0))
  · exact mixed_overlap_component_ne k D l m hlk hlm q γ.val
      γ.property.1 γ.property.2

end

end DaggerOrdinaryRigidificationCof.InnerHornFacetOverlap
