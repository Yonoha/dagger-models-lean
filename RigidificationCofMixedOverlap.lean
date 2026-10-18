import RigidificationCofOmittedEvaluation
import RigidificationCofFaceComposition
import RigidificationCofCutOverlap

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.BoundaryData

noncomputable section

open PathFacets SimplicialThickening

variable {n : ℕ} {A : SC.{u}}

/-- Omit/cut agreement uses the original proper-face functor's WHOLE composition map. -/
theorem mixed_overlap_component_ne (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (k l : interior n) (hkl : k ≠ l) (q : SimplexCategoryᵒᵖ)
    (γ : (extremeHom.{u} n).obj q) (hk : ∀ t, ULift.up k.val ∉ (γ.obj t).I)
    (hl : ∀ t, ULift.up l.val ∈ (γ.obj t).I) :
    (omittedEvaluation a k).app q ⟨γ, hk⟩ = (cutEvaluation a l).app q ⟨γ, hl⟩ := by
  let s := missingFace k.val
  have h0 := missingFace_zero k
  have hn := missingFace_last k
  have hmid : l.val ∈ s := (mem_missingFace k.val l.val).mpr
    (fun h => hkl (Subtype.ext h.symm))
  have hs : s.Nonempty := ⟨0, h0⟩
  have hp := missingFace_proper k.val
  let γs : (pathsInFace.{u} s 0 (Fin.last (n + 1))).toSSet.obj q :=
    ⟨γ, omitted_le_paths k.val 0 (Fin.last (n + 1)) q hk⟩
  let γl : (pathsInFace.{u} s 0 l.val).toSSet.obj q :=
    ⟨splitChainLeft ⟨γ, hl⟩, fun t x hx => γs.property t x hx.1⟩
  let γr : (pathsInFace.{u} s l.val (Fin.last (n + 1))).toSSet.obj q :=
    ⟨splitChainRight ⟨γ, hl⟩, fun t x hx => γs.property t x hx.1⟩
  have hc0 := congrFun (congrArg
    (fun f : (extremeCut.{u} n l).toSSet ⟶ (extremeCut.{u} n l).toSSet => f.app q)
    (cutInverse_map (ULift.up 0) (ULift.up l.val) (ULift.up (Fin.last (n + 1)))))
      (⟨γ, hl⟩ : (extremeCut.{u} n l).toSSet.obj q)
  have he : (compose (ULift.up 0) (ULift.up l.val)
      (ULift.up (Fin.last (n + 1)))).app q (γl.val, γr.val) = γ :=
    congrArg Subtype.val hc0
  have hleft := congrFun (congrArg (fun f => f.app q)
    (faceEvaluation_proper a s hs hp 0 l.val h0 hmid (leftProper l))) γl
  have hright := congrFun (congrArg (fun f => f.app q)
    (faceEvaluation_proper a s hs hp l.val (Fin.last (n + 1)) hmid hn (rightProper l))) γr
  change (properMap a 0 l.val (leftProper l)).app q γl.val =
    (faceEvaluation a s hs hp 0 l.val h0 hmid).app q γl at hleft
  change (properMap a l.val (Fin.last (n + 1)) (rightProper l)).app q γr.val =
    (faceEvaluation a s hs hp l.val (Fin.last (n + 1)) hmid hn).app q γr at hright
  rw [cutEvaluation_app]
  change (faceEvaluation a s hs hp 0 (Fin.last (n + 1)) h0 hn).app q γs =
    elementComp q ((properMap a 0 l.val (leftProper l)).app q γl.val)
      ((properMap a l.val (Fin.last (n + 1)) (rightProper l)).app q γr.val)
  rw [hleft, hright]
  have hc := faceEvaluation_comp a s hs hp 0 l.val (Fin.last (n + 1)) h0 hmid hn q γl γr
  have hγ : (⟨(compose (ULift.up 0) (ULift.up l.val)
      (ULift.up (Fin.last (n + 1)))).app q (γl.val, γr.val),
        compose_mem_face s 0 l.val (Fin.last (n + 1)) q γl γr⟩ :
      (pathsInFace.{u} s 0 (Fin.last (n + 1))).toSSet.obj q) = γs := Subtype.ext he
  rw [hγ] at hc
  exact hc

/-- All mixed overlaps, INCLUDING the actual empty same-position intersection. -/
theorem mixed_overlap (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (k l : interior n) :
    SSet.Subcomplex.homOfLE (inf_le_left : extremeOmitted n k ⊓ extremeCut n l ≤ _)
        ≫ omittedEvaluation a k =
      SSet.Subcomplex.homOfLE (inf_le_right : extremeOmitted n k ⊓ extremeCut n l ≤ _)
        ≫ cutEvaluation a l := by
  apply NatTrans.ext
  funext q γ
  by_cases hkl : k = l
  · subst l
    exact False.elim (γ.property.1 0 (γ.property.2 0))
  · exact mixed_overlap_component_ne a k l hkl q γ.val γ.property.1 γ.property.2

end

end DaggerOrdinaryRigidificationCof.BoundaryData
