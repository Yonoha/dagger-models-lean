import OriginalCounitRightConeQFaceSupportReconciled
import OriginalFlagAugmentationToCenters

/-!
# Support of the canonical flag center

The existing terminal totally nondegenerate center of a flagged-necklace
quotient class inherits the entire simplicial image support of *every*
representative of that class. First take the original flank inclusion,
which only restricts the representative's image. Then apply the retained
flanked code-epi theorem to the existing arrow from that flank to the
chosen center. No quotient equality is silently replaced by a code map.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace NecklaceCode
open DaggerOriginalFlagFlankification
open DaggerOriginalCounitRightConeQFaceSupport

universe u

namespace DaggerOriginalCounitRightConeQCenterSupport

noncomputable section

/-- The canonical center has no support outside any chosen representative. -/
theorem center_support_of_representative
    (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (p : Degree X a b n) (A : X.Subcomplex)
    (hp : SSet.Subcomplex.range p.1.map ≤ A) :
    SSet.Subcomplex.range
      (centerDegreeObj X a b n (classOf X a b n p)).1.map ≤ A := by
  let fp : Degree X a b n := (flankification X a b n).obj p
  let cp : Degree X a b n := centerDegreeObj X a b n (classOf X a b n p)
  let h : fp.1 ⟶ cp.1 := ((toCenters X a b n).app p).val
  have hfp : SSet.Subcomplex.range fp.1.map ≤ A := by
    change SSet.Subcomplex.range ((flankInclusion p.2).map ≫ p.1.map) ≤ A
    exact (Subfunctor.range_comp_le _ _).trans hp
  have hF : Flanked fp.2 := flankification_flanked p
  have hG : Flanked cp.2 := (fiberCenter X a b n (classOf X a b n p)).property
  have hFG : NecklaceCode.Flag.map h.hom fp.2 = cp.2 :=
    toCenters_flag X a b n p
  letI : Epi h.hom.map := flanked_code_epi fp.2 cp.2 h.hom hFG hF hG
  exact support_descends_of_epi (P := fp.1) (R := cp.1) h A hfp

/-- Equal quotient classes use the same actual canonical center, whose
whole necklace map is supported in both source subcomplexes. -/
theorem center_support_of_equal_class
    (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (p q : Degree X a b n)
    (heq : classOf X a b n p = classOf X a b n q)
    (A B : X.Subcomplex)
    (hp : SSet.Subcomplex.range p.1.map ≤ A)
    (hq : SSet.Subcomplex.range q.1.map ≤ B) :
    SSet.Subcomplex.range
      (centerDegreeObj X a b n (classOf X a b n p)).1.map ≤ A ⊓ B := by
  apply le_inf (center_support_of_representative X a b n p A hp)
  have hc : SSet.Subcomplex.range
      (centerDegreeObj X a b n (classOf X a b n p)).1.map =
      SSet.Subcomplex.range
        (centerDegreeObj X a b n (classOf X a b n q)).1.map :=
    congrArg (fun t ↦ SSet.Subcomplex.range
      (centerDegreeObj X a b n t).1.map) heq
  rw [hc]
  exact center_support_of_representative X a b n q B hq

end

end DaggerOriginalCounitRightConeQCenterSupport
