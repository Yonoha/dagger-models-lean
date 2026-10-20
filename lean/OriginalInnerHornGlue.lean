import OriginalInnerHornDiagram
import OriginalInnerHornFacetOverlap
import OriginalInnerHornScalarExtension

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace DaggerOrdinaryRigidificationCof.InnerHornGlue

noncomputable section

open PathFacets InnerHornFaces InnerHornDiagram
open InnerHornFacetMaps InnerHornFacetOverlap

variable {n : ℕ} {A : SC.{u}} (k : interior n)
variable (D : CompatibleFaceData (n + 1) A (Admissible k))

/-- Evaluate exactly the facets present in the original inner horn. -/
def facetEvaluation (l : FacetIndex k) : (facetSub.{u} k l).toSSet ⟶
    (D.obj 0 ⟶[SSet.{u}] D.obj (Fin.last (n + 1))) :=
  match l with
  | Sum.inl l => omittedEvaluation k D l.val l.property
  | Sum.inr l => cutEvaluation k D l

theorem facet_overlap (l r : FacetIndex k) :
    SSet.Subcomplex.homOfLE (inf_le_left : facetSub k l ⊓ facetSub k r ≤ _) ≫
      facetEvaluation k D l =
        SSet.Subcomplex.homOfLE (inf_le_right : facetSub k l ⊓ facetSub k r ≤ _) ≫
          facetEvaluation k D r := by
  rcases l with l | l <;> rcases r with r | r
  · exact omitted_overlap k D l.val r.val l.property r.property
  · exact mixed_overlap k D l.val l.property r
  · apply NatTrans.ext
    funext q γ
    have h := congrFun (congrArg (fun f ↦ f.app q)
      (mixed_overlap k D r.val r.property l))
        (⟨γ.val, ⟨γ.property.2, γ.property.1⟩⟩ :
          (extremeOmitted.{u} n r.val ⊓ extremeCut n l).toSSet.obj q)
    exact h.symm
  · exact cut_overlap k D l r

/-- Descent through Mathlib's colimit of the entire literal extreme horn. -/
def hornMap : (extremeHorn.{u} n k).toSSet ⟶
    (D.obj 0 ⟶[SSet.{u}] D.obj (Fin.last (n + 1))) :=
  Multicofork.IsColimit.desc (InnerHornDiagram.isColimit k) (facetEvaluation k D)
    (fun p ↦ facet_overlap k D p.1 p.2)

theorem hornMap_restrict (l : FacetIndex k) :
    SSet.Subcomplex.homOfLE (facet_le k l) ≫ hornMap k D = facetEvaluation k D l :=
  Multicofork.IsColimit.fac (InnerHornDiagram.isColimit k) (facetEvaluation k D)
    (fun p ↦ facet_overlap k D p.1 p.2) l

theorem hornMap_cut (l : interior n) :
    SSet.Subcomplex.homOfLE (cut_le_extremeHorn n k l) ≫ hornMap k D =
      cutEvaluation k D l :=
  hornMap_restrict k D (Sum.inr l)

theorem hornMap_omitted (l : interior n) (hlk : l ≠ k) :
    SSet.Subcomplex.homOfLE (omitted_le_extremeHorn n k l hlk) ≫ hornMap k D =
      omittedEvaluation k D l hlk :=
  hornMap_restrict k D (Sum.inl ⟨l, hlk⟩)

/-- The locally Kan hypothesis extends the glued map on the extreme Hom. -/
theorem exists_extension
    [SSet.KanComplex (D.obj 0 ⟶[SSet.{u}] D.obj (Fin.last (n + 1)))] :
    ∃ ell : extremeHom.{u} n ⟶
        (D.obj 0 ⟶[SSet.{u}] D.obj (Fin.last (n + 1))),
      (extremeHorn n k).ι ≫ ell = hornMap k D :=
  extremeHorn_extension k (hornMap k D)

end

end DaggerOrdinaryRigidificationCof.InnerHornGlue
