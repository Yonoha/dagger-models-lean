import RigidificationCofMixedOverlap
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.BoundaryData

noncomputable section

open PathFacets SimplicialThickening

variable {n : ℕ} {A : SC.{u}}

abbrev FacetIndex (n : ℕ) := interior n ⊕ interior n

def facetSub (n : ℕ) : FacetIndex n → (extremeHom.{u} n).Subcomplex :=
  Sum.elim (extremeOmitted n) (extremeCut n)

def boundaryDiagram (n : ℕ) : SSet.Subcomplex.MulticoequalizerDiagram
    (extremeBoundary.{u} n) (facetSub n) (fun k l => facetSub n k ⊓ facetSub n l) where
  eq_inf _ _ := rfl
  iSup_eq := by
    apply le_antisymm
    · apply iSup_le
      rintro (k | k)
      · exact omitted_le_extremeBoundary n k
      · exact cut_le_extremeBoundary n k
    · unfold extremeBoundary
      apply iSup_le
      intro k
      exact sup_le (le_iSup (facetSub n) (Sum.inl k)) (le_iSup (facetSub n) (Sum.inr k))

def facetEvaluation (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (k : FacetIndex n) : (facetSub.{u} n k).toSSet ⟶
      (vertex a 0 ⟶[SSet.{u}] vertex a (Fin.last (n + 1))) :=
  match k with
  | Sum.inl k => omittedEvaluation a k
  | Sum.inr k => cutEvaluation a k

theorem facet_overlap (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (k l : FacetIndex n) :
    SSet.Subcomplex.homOfLE (inf_le_left : facetSub n k ⊓ facetSub n l ≤ _)
        ≫ facetEvaluation a k =
      SSet.Subcomplex.homOfLE (inf_le_right : facetSub n k ⊓ facetSub n l ≤ _)
        ≫ facetEvaluation a l := by
  rcases k with k | k <;> rcases l with l | l
  · exact omitted_overlap a k l
  · exact mixed_overlap a k l
  · apply NatTrans.ext
    funext q γ
    have h := congrFun (congrArg (fun f => f.app q) (mixed_overlap a l k))
      (⟨γ.val, ⟨γ.property.2, γ.property.1⟩⟩ :
        (extremeOmitted.{u} n l ⊓ extremeCut n k).toSSet.obj q)
    exact h.symm
  · exact cut_overlap a k l

/-- Full existing colimit UP of the ENTIRE literal omit/cut boundary. -/
def boundaryIsColimit (n : ℕ) :
    IsColimit ((boundaryDiagram.{u} n).multicofork.map SSet.Subcomplex.toSSetFunctor) :=
  (boundaryDiagram n).isColimit

def boundaryMap (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A) :
    (extremeBoundary.{u} n).toSSet ⟶
      (vertex a 0 ⟶[SSet.{u}] vertex a (Fin.last (n + 1))) :=
  Multicofork.IsColimit.desc (boundaryIsColimit n) (facetEvaluation a)
    (fun k => facet_overlap a k.1 k.2)

theorem boundaryMap_restrict (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (k : FacetIndex n) :
    SSet.Subcomplex.homOfLE
      (show facetSub.{u} n k ≤ extremeBoundary n from by
        rcases k with k | k
        · exact omitted_le_extremeBoundary n k
        · exact cut_le_extremeBoundary n k) ≫ boundaryMap a = facetEvaluation a k :=
  Multicofork.IsColimit.fac (boundaryIsColimit n) (facetEvaluation a)
    (fun k => facet_overlap a k.1 k.2) k

theorem boundaryMap_hom_ext {Y : SSet.{u}} {f g : (extremeBoundary.{u} n).toSSet ⟶ Y}
    (h : ∀ k : FacetIndex n,
      SSet.Subcomplex.homOfLE
        (show facetSub.{u} n k ≤ extremeBoundary n from by
          rcases k with k | k
          · exact omitted_le_extremeBoundary n k
          · exact cut_le_extremeBoundary n k) ≫ f =
        SSet.Subcomplex.homOfLE
          (show facetSub.{u} n k ≤ extremeBoundary n from by
            rcases k with k | k
            · exact omitted_le_extremeBoundary n k
            · exact cut_le_extremeBoundary n k) ≫ g) : f = g :=
  Multicofork.IsColimit.hom_ext (boundaryIsColimit n) h

end

end DaggerOrdinaryRigidificationCof.BoundaryData
