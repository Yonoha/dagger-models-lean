import OriginalExtremeHorn
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace DaggerOrdinaryRigidificationCof.InnerHornDiagram

open PathFacets

variable {n : ℕ}

/-- Omitted facets exclude the missing index; all cut facets are present. -/
abbrev FacetIndex (k : interior n) := {l : interior n // l ≠ k} ⊕ interior n

def facetSub (k : interior n) : FacetIndex k → (extremeHom.{u} n).Subcomplex :=
  Sum.elim (fun l ↦ extremeOmitted n l.val) (extremeCut n)

theorem facet_le (k : interior n) (l : FacetIndex k) :
    facetSub.{u} k l ≤ extremeHorn n k := by
  rcases l with l | l
  · exact omitted_le_extremeHorn n k l.val l.property
  · exact cut_le_extremeHorn n k l

/-- The literal horn union, with the actual pairwise intersections as relations. -/
def diagram (k : interior n) : SSet.Subcomplex.MulticoequalizerDiagram
    (extremeHorn.{u} n k) (facetSub k) (fun l r ↦ facetSub k l ⊓ facetSub k r) where
  eq_inf _ _ := rfl
  iSup_eq := by
    apply le_antisymm
    · exact iSup_le (facet_le k)
    · unfold extremeHorn
      apply sup_le
      · apply iSup_le
        intro l
        exact le_iSup (facetSub k) (Sum.inr l)
      · apply iSup_le
        intro l
        exact le_iSup (facetSub k) (Sum.inl l)

/-- Mathlib supplies the simplicial-set colimit of this literal union. -/
noncomputable def isColimit (k : interior n) :
    IsColimit ((diagram.{u} k).multicofork.map SSet.Subcomplex.toSSetFunctor) :=
  (diagram k).isColimit

theorem hom_ext (k : interior n) {Y : SSet.{u}}
    {f g : (extremeHorn n k).toSSet ⟶ Y}
    (h : ∀ l : FacetIndex k,
      SSet.Subcomplex.homOfLE (facet_le k l) ≫ f =
        SSet.Subcomplex.homOfLE (facet_le k l) ≫ g) : f = g :=
  Multicofork.IsColimit.hom_ext (isColimit k) h

end DaggerOrdinaryRigidificationCof.InnerHornDiagram
