import DaggerModels.SimplicialEnrichment
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Comma.Arrow

/-! Full mapping-space transport along an actual isomorphism of the original bundled
simplicial categories. All objects, hom simplices and simplex operators are unchanged. -/

open CategoryTheory DaggerModels

universe o v

namespace DaggerSimplicialIsoHoms

noncomputable section

variable {C D E : SimplicialCat.{o, v}}

abbrev degree (F : C ⟶ D) (q : SimplexCategoryᵒᵖ) := SimplicialEnrichment.functor F q

theorem degree_id (C : SimplicialCat.{o, v}) (q : SimplexCategoryᵒᵖ) :
    degree (𝟙 C) q = 𝟭 (SimplicialEnrichment.At C.Obj q) := rfl

theorem degree_comp (F : C ⟶ D) (G : D ⟶ E) (q : SimplexCategoryᵒᵖ) :
    degree (F ≫ G) q = degree F q ⋙ degree G q := rfl

instance degreeIsEquivalence (e : C ≅ D) (q : SimplexCategoryᵒᵖ) :
    (degree e.hom q).IsEquivalence :=
  Functor.IsEquivalence.mk' (degree e.inv q)
    (eqToIso (by rw [← degree_comp, e.hom_inv_id, degree_id]))
    (eqToIso (by rw [← degree_comp, e.inv_hom_id, degree_id]))

theorem component_bijective (e : C ≅ D) (a b : C.Obj) (q : SimplexCategoryᵒᵖ) :
    Function.Bijective ((e.hom.map a b).app q) :=
  (Functor.FullyFaithful.ofFullyFaithful (degree e.hom q)).map_bijective a b

instance componentIsIso (e : C ≅ D) (a b : C.Obj) (q : SimplexCategoryᵒᵖ) :
    IsIso ((e.hom.map a b).app q) :=
  (isIso_iff_bijective _).mpr (component_bijective e a b q)

instance mapIsIso (e : C ≅ D) (a b : C.Obj) : IsIso (e.hom.map a b) :=
  NatIso.isIso_of_isIso_app (e.hom.map a b)

/-- The hom is literally the original full enriched-functor map. -/
def homIso (e : C ≅ D) (a b : C.Obj) :
    (a ⟶[SSet.{v}] b) ≅ (e.hom.obj a ⟶[SSet.{v}] e.hom.obj b) :=
  asIso (e.hom.map a b)

/-- Keep the original source and postcompose its original arrow with the same hom map. -/
def postcompArrowIso (e : C ≅ D) (a b : C.Obj) {A : SSet.{v}}
    (i : A ⟶ (a ⟶[SSet.{v}] b)) :
    Arrow.mk i ≅ Arrow.mk (i ≫ e.hom.map a b) :=
  Arrow.isoMk (Iso.refl _) (homIso e a b) (by simp [homIso])

end

end DaggerSimplicialIsoHoms
