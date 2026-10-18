import AmalgamPaddedRaw
import SimplicialIsoHoms

/-! Nonempty vertices in every original amalgam Hom, including arbitrary pushout apices. -/

open CategoryTheory Limits DaggerModels DaggerAmalgamPresentation
open DaggerAmalgamPaddedClassification
open Simplicial

universe u

set_option autoImplicit false

namespace DaggerAmalgamOriginalResults

noncomputable section

/-- The actual tagged object quotient is covered by its four original endpoint families. -/
theorem ordinary_hom_vertices_nonempty (C B : SimplicialCat.{u, u})
    (x : C.Obj) (b : B.Obj)
    (hC : ∀ a d : C.Obj, Nonempty ((a ⟶[SSet] d) _⦋0⦌))
    (hB : ∀ z w : B.Obj, Nonempty ((z ⟶[SSet] w) _⦋0⦌))
    (s t : Objects C B x b) :
    Nonempty ((SimplicialCat.HomQuotient.hom (relations C B x b) s t) _⦋0⦌) := by
  refine Quot.inductionOn s (fun s ↦ ?_)
  refine Quot.inductionOn t (fun t ↦ ?_)
  cases s with
  | inl a =>
    cases t with
    | inl d => exact ⟨((leftLeg C B x b).map a d).app _ (Classical.choice (hC a d))⟩
    | inr w =>
      exact ⟨SimplicialCat.HomQuotient.mk _ _
        (decodeON C B x b _ a w 0
          ⟨Classical.choice (hC a x), Fin.elim0, Fin.elim0, Classical.choice (hB b w)⟩)⟩
  | inr z =>
    cases t with
    | inl d =>
      exact ⟨SimplicialCat.HomQuotient.mk _ _
        (decodeNO C B x b _ z d 0
          ⟨Classical.choice (hB z b), Fin.elim0, Fin.elim0, Classical.choice (hC x d)⟩)⟩
    | inr w => exact ⟨((rightLeg C B x b).map z w).app _ (Classical.choice (hB z w))⟩

/-- Transport the original vertices through the actual enriched iso and its object equations. -/
theorem hom_vertices_nonempty_of_iso {C D : SimplicialCat.{u, u}} (e : C ≅ D)
    (hC : ∀ a d : C.Obj, Nonempty ((a ⟶[SSet] d) _⦋0⦌))
    (a d : D.Obj) : Nonempty ((a ⟶[SSet] d) _⦋0⦌) := by
  have ha : e.hom.obj (e.inv.obj a) = a :=
    congrArg (fun F : D ⟶ D ↦ F.obj a) e.inv_hom_id
  have hd : e.hom.obj (e.inv.obj d) = d :=
    congrArg (fun F : D ⟶ D ↦ F.obj d) e.inv_hom_id
  have h : Nonempty ((e.hom.obj (e.inv.obj a) ⟶[SSet] e.hom.obj (e.inv.obj d)) _⦋0⦌) :=
    ⟨(e.hom.map (e.inv.obj a) (e.inv.obj d)).app _
      (Classical.choice (hC (e.inv.obj a) (e.inv.obj d)))⟩
  simpa only [ha, hd] using h

/-- Nonempty original Hom vertices at any original dagger-pushout apex. -/
theorem original_hom_vertices_nonempty (C B : DaggerSimplicialCat.{u, u})
    (x : C.Obj) (b : B.Obj) {P : DaggerSimplicialCat.{u, u}}
    (i : C ⟶ P) (j : B ⟶ P)
    (sq : IsPushout (DaggerDiscreteObjects.fromPoint C x)
      (DaggerDiscreteObjects.fromPoint B b) i j)
    (hC : ∀ a d : C.Obj, Nonempty ((a ⟶[SSet] d) _⦋0⦌))
    (hB : ∀ z w : B.Obj, Nonempty ((z ⟶[SSet] w) _⦋0⦌))
    (a d : P.Obj) : Nonempty ((a ⟶[SSet] d) _⦋0⦌) :=
  hom_vertices_nonempty_of_iso
    (DaggerSimplicialCat.forget.mapIso (Dagger.originalIso C B x b i j sq))
    (ordinary_hom_vertices_nonempty C.toSimplicialCat B.toSimplicialCat x b hC hB) a d

end
end DaggerAmalgamOriginalResults
