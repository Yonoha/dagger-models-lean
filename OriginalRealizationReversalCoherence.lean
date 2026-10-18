import OriginalRealizationOppositeComparison
import OriginalSingularReversalCoherence

/-!
# The actual realization reversal squares to the double-op comparison

The proof compares mates under the existing realization/singular adjunction.
The singular-side square is used explicitly; uniqueness of a left adjoint
alone is not treated as an involution law.
-/

set_option autoImplicit false

open CategoryTheory

universe u

namespace DaggerOriginalRealizationReversalCoherence

open DaggerOriginalSingularSetReversal
open DaggerOriginalSingularReversalCoherence
open DaggerOriginalRealizationOppositeComparison

noncomputable section

private abbrev O : SSet.{u} ⥤ SSet.{u} := SSet.opFunctor.{u}
private abbrev R : SSet.{u} ⥤ TopCat.{u} := SSet.toTop.{u}
private abbrev S : TopCat.{u} ⥤ SSet.{u} := TopCat.toSSet.{u}

/-- Transposition through the reversal equivalence, then the actual
singular-set reversal. -/
def singularMate (X : SSet.{u}) (Y : TopCat.{u}) :
    (O.obj X ⟶ S.obj Y) ≃ (X ⟶ S.obj Y) :=
  (SSet.opEquivalence.{u}.toAdjunction.homEquiv X (S.obj Y)).trans
    (Adjunction.equivHomsetRightOfNatIso singularReversal)

/-- The homset equivalence has the literal double-op-unit formula. -/
theorem singularMate_apply (X : SSet.{u}) (Y : TopCat.{u})
    (f : O.obj X ⟶ S.obj Y) :
    singularMate X Y f =
      SSet.opFunctorCompOpFunctorIso.inv.app X ≫ O.map f ≫
        singularReversal.hom.app Y := by
  rfl

/-- Explicit unit of the adjunction obtained by composing reversal with
realization and transporting along singular reversal. -/
theorem opposite_unit_explicit (X : SSet.{u}) :
    oppositeRealizationAdjunctionToSing.unit.app X =
      SSet.opFunctorCompOpFunctorIso.inv.app X ≫
        O.map (sSetTopAdj.unit.app (O.obj X)) ≫
          singularReversal.hom.app (R.obj (O.obj X)) := by
  calc
    oppositeRealizationAdjunctionToSing.unit.app X =
        (oppositeRealizationAdjunctionToSing.homEquiv X
          (R.obj (O.obj X))) (𝟙 _) :=
      (oppositeRealizationAdjunctionToSing.homEquiv_id X).symm
    _ = singularMate X (R.obj (O.obj X))
          ((sSetTopAdj.homEquiv (O.obj X) (R.obj (O.obj X))) (𝟙 _)) := by
      simp only [oppositeRealizationAdjunctionToSing,
        oppositeRealizationAdjunction, singularMate,
        Adjunction.ofNatIsoRight, Adjunction.mkOfHomEquiv_homEquiv,
        Adjunction.comp_homEquiv, Equiv.trans_apply]
      rfl
    _ = singularMate X (R.obj (O.obj X))
          (sSetTopAdj.unit.app (O.obj X)) := by
      rw [sSetTopAdj.homEquiv_id]
    _ = _ := singularMate_apply X (R.obj (O.obj X)) _

/-- The naturality equation identifying the mate of the realization
comparison with the actual singular comparison. -/
theorem realization_mate (X : SSet.{u}) :
    sSetTopAdj.unit.app (O.obj X) ≫
      S.map (realizationOppositeIso.hom.app X) =
        O.map (sSetTopAdj.unit.app X) ≫
          singularReversal.hom.app (R.obj X) := by
  apply (singularMate X (R.obj X)).injective
  have hn := singularReversal.hom.naturality
    (realizationOppositeIso.hom.app X)
  have hn' :
      O.map (S.map (realizationOppositeIso.hom.app X)) ≫
        singularReversal.hom.app (R.obj X) =
          singularReversal.hom.app (R.obj (O.obj X)) ≫
            S.map (realizationOppositeIso.hom.app X) := by
    simpa only [Functor.comp_map] using hn
  have hl :
      singularMate X (R.obj X)
        (sSetTopAdj.unit.app (O.obj X) ≫
          S.map (realizationOppositeIso.hom.app X)) =
        sSetTopAdj.unit.app X := by
    rw [singularMate_apply, O.map_comp]
    calc
      SSet.opFunctorCompOpFunctorIso.inv.app X ≫
          (O.map (sSetTopAdj.unit.app (O.obj X)) ≫
            O.map (S.map (realizationOppositeIso.hom.app X))) ≫
            singularReversal.hom.app (R.obj X) =
          (SSet.opFunctorCompOpFunctorIso.inv.app X ≫
            O.map (sSetTopAdj.unit.app (O.obj X)) ≫
              singularReversal.hom.app (R.obj (O.obj X))) ≫
                S.map (realizationOppositeIso.hom.app X) := by
        simp only [Category.assoc]
        rw [hn']
      _ = oppositeRealizationAdjunctionToSing.unit.app X ≫
            S.map (realizationOppositeIso.hom.app X) := by
        rw [opposite_unit_explicit]
      _ = sSetTopAdj.unit.app X := realizationOppositeIso_unit X
  have hr :
      singularMate X (R.obj X)
        (O.map (sSetTopAdj.unit.app X) ≫
          singularReversal.hom.app (R.obj X)) =
        sSetTopAdj.unit.app X := by
    rw [singularMate_apply, O.map_comp]
    calc
      SSet.opFunctorCompOpFunctorIso.inv.app X ≫
          (O.map (O.map (sSetTopAdj.unit.app X)) ≫
            O.map (singularReversal.hom.app (R.obj X))) ≫
              singularReversal.hom.app (R.obj X) =
          SSet.opFunctorCompOpFunctorIso.inv.app X ≫
            (O.map (O.map (sSetTopAdj.unit.app X)) ≫
              SSet.opFunctorCompOpFunctorIso.hom.app (S.obj (R.obj X))) := by
        rw [← singularReversal_square (R.obj X)]
        simp only [Category.assoc]
      _ = SSet.opFunctorCompOpFunctorIso.inv.app X ≫
            (SSet.opFunctorCompOpFunctorIso.hom.app X ≫
              sSetTopAdj.unit.app X) := by
        simpa only [Category.assoc, Functor.comp_map, Functor.id_map] using
          congrArg (fun k ↦ SSet.opFunctorCompOpFunctorIso.inv.app X ≫ k)
            (SSet.opFunctorCompOpFunctorIso.hom.naturality
              (sSetTopAdj.unit.app X))
      _ = sSetTopAdj.unit.app X := by
        rw [← Category.assoc,
          SSet.opFunctorCompOpFunctorIso.inv_hom_id_app, Category.id_comp]
  exact hl.trans hr.symm

/-- Twice applying the actual realization comparison agrees with realization
of Mathlib's double-op isomorphism. -/
theorem realizationOppositeIso_square (X : SSet.{u}) :
    realizationOppositeIso.hom.app (O.obj X) ≫
      realizationOppositeIso.hom.app X =
        R.map (SSet.opFunctorCompOpFunctorIso.hom.app X) := by
  apply (sSetTopAdj.homEquiv (O.obj (O.obj X)) (R.obj X)).injective
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp]
  have hn := singularReversal.hom.naturality
    (realizationOppositeIso.hom.app X)
  have hn' :
      singularReversal.hom.app (R.obj (O.obj X)) ≫
        S.map (realizationOppositeIso.hom.app X) =
          O.map (S.map (realizationOppositeIso.hom.app X)) ≫
            singularReversal.hom.app (R.obj X) := by
    simpa only [Functor.comp_map] using hn.symm
  calc
    sSetTopAdj.unit.app (O.obj (O.obj X)) ≫
        (S.map (realizationOppositeIso.hom.app (O.obj X)) ≫
          S.map (realizationOppositeIso.hom.app X)) =
      (O.map (sSetTopAdj.unit.app (O.obj X)) ≫
        singularReversal.hom.app (R.obj (O.obj X))) ≫
          S.map (realizationOppositeIso.hom.app X) := by
      simpa only [Category.assoc] using
        congrArg (fun k ↦ k ≫ S.map (realizationOppositeIso.hom.app X))
          (realization_mate (O.obj X))
    _ = O.map (sSetTopAdj.unit.app (O.obj X)) ≫
          (O.map (S.map (realizationOppositeIso.hom.app X)) ≫
            singularReversal.hom.app (R.obj X)) := by
      simp only [Category.assoc]
      rw [hn']
    _ = O.map (O.map (sSetTopAdj.unit.app X)) ≫
          (O.map (singularReversal.hom.app (R.obj X)) ≫
            singularReversal.hom.app (R.obj X)) := by
      simpa only [O.map_comp, Category.assoc] using
        congrArg (fun k ↦ O.map k ≫ singularReversal.hom.app (R.obj X))
          (realization_mate X)
    _ = O.map (O.map (sSetTopAdj.unit.app X)) ≫
          SSet.opFunctorCompOpFunctorIso.hom.app (S.obj (R.obj X)) := by
      rw [singularReversal_square (R.obj X)]
    _ = SSet.opFunctorCompOpFunctorIso.hom.app X ≫
          sSetTopAdj.unit.app X := by
      simpa only [Functor.comp_map, Functor.id_map] using
        SSet.opFunctorCompOpFunctorIso.hom.naturality
          (sSetTopAdj.unit.app X)
    _ = sSetTopAdj.unit.app (O.obj (O.obj X)) ≫
          S.map (R.map (SSet.opFunctorCompOpFunctorIso.hom.app X)) := by
      simpa only [Functor.comp_map, Functor.id_map] using
        sSetTopAdj.unit.naturality
          (SSet.opFunctorCompOpFunctorIso.hom.app X)

end

end DaggerOriginalRealizationReversalCoherence
