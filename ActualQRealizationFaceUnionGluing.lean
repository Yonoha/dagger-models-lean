import OriginalCounitRightConeQRealizationCofibrationsReconciled
import ActualQRealizationRepresentableWeakness
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-! Weak collapses for realized nonempty faces and their actual subcomplex pushouts. -/

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra
open Simplicial
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerOriginalCounitRightConeQRealizationCofibrations
open DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualQRealizationFaceUnionGluing

noncomputable section

/-- A map between two objects with weak terminal collapses is geometrically weak. -/
theorem map_GW_of_collapses {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : GW (toUnit X)) (hY : GW (toUnit Y)) : GW f := by
  letI : WeakEquivalence (toUnit X) := (weakEquivalence_iff_GW _).2 hX
  letI : WeakEquivalence (toUnit Y) := (weakEquivalence_iff_GW _).2 hY
  exact (weakEquivalence_iff_GW _).1
    (weakEquivalence_of_postcomp_of_fac (isTerminalTensorUnit.hom_ext (f ≫ toUnit Y)
      (toUnit X)))

/-- A weak map from a weakly contractible object gives a weak terminal collapse. -/
theorem collapse_GW_of_weak_map {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : GW f) (hX : GW (toUnit X)) : GW (toUnit Y) := by
  letI : WeakEquivalence f := (weakEquivalence_iff_GW _).2 hf
  letI : WeakEquivalence (toUnit X) := (weakEquivalence_iff_GW _).2 hX
  exact (weakEquivalence_iff_GW _).1
    (weakEquivalence_of_precomp_of_fac (isTerminalTensorUnit.hom_ext (f ≫ toUnit Y)
      (toUnit X)))

/-- Every nonempty literal face is representable, hence has weakly contractible Q-realization. -/
theorem face_toUnit_GW {n : ℕ} (S : Finset (Fin (n + 1))) (hS : S.Nonempty) :
    GW (toUnit (realization.{u}.obj (SSet.stdSimplex.face S : SSet.{u}))) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hS.card_ne_zero
  let e : Fin (m + 1) ≃o S := Finset.orderIsoOfFin S hm
  let f := realization.{u}.mapIso
    (SSet.stdSimplex.isoOfRepresentableBy (SSet.stdSimplex.faceRepresentableBy S m e))
  exact collapse_GW_of_weak_map f.hom
    ((weakEquivalence_iff_GW _).1 (inferInstance : WeakEquivalence f.hom))
    (DaggerActualQRealizationRepresentableWeakness.representable_toUnit_GW ⦋m⦌)

/-- The native union pushout preserves weak contractibility after the actual realization. -/
theorem sup_toUnit_GW {X : SSet.{u}} (U V : X.Subcomplex)
    (hI : GW (toUnit (realization.obj (U ⊓ V).toSSet)))
    (hU : GW (toUnit (realization.obj (U : SSet.{u}))))
    (hV : GW (toUnit (realization.obj (V : SSet.{u})))) :
    GW (toUnit (realization.obj (U ⊔ V).toSSet)) := by
  let sq : (U ⊓ V).BicartSq U V (U ⊔ V) := ⟨rfl, rfl⟩
  let f : (U ⊓ V).toSSet ⟶ (U : SSet.{u}) :=
    SSet.Subcomplex.homOfLE inf_le_left
  let j : (V : SSet.{u}) ⟶ (U ⊔ V).toSSet :=
    SSet.Subcomplex.homOfLE le_sup_right
  have hf : GW (realization.map f) := map_GW_of_collapses _ hI hU
  letI : Cofibration f := SSet.modelCategoryQuillen.cofibration_of_mono _
  letI : WeakEquivalence (realization.map f) := (weakEquivalence_iff_GW _).2 hf
  have ht : trivialCofibrations SSet.{u} (realization.map f) := mem_trivialCofibrations _
  have hj : trivialCofibrations SSet.{u} (realization.map j) :=
    MorphismProperty.of_isPushout (sq.isPushout.flip.map realization) ht
  rw [mem_trivialCofibrations_iff] at hj
  exact collapse_GW_of_weak_map (realization.map j)
    ((weakEquivalence_iff_GW _).1 hj.2) hV

end
end DaggerActualQRealizationFaceUnionGluing
