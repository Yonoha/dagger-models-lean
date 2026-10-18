import OriginalSimplicialCategoryVertexComponentHomotopy

/-!
# Actual original Hom transport is weak when its vertex component is invertible

An actual inverse component is represented by an original vertex. Its two
original composites have the original identity components. The proved
component homotopies yield an actual homotopy equivalence after realization
and singular, hence weak equivalence of the whole original precomposition map.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels HomotopicalAlgebra
open DaggerOriginalSimplicialPiZeroCategory
open DaggerOriginalSimplicialCategoryVertexComposition
open DaggerOriginalSimplicialCategoryVertexComponentHomotopy
universe u
namespace DaggerOriginalSimplicialCategoryVertexTransportWeakEquivalence
noncomputable section

/-- Original inverse components give a Hom transport homotopy equivalence after realization. -/
def precomposeVertexHomotopyEquiv (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌))
    (b : (C.enriched.Hom y x).obj (op ⦋0⦌))
    (hab : SSet.π₀.mk ((C.enriched.comp x y x).app (op ⦋0⦌) (a, b)) =
      SSet.π₀.mk ((C.enriched.id x).app (op ⦋0⦌) PUnit.unit))
    (hba : SSet.π₀.mk ((C.enriched.comp y x y).app (op ⦋0⦌) (b, a)) =
      SSet.π₀.mk ((C.enriched.id y).app (op ⦋0⦌) PUnit.unit)) (z : C.Obj) :
    (DaggerNerveHomotopy.R.obj (C.enriched.Hom y z)).HomotopyEquiv
      (DaggerNerveHomotopy.R.obj (C.enriched.Hom x z)) where
  hom := DaggerNerveHomotopy.R.map (precomposeVertex C a z)
  inv := DaggerNerveHomotopy.R.map (precomposeVertex C b z)
  homInvId := by
    let h := Classical.choice (precomposeVertex_componentHomotopy C
      ((C.enriched.comp y x y).app (op ⦋0⦌) (b, a))
      ((C.enriched.id y).app (op ⦋0⦌) PUnit.unit) hba z)
    refine SSet.Homotopy.congr h ?_ ?_
    · rw [← DaggerNerveHomotopy.R.map_comp, precomposeVertex_comp]
    · rw [precomposeVertex_id, DaggerNerveHomotopy.R.map_id]
  invHomId := by
    let h := Classical.choice (precomposeVertex_componentHomotopy C
      ((C.enriched.comp x y x).app (op ⦋0⦌) (a, b))
      ((C.enriched.id x).app (op ⦋0⦌) PUnit.unit) hab z)
    refine SSet.Homotopy.congr h ?_ ?_
    · rw [← DaggerNerveHomotopy.R.map_comp, precomposeVertex_comp]
    · rw [precomposeVertex_id, DaggerNerveHomotopy.R.map_id]

/-- Actual original inverse vertex components imply weak equivalence of full Hom transport. -/
theorem precomposeVertex_weakEquivalence_of_inverse (C : SimplicialCat.{u, u})
    {x y : C.Obj} (a : (C.enriched.Hom x y).obj (op ⦋0⦌))
    (b : (C.enriched.Hom y x).obj (op ⦋0⦌))
    (hab : SSet.π₀.mk ((C.enriched.comp x y x).app (op ⦋0⦌) (a, b)) =
      SSet.π₀.mk ((C.enriched.id x).app (op ⦋0⦌) PUnit.unit))
    (hba : SSet.π₀.mk ((C.enriched.comp y x y).app (op ⦋0⦌) (b, a)) =
      SSet.π₀.mk ((C.enriched.id y).app (op ⦋0⦌) PUnit.unit)) (z : C.Obj) :
    WeakEquivalence (precomposeVertex C a z) := by
  apply (SSet.modelCategoryQuillen.weakEquivalence_iff _).mpr
  apply (TopCat.modelCategory.weakEquivalence_iff _).mpr
  exact SSet.KanComplex.W.homotopyEquivHom (precomposeVertexHomotopyEquiv C a b hab hba z)

/-- Invertibility in the actual original component category implies weak Hom transport. -/
theorem precomposeVertex_weakEquivalence (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌))
    (ha : @IsIso (componentObjects C) (componentCategory C) x y (SSet.π₀.mk a))
    (z : C.Obj) : WeakEquivalence (precomposeVertex C a z) := by
  let ca : @Quiver.Hom (componentObjects C) inferInstance x y := SSet.π₀.mk a
  have : @IsIso (componentObjects C) (componentCategory C) x y ca := ha
  obtain ⟨b, hb⟩ := SSet.π₀.mk_surjective (inv ca)
  apply precomposeVertex_weakEquivalence_of_inverse C a b
  · change @CategoryStruct.comp (componentObjects C) (componentCategory C).toCategoryStruct
      x y x ca (SSet.π₀.mk b) =
      @CategoryStruct.id (componentObjects C) (componentCategory C).toCategoryStruct x
    rw [hb]
    exact IsIso.hom_inv_id ca
  · change @CategoryStruct.comp (componentObjects C) (componentCategory C).toCategoryStruct
      y x y (SSet.π₀.mk b) ca =
      @CategoryStruct.id (componentObjects C) (componentCategory C).toCategoryStruct y
    rw [hb]
    exact IsIso.inv_hom_id ca

end
end DaggerOriginalSimplicialCategoryVertexTransportWeakEquivalence
