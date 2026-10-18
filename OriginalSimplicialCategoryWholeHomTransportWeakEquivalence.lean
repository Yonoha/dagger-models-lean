import OriginalSimplicialCategoryWholeHomTransport

/-!
# Invertible original components act weakly on the entire original Hom coproduct

Use the actual original whole endpoint-preserving transport homotopies.
Represent the inverse component by an original vertex and construct the
homotopy equivalence after realization and singular on the entire sums.
No preservation of coproducts by singular or unproved stability of weak
equivalences under coproducts is assumed.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels HomotopicalAlgebra
open DaggerOriginalSimplicialPiZeroCategory
open DaggerOriginalSimplicialCategoryVertexComposition
open DaggerOriginalSimplicialCategoryWholeHomTransport
open DaggerOriginalSimplicialCategoryWholeBarFibreIso
universe u
namespace DaggerOriginalSimplicialCategoryWholeHomTransportWeakEquivalence
noncomputable section

/-- Original inverse components give a whole Hom-sum equivalence after realization. -/
def wholeHomPrecomposeHomotopyEquiv (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌))
    (b : (C.enriched.Hom y x).obj (op ⦋0⦌))
    (hab : SSet.π₀.mk ((C.enriched.comp x y x).app (op ⦋0⦌) (a, b)) =
      SSet.π₀.mk ((C.enriched.id x).app (op ⦋0⦌) PUnit.unit))
    (hba : SSet.π₀.mk ((C.enriched.comp y x y).app (op ⦋0⦌) (b, a)) =
      SSet.π₀.mk ((C.enriched.id y).app (op ⦋0⦌) PUnit.unit)) :
    (DaggerNerveHomotopy.R.obj (originalHomSum C y)).HomotopyEquiv
      (DaggerNerveHomotopy.R.obj (originalHomSum C x)) where
  hom := DaggerNerveHomotopy.R.map (wholeHomPrecompose C a)
  inv := DaggerNerveHomotopy.R.map (wholeHomPrecompose C b)
  homInvId := by
    let h := Classical.choice (wholeHomPrecompose_componentHomotopy C
      ((C.enriched.comp y x y).app (op ⦋0⦌) (b, a))
      ((C.enriched.id y).app (op ⦋0⦌) PUnit.unit) hba)
    refine SSet.Homotopy.congr h ?_ ?_
    · rw [← DaggerNerveHomotopy.R.map_comp, wholeHomPrecompose_comp]
    · rw [wholeHomPrecompose_id, DaggerNerveHomotopy.R.map_id]
  invHomId := by
    let h := Classical.choice (wholeHomPrecompose_componentHomotopy C
      ((C.enriched.comp x y x).app (op ⦋0⦌) (a, b))
      ((C.enriched.id x).app (op ⦋0⦌) PUnit.unit) hab)
    refine SSet.Homotopy.congr h ?_ ?_
    · rw [← DaggerNerveHomotopy.R.map_comp, wholeHomPrecompose_comp]
    · rw [wholeHomPrecompose_id, DaggerNerveHomotopy.R.map_id]

/-- Actual original inverse vertex components make the entire Hom transport weak. -/
theorem wholeHomPrecompose_weakEquivalence_of_inverse (C : SimplicialCat.{u, u})
    {x y : C.Obj} (a : (C.enriched.Hom x y).obj (op ⦋0⦌))
    (b : (C.enriched.Hom y x).obj (op ⦋0⦌))
    (hab : SSet.π₀.mk ((C.enriched.comp x y x).app (op ⦋0⦌) (a, b)) =
      SSet.π₀.mk ((C.enriched.id x).app (op ⦋0⦌) PUnit.unit))
    (hba : SSet.π₀.mk ((C.enriched.comp y x y).app (op ⦋0⦌) (b, a)) =
      SSet.π₀.mk ((C.enriched.id y).app (op ⦋0⦌) PUnit.unit)) :
    WeakEquivalence (wholeHomPrecompose C a) := by
  apply (SSet.modelCategoryQuillen.weakEquivalence_iff _).mpr
  apply (TopCat.modelCategory.weakEquivalence_iff _).mpr
  exact SSet.KanComplex.W.homotopyEquivHom (wholeHomPrecomposeHomotopyEquiv C a b hab hba)

/-- Actual component invertibility implies weak transport of the entire original Hom sum. -/
theorem wholeHomPrecompose_weakEquivalence (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌))
    (ha : @IsIso (componentObjects C) (componentCategory C) x y (SSet.π₀.mk a))
    : WeakEquivalence (wholeHomPrecompose C a) := by
  let ca : @Quiver.Hom (componentObjects C) inferInstance x y := SSet.π₀.mk a
  have : @IsIso (componentObjects C) (componentCategory C) x y ca := ha
  obtain ⟨b, hb⟩ := SSet.π₀.mk_surjective (inv ca)
  apply wholeHomPrecompose_weakEquivalence_of_inverse C a b
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
end DaggerOriginalSimplicialCategoryWholeHomTransportWeakEquivalence
