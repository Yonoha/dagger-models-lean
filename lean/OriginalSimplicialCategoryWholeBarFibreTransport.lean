import OriginalSimplicialCategoryWholeHomTransportWeakEquivalence

/-!
# Original vertex transport on the actual entire strict bar fibres

Conjugate the original entire Hom transport by the proved original Hom-fibre
isomorphisms. Every original endpoint component remains present. This is the
actual strict-fibre transport specified by original Hom precomposition; no
homotopy-fibre identification or realization quasifibration is assumed.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Simplicial DaggerModels
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
open DaggerOriginalSimplicialPiZeroCategory
open DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerOriginalSimplicialCategoryWholeBarFibreDegree
open DaggerOriginalSimplicialCategoryWholeBarFibreIso
open DaggerOriginalSimplicialCategoryWholeHomTransport
open DaggerOriginalSimplicialCategoryWholeHomTransportWeakEquivalence
universe u
namespace DaggerOriginalSimplicialCategoryWholeBarFibreTransport
noncomputable section

/-- Original precomposition specifies the transport between the actual whole strict fibres. -/
def wholeBarFibreTransport (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    (wholeBarFibre C y).toSSet ⟶ (wholeBarFibre C x).toSSet :=
  (wholeBarHomFibreIso C y).inv ≫ wholeHomPrecompose C a ≫ (wholeBarHomFibreIso C x).hom

/-- The entire strict-fibre transport retains precisely the original whole Hom transport. -/
theorem wholeBarFibreTransport_hom (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    (wholeBarHomFibreIso C y).hom ≫ wholeBarFibreTransport C a =
      wholeHomPrecompose C a ≫ (wholeBarHomFibreIso C x).hom := by
  simp only [wholeBarFibreTransport, Iso.hom_inv_id_assoc]

/-- Original component invertibility makes the entire original strict-fibre transport weak. -/
theorem wholeBarFibreTransport_weakEquivalence (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌))
    (ha : @IsIso (componentObjects C) (componentCategory C) x y (SSet.π₀.mk a)) :
    WeakEquivalence (wholeBarFibreTransport C a) := by
  have : WeakEquivalence (wholeHomPrecompose C a) := wholeHomPrecompose_weakEquivalence C a ha
  dsimp [wholeBarFibreTransport]
  infer_instance

/-- The exact original pi0 groupoid makes all whole original Hom-sum transports weak. -/
theorem wholeHomPrecompose_weakEquivalence_of_actualGroupoid (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    WeakEquivalence (wholeHomPrecompose C a) := by
  obtain ⟨G, hG⟩ := hC
  have hi : ∀ {r s : componentObjects C} (f : r ⟶ s), IsIso f := by
    rw [← hG]
    intro r s f
    let g : Groupoid.{u, u} (componentObjects C) := G
    infer_instance
  exact wholeHomPrecompose_weakEquivalence C a (hi (r := x) (s := y) (SSet.π₀.mk a))

/-- The exact original pi0 groupoid makes all actual whole strict-fibre transports weak. -/
theorem wholeBarFibreTransport_weakEquivalence_of_actualGroupoid (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    WeakEquivalence (wholeBarFibreTransport C a) := by
  have : WeakEquivalence (wholeHomPrecompose C a) :=
    wholeHomPrecompose_weakEquivalence_of_actualGroupoid C hC a
  dsimp [wholeBarFibreTransport]
  infer_instance

end
end DaggerOriginalSimplicialCategoryWholeBarFibreTransport
