import NativeConstantSourceMappingRow

/-! Identify the SAME original ordinary nerve row by the native lifted ordinal equivalence. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerNativeConstantSourceMappingRow
universe u
namespace DaggerNativeOrdinaryNerveRowIso
noncomputable section

/-- Use the native order equivalence and its existing categorical equivalence. -/
def ordinalOrderIso (n : SimplexCategory) : ULift.{u} (Fin (n.len + 1)) ≃o Fin (n.len + 1) where
  toEquiv := Equiv.ulift
  map_rel_iff' := Iff.rfl

def ordinalEquivalence (n : SimplexCategory) :
    ULift.{u} (Fin (n.len + 1)) ≌ Fin (n.len + 1) := (ordinalOrderIso.{u} n).equivalence

/-- The native equivalence retains the entire original finite-ordinal functor. -/
theorem inverse_functor (n : SimplexCategory) :
    (ordinalEquivalence.{u} n).inverse ⋙ (ordinalEquivalence.{u} n).functor =
      𝟭 (Fin (n.len + 1)) := CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The other composite retains every lifted original vertex. -/
theorem functor_inverse (n : SimplexCategory) :
    (ordinalEquivalence.{u} n).functor ⋙ (ordinalEquivalence.{u} n).inverse =
      𝟭 (ULift.{u} (Fin (n.len + 1))) := CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The SAME original bisimplicial nerve, with its indices interchanged. -/
abbrev nerveRow (C : SimplicialCat.{u, u}) (n : SimplexCategory) : SSet.{u} :=
  (bisimplicialNerveFunctor.obj C).flip.obj (op n)

/-- Lift a whole original chain, preserving all target objects including repeated labels. -/
def toLifted (C : SimplicialCat.{u, u}) (n : SimplexCategory) :
    nerveRow C n ⟶ ordinaryRow (ULift.{u} (Fin (n.len + 1))) C where
  app _ p := ⟨(ordinalEquivalence.{u} n).functor ⋙ p⟩
  naturality _ _ a := by
    funext p
    apply ULift.ext
    exact (CategoryTheory.Functor.assoc (ordinalEquivalence.{u} n).functor p (degreeMap C a)).symm

/-- Restrict the SAME lifted chain to the actual original Fin-domain nerve. -/
def fromLifted (C : SimplicialCat.{u, u}) (n : SimplexCategory) :
    ordinaryRow (ULift.{u} (Fin (n.len + 1))) C ⟶ nerveRow C n where
  app _ p := (ordinalEquivalence.{u} n).inverse ⋙ p.down
  naturality _ _ a := by
    funext p
    exact (CategoryTheory.Functor.assoc (ordinalEquivalence.{u} n).inverse p.down
      (degreeMap C a)).symm

/-- An actual SSet isomorphism using both entire original chain identities. -/
def rowIso (C : SimplicialCat.{u, u}) (n : SimplexCategory) :
    nerveRow C n ≅ ordinaryRow (ULift.{u} (Fin (n.len + 1))) C where
  hom := toLifted C n
  inv := fromLifted C n
  hom_inv_id := by
    apply NatTrans.ext
    funext q p
    change (ordinalEquivalence.{u} n).inverse ⋙ ((ordinalEquivalence.{u} n).functor ⋙ p) = p
    rw [← CategoryTheory.Functor.assoc, inverse_functor, CategoryTheory.Functor.id_comp]
  inv_hom_id := by
    apply NatTrans.ext
    funext q p
    apply ULift.ext
    change (ordinalEquivalence.{u} n).functor ⋙
      ((ordinalEquivalence.{u} n).inverse ⋙ p.down) = p.down
    rw [← CategoryTheory.Functor.assoc, functor_inverse, CategoryTheory.Functor.id_comp]

end
end DaggerNativeOrdinaryNerveRowIso
