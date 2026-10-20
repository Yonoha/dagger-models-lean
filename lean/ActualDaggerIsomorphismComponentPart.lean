import ActualSimplicialIsomorphismComponentMaps
import NativeSimplicialComponentDagger
import NativeDaggerEnrichedHomRestriction

/-! The ALL-isomorphism-component part inherits precisely the original dagger. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialPiZeroCategory DaggerActualConstantSimplicialCategory
open DaggerActualPiZeroConstantHomEquivalence DaggerActualSimplicialIsomorphismComponentPart
open DaggerNativeSimplicialComponentDagger
universe u
namespace DaggerActualDaggerIsomorphismComponentPart
noncomputable section

local instance (C : SimplicialCat.{u, u}) :
    EnrichedCategory SSet.{u} (constant (componentObjects C)).Obj :=
  (constant (componentObjects C)).enriched

theorem dagger_projection (D : DaggerSimplicialCat.{u, u})
    (x y : componentObjects D.toSimplicialCat) :
    D.daggerStructure.dagger x y ≫ (projection D.toSimplicialCat).map y x =
      (projection D.toSimplicialCat).map x y ≫ DaggerUnitaryDiscrete.constMap
        (fun a : x ⟶ y ↦ SSet.mapπ₀ (D.daggerStructure.dagger x y) a) := by
  apply constant_ext
  intro v
  change ((projection D.toSimplicialCat).map y x).app (op ⦋0⦌)
      ((D.daggerStructure.dagger x y).app (op ⦋0⦌) v) =
    SSet.mapπ₀ (D.daggerStructure.dagger x y)
      (((projection D.toSimplicialCat).map x y).app (op ⦋0⦌) v)
  rw [projection_vertex, projection_vertex]
  rfl

theorem dagger_projection_apply (D : DaggerSimplicialCat.{u, u})
    (x y : componentObjects D.toSimplicialCat) (q : SimplexCategoryᵒᵖ)
    (s : (D.enriched.Hom x y).obj q) :
    ((projection D.toSimplicialCat).map y x).app q
        ((D.daggerStructure.dagger x y).app q s) =
      SSet.mapπ₀ (D.daggerStructure.dagger x y)
        (((projection D.toSimplicialCat).map x y).app q s) :=
  congrFun (NatTrans.congr_app (dagger_projection D x y) q) s

theorem dagger_mem (D : DaggerSimplicialCat.{u, u}) (x y : D.Obj)
    (q : SimplexCategoryᵒᵖ) (s : (homSubcomplex D.toSimplicialCat x y : SSet.{u}).obj q) :
    (D.daggerStructure.dagger x y).app q s.val ∈
      (homSubcomplex D.toSimplicialCat y x).obj q := by
  change IsIso (((projection D.toSimplicialCat).map y x).app q
    ((D.daggerStructure.dagger x y).app q s.val))
  rw [dagger_projection_apply]
  letI := componentDagger D
  have : IsIso (((projection D.toSimplicialCat).map x y).app q s.val) := s.property
  exact dagger_isIso (((projection D.toSimplicialCat).map x y).app q s.val)

def part (D : DaggerSimplicialCat.{u, u}) : DaggerSimplicialCat.{u, u} :=
  DaggerNativeDaggerEnrichedHomRestriction.restricted D (homSubcomplex D.toSimplicialCat)
    (id_mem D.toSimplicialCat) (comp_mem D.toSimplicialCat) (dagger_mem D)

def inclusion (D : DaggerSimplicialCat.{u, u}) : part D ⟶ D :=
  DaggerNativeDaggerEnrichedHomRestriction.inclusion D (homSubcomplex D.toSimplicialCat)
    (id_mem D.toSimplicialCat) (comp_mem D.toSimplicialCat) (dagger_mem D)

theorem part_underlying (D : DaggerSimplicialCat.{u, u}) :
    (part D).toSimplicialCat = DaggerActualSimplicialIsomorphismComponentPart.part
      D.toSimplicialCat :=
  rfl

theorem inclusion_map (D : DaggerSimplicialCat.{u, u}) (x y : D.Obj) :
    (inclusion D).map x y = (homSubcomplex D.toSimplicialCat x y).ι :=
  rfl

end
end DaggerActualDaggerIsomorphismComponentPart
