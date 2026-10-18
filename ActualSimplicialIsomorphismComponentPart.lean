import NativeEnrichedHomSubcomplexRestriction
import ActualPiZeroConstantAdjunction

/-! Select precisely the original Hom components whose arrows are isomorphisms in pi-zero. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialPiZeroCategory DaggerActualConstantSimplicialCategory
open DaggerActualPiZeroConstantHomEquivalence
universe u
namespace DaggerActualSimplicialIsomorphismComponentPart
noncomputable section

local instance (C : SimplicialCat.{u, u}) :
    EnrichedCategory SSet.{u} (constant (componentObjects C)).Obj :=
  (constant (componentObjects C)).enriched

def projection (C : SimplicialCat.{u, u}) : C ⟶ constant (componentObjects C) :=
  fromOrdinary C (componentObjects C) (𝟭 (componentObjects C))

theorem projection_vertex (C : SimplicialCat.{u, u}) (x y : componentObjects C)
    (v : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    ((projection C).map x y).app (op ⦋0⦌) v =
      (SSet.π₀.mk v : (x : componentObjects C) ⟶ (y : componentObjects C)) :=
  constant_symm_mk (fun a ↦ a) v

def homSubcomplex (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    (C.enriched.Hom x y).Subcomplex where
  obj q := {s | IsIso (((projection C).map x y).app q s)}
  map f s hs := by
    have ht := congrFun (((projection C).map x y).naturality f) s
    change ((projection C).map x y).app _ ((C.enriched.Hom x y).map f s) =
      ((projection C).map x y).app _ s at ht
    change IsIso (((projection C).map x y).app _ ((C.enriched.Hom x y).map f s))
    rw [ht]
    exact hs

theorem id_mem (C : SimplicialCat.{u, u}) (x : C.Obj) (q : SimplexCategoryᵒᵖ)
    (s : (𝟙_ SSet.{u}).obj q) :
    (C.enriched.id x).app q s ∈ (homSubcomplex C x x).obj q := by
  change IsIso (((projection C).map x x).app q ((C.enriched.id x).app q s))
  have ht := congrFun (NatTrans.congr_app ((projection C).map_id x) q) s
  change ((projection C).map x x).app q ((C.enriched.id x).app q s) =
    𝟙 ((projection C).obj x) at ht
  rw [ht]
  infer_instance

theorem comp_mem (C : SimplicialCat.{u, u}) (x y z : C.Obj) (q : SimplexCategoryᵒᵖ)
    (s : (homSubcomplex C x y : SSet.{u}).obj q)
    (t : (homSubcomplex C y z : SSet.{u}).obj q) :
    (C.enriched.comp x y z).app q (s.val, t.val) ∈ (homSubcomplex C x z).obj q := by
  change IsIso (((projection C).map x z).app q
    ((C.enriched.comp x y z).app q (s.val, t.val)))
  have ht := congrFun (NatTrans.congr_app ((projection C).map_comp x y z) q) (s.val, t.val)
  change ((projection C).map x z).app q ((C.enriched.comp x y z).app q (s.val, t.val)) =
    ((projection C).map x y).app q s.val ≫ ((projection C).map y z).app q t.val at ht
  rw [ht]
  have : IsIso (((projection C).map x y).app q s.val) := s.property
  have : IsIso (((projection C).map y z).app q t.val) := t.property
  infer_instance

def part (C : SimplicialCat.{u, u}) : SimplicialCat.{u, u} :=
  DaggerNativeEnrichedHomSubcomplexRestriction.restricted C (homSubcomplex C)
    (id_mem C) (comp_mem C)

def inclusion (C : SimplicialCat.{u, u}) : part C ⟶ C :=
  DaggerNativeEnrichedHomSubcomplexRestriction.inclusion C (homSubcomplex C)
    (id_mem C) (comp_mem C)

theorem hom_vertex_iff (C : SimplicialCat.{u, u}) (x y : componentObjects C)
    (v : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    v ∈ (homSubcomplex C x y).obj (op ⦋0⦌) ↔
      IsIso (C := componentObjects C) (X := x) (Y := y) (SSet.π₀.mk v) := by
  change IsIso (((projection C).map x y).app (op ⦋0⦌) v) ↔ _
  rw [projection_vertex]

theorem inclusion_map (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    (inclusion C).map x y = (homSubcomplex C x y).ι :=
  rfl

end
end DaggerActualSimplicialIsomorphismComponentPart
