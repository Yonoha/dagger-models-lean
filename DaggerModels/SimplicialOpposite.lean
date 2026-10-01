import DaggerModels.DaggerSimplicialCategory

/-!
Part I `bg.lem.creation`.
This constructs the actual object and ordinary opposite functors on simplicial categories.
It does not assert that either limits or colimits are created by dagger forgetting.
-/

open CategoryTheory MonoidalCategory BraidedCategory Opposite

universe o v

noncomputable section

namespace DaggerModels
namespace SimplicialCat

/-- The actual object type of a simplicial category, with arbitrary object maps. -/
def objects : SimplicialCat.{o, v} ⥤ Type o where
  obj C := C.Obj
  map F := F.obj

/-- The ordinary opposite enrichment uses the same simplicial sets and operators. -/
def opposite (C : SimplicialCat.{o, v}) : SimplicialCat.{o, v} :=
  of C.Objᵒᵖ

/-- Reverse the endpoints of every hom map; no simplex operator is reversed. -/
def oppositeMap {C D : SimplicialCat.{o, v}} (F : C ⟶ D) : opposite C ⟶ opposite D where
  obj X := op (F.obj X.unop)
  map X Y := F.map Y.unop X.unop
  map_id X := F.map_id X.unop
  map_comp X Y Z := by
    change (β_ _ _).hom ≫ eComp SSet Z.unop Y.unop X.unop ≫
      F.map Z.unop X.unop = _
    rw [F.map_comp, ← braiding_naturality_assoc]
    rfl

/-- Ordinary opposite is a covariant endofunctor of the category of simplicial categories. -/
def oppositeFunctor : SimplicialCat.{o, v} ⥤ SimplicialCat.{o, v} where
  obj := opposite
  map := oppositeMap
  map_id C := by
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [oppositeMap]
  map_comp F G := by
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [oppositeMap]

@[simp]
theorem oppositeFunctor_obj (C : SimplicialCat.{o, v}) :
    oppositeFunctor.obj C = opposite C := rfl

@[simp]
theorem oppositeMap_map {C D : SimplicialCat.{o, v}} (F : C ⟶ D)
    (X Y : (opposite C).Obj) : (oppositeMap F).map X Y = F.map Y.unop X.unop := rfl

/-- Removing two object wrappers is an actual enriched functor. -/
def doubleOppositeHom (C : SimplicialCat.{o, v}) : opposite (opposite C) ⟶ C where
  obj X := X.unop.unop
  map _ _ := 𝟙 _
  map_id X := by
    change eId SSet X.unop.unop ≫ 𝟙 _ = eId SSet X.unop.unop
    simp
  map_comp X Y Z := by
    change ((β_ _ _).hom ≫ (β_ _ _).hom ≫
      eComp SSet X.unop.unop Y.unop.unop Z.unop.unop) ≫ 𝟙 _ = _
    ext n p
    simp only [SSet.comp_app]
    rfl

/-- Inserting two object wrappers is the inverse enriched functor. -/
def doubleOppositeInv (C : SimplicialCat.{o, v}) : C ⟶ opposite (opposite C) where
  obj X := op (op X)
  map _ _ := 𝟙 _
  map_id X := by
    change eId SSet X ≫ 𝟙 _ = eId SSet X
    simp
  map_comp X Y Z := by
    change eComp SSet X Y Z ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫
      (β_ _ _).hom ≫ (β_ _ _).hom ≫ eComp SSet X Y Z
    ext n p
    simp only [SSet.comp_app]
    rfl

/-- Double opposite is isomorphic to the original actual simplicial category. -/
def doubleOppositeIso (C : SimplicialCat.{o, v}) : opposite (opposite C) ≅ C where
  hom := doubleOppositeHom C
  inv := doubleOppositeInv C
  hom_inv_id := by
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [doubleOppositeHom, doubleOppositeInv]
  inv_hom_id := by
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [doubleOppositeHom, doubleOppositeInv]

/-- The involution is natural for arbitrary enriched functors and arbitrary object maps. -/
def doubleOppositeNatIso : oppositeFunctor ⋙ oppositeFunctor ≅
    𝟭 (SimplicialCat.{o, v}) :=
  NatIso.ofComponents doubleOppositeIso (by
    intro C D F
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [doubleOppositeIso, doubleOppositeHom, oppositeFunctor, oppositeMap])

/-- The actual opposite involution satisfies its triangle identity. -/
theorem opposite_triangle (C : SimplicialCat.{o, v}) :
    oppositeFunctor.map (doubleOppositeNatIso.inv.app C) ≫
      doubleOppositeNatIso.hom.app (oppositeFunctor.obj C) =
      𝟙 (oppositeFunctor.obj C) := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  simp [doubleOppositeNatIso, doubleOppositeIso, doubleOppositeHom, doubleOppositeInv,
    oppositeFunctor, oppositeMap]

/-- Ordinary opposite is an involutive autoequivalence at independent universes. -/
def oppositeEquivalence : SimplicialCat.{o, v} ≌ SimplicialCat.{o, v} where
  functor := oppositeFunctor
  inverse := oppositeFunctor
  unitIso := doubleOppositeNatIso.symm
  counitIso := doubleOppositeNatIso
  functor_unitIso_comp := opposite_triangle

instance : oppositeFunctor.{o, v}.IsEquivalence := oppositeEquivalence.isEquivalence_functor

/-- Opposite preserves the actual object type by the canonical wrapper isomorphism. -/
def oppositeObjectsIso : oppositeFunctor ⋙ objects ≅ objects.{o, v} :=
  NatIso.ofComponents (fun C ↦
    { hom := Opposite.unop
      inv := Opposite.op
      hom_inv_id := rfl
      inv_hom_id := rfl }) (by
    intro C D F
    rfl)

end SimplicialCat

/-- The actual dagger functors form a natural map to the ordinary opposite. -/
def DaggerSimplicialCat.daggerNatural :
    DaggerSimplicialCat.forget.{o, v} ⟶
      DaggerSimplicialCat.forget.{o, v} ⋙ SimplicialCat.oppositeFunctor where
  app C := DaggerSimplicialStructure.daggerFunctor (C := C.Obj)
  naturality {C D} F := by
    change F.toEnrichedFunctor.comp SSet
      (DaggerSimplicialStructure.daggerFunctor (C := D.Obj)) =
      (DaggerSimplicialStructure.daggerFunctor (C := C.Obj)).comp SSet
        (SimplicialCat.oppositeMap F.toEnrichedFunctor)
    apply EnrichedFunctor.ext SSet
    case h_obj =>
      intro X
      rfl
    case h_map =>
      intro X Y
      simpa [SimplicialCat.oppositeMap, DaggerSimplicialStructure.daggerFunctor,
        EnrichedFunctor.comp] using F.map_dagger X Y

end DaggerModels
