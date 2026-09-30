import DaggerModels.SimplicialCat
import DaggerModels.DaggerCategory
import Mathlib.CategoryTheory.Enriched.Opposite

/-!
# Dagger simplicial categories

This implements Part I, `bg.def.dagger-scat`: dagger is a simplicial map
between the reversed hom spaces, fixes enriched identities, and reverses
composition. It does not reverse the simplex category and does not impose
a fixed-vertex condition on mapping spaces. Objects and mapping spaces have
independent universes. No model structure is assumed here.
-/

open CategoryTheory MonoidalCategory BraidedCategory Opposite Simplicial

universe o v

namespace DaggerModels

/-- The canonical swap on the actual Cartesian tensor of simplicial sets. -/
noncomputable instance sSetBraidedCategory : BraidedCategory SSet.{v} :=
  .ofCartesianMonoidalCategory

/-- The chosen SSet braiding is the actual pointwise swap. -/
theorem sSetBraiding_app_apply (K L : SSet.{v}) (n : SimplexCategoryᵒᵖ)
    (x : (K ⊗ L).obj n) : (β_ K L).hom.app n x = (x.2, x.1) := by
  apply Prod.ext
  · exact congrFun (NatTrans.congr_app
      (CartesianMonoidalCategory.braiding_hom_fst K L) n) x
  · exact congrFun (NatTrans.congr_app
      (CartesianMonoidalCategory.braiding_hom_snd K L) n) x

/-- The hom-level form of an identity-on-objects involutive simplicial functor to the opposite. -/
class DaggerSimplicialStructure (C : Type o) [EnrichedCategory SSet.{v} C] where
  dagger (X Y : C) : (X ⟶[SSet.{v}] Y) ⟶ (Y ⟶[SSet.{v}] X)
  dagger_involutive (X Y : C) : dagger X Y ≫ dagger Y X = 𝟙 _
  dagger_id (X : C) : eId SSet X ≫ dagger X X = eId SSet X
  dagger_comp (X Y Z : C) :
    eComp SSet X Y Z ≫ dagger X Z =
      (dagger X Y ⊗ₘ dagger Y Z) ≫
        (β_ (Y ⟶[SSet.{v}] X) (Z ⟶[SSet.{v}] Y)).hom ≫ eComp SSet Z Y X

namespace DaggerSimplicialStructure

variable {C : Type o} [EnrichedCategory SSet.{v} C] [DaggerSimplicialStructure C]

/-- The full mapping spaces are isomorphic by the actual involutive dagger maps. -/
def daggerIso (X Y : C) : (X ⟶[SSet.{v}] Y) ≅ (Y ⟶[SSet.{v}] X) where
  hom := dagger X Y
  inv := dagger Y X
  hom_inv_id := dagger_involutive X Y
  inv_hom_id := dagger_involutive Y X

/-- Dagger acts on every simplex of a mapping space. -/
def daggerSimplex {X Y : C} {n : ℕ} (x : (X ⟶[SSet.{v}] Y) _⦋n⦌) :
    (Y ⟶[SSet.{v}] X) _⦋n⦌ := (dagger X Y).app (op ⦋n⦌) x

@[simp]
theorem daggerSimplex_involutive {X Y : C} {n : ℕ} (x : (X ⟶[SSet.{v}] Y) _⦋n⦌) :
    daggerSimplex (daggerSimplex x) = x :=
  congrFun (NatTrans.congr_app (dagger_involutive X Y) (op ⦋n⦌)) x

/-- Dagger commutes with the same simplex operator, without reversal. -/
theorem daggerSimplex_map {X Y : C} {n k : ℕ} (α : ⦋k⦌ ⟶ ⦋n⦌)
    (x : (X ⟶[SSet.{v}] Y) _⦋n⦌) :
    daggerSimplex ((X ⟶[SSet.{v}] Y).map α.op x) =
      (Y ⟶[SSet.{v}] X).map α.op (daggerSimplex x) :=
  congrFun ((dagger X Y).naturality α.op) x

/-- Dagger fixes the enriched identity in every degree. -/
theorem dagger_id_app (X : C) (n : SimplexCategoryᵒᵖ) :
    (dagger X X).app n ((eId SSet X).app n PUnit.unit) =
      (eId SSet X).app n PUnit.unit :=
  congrFun (NatTrans.congr_app (dagger_id X) n) PUnit.unit

/-- The actual composition of simplices is reversed in every degree. -/
theorem dagger_comp_app (X Y Z : C) (n : SimplexCategoryᵒᵖ)
    (f : (X ⟶[SSet.{v}] Y).obj n) (g : (Y ⟶[SSet.{v}] Z).obj n) :
    (dagger X Z).app n ((eComp SSet X Y Z).app n (f, g)) =
      (eComp SSet Z Y X).app n ((dagger Y Z).app n g, (dagger X Y).app n f) := by
  have h := congrFun (NatTrans.congr_app (dagger_comp X Y Z) n) (f, g)
  simpa only [SSet.comp_app, Function.comp_apply, SSet.tensorHom_app_apply,
    sSetBraiding_app_apply] using h

/-- The actual enriched dagger functor, with object map `Opposite.op`. -/
def daggerFunctor : EnrichedFunctor SSet.{v} C Cᵒᵖ where
  obj := Opposite.op
  map := dagger
  map_id := dagger_id
  map_comp X Y Z := dagger_comp X Y Z

/-- The inverse enriched functor uses the same dagger on the reversed hom spaces. -/
def daggerInverse : EnrichedFunctor SSet.{v} Cᵒᵖ C where
  obj := Opposite.unop
  map X Y := dagger Y.unop X.unop
  map_id X := dagger_id X.unop
  map_comp X Y Z := by
    change (β_ _ _).hom ≫ eComp SSet Z.unop Y.unop X.unop ≫
      dagger Z.unop X.unop = _
    rw [dagger_comp, ← braiding_naturality_assoc]
    simp

/-- Dagger followed by its typed inverse is exactly the identity enriched functor. -/
@[simp]
theorem daggerFunctor_comp_inverse :
    (daggerFunctor (C := C)).comp SSet daggerInverse = EnrichedFunctor.id SSet C := by
  apply EnrichedFunctor.ext SSet
  case h_obj =>
    intro X
    rfl
  case h_map =>
    intro X Y
    simpa [daggerFunctor, daggerInverse, EnrichedFunctor.comp, EnrichedFunctor.id] using
      dagger_involutive X Y

/-- The other typed composite is exactly the identity enriched functor on the opposite. -/
@[simp]
theorem daggerInverse_comp_functor :
    (daggerInverse (C := C)).comp SSet daggerFunctor = EnrichedFunctor.id SSet Cᵒᵖ := by
  apply EnrichedFunctor.ext SSet
  case h_obj =>
    intro X
    rfl
  case h_map =>
    intro X Y
    simpa [daggerFunctor, daggerInverse, EnrichedFunctor.comp, EnrichedFunctor.id] using
      dagger_involutive Y.unop X.unop

/-- The genuine dagger functor on the underlying degree-zero category. -/
noncomputable def underlyingDaggerFunctor :
    ForgetEnrichment SSet.{v} C ⥤ (ForgetEnrichment SSet.{v} C)ᵒᵖ :=
  daggerFunctor.forget ⋙ (forgetEnrichmentOppositeEquivalence SSet C).functor

/-- The existing ordinary dagger-category structure is induced by the full simplicial dagger. -/
instance underlyingDaggerCategory : DaggerCategory (ForgetEnrichment SSet.{v} C) where
  dagger f := ForgetEnrichment.homOf SSet
    (ForgetEnrichment.homTo SSet f ≫ dagger _ _)
  dagger_involutive f := by
    change (ForgetEnrichment.homTo SSet f ≫ dagger _ _) ≫ dagger _ _ = _
    rw [Category.assoc, dagger_involutive, Category.comp_id]
    rfl
  dagger_id X := dagger_id (ForgetEnrichment.to SSet X)
  dagger_comp f g := by
    exact congrArg Quiver.Hom.unop (underlyingDaggerFunctor.map_comp f g)

end DaggerSimplicialStructure

/-- A bundled genuine dagger simplicial category, with separate object and hom universes. -/
structure DaggerSimplicialCat where
  toSimplicialCat : SimplicialCat.{o, v}
  daggerStructure : DaggerSimplicialStructure toSimplicialCat.Obj

namespace DaggerSimplicialCat

/-- The objects of the original simplicial category. -/
abbrev Obj (C : DaggerSimplicialCat.{o, v}) := C.toSimplicialCat.Obj

instance : CoeSort (DaggerSimplicialCat.{o, v}) (Type o) := ⟨Obj⟩

instance enriched (C : DaggerSimplicialCat.{o, v}) : EnrichedCategory SSet.{v} C.Obj :=
  C.toSimplicialCat.enriched

instance daggerStructureInstance (C : DaggerSimplicialCat.{o, v}) :
    DaggerSimplicialStructure C.Obj := C.daggerStructure

/-- Bundle an actual enrichment and its full dagger structure. -/
def of (C : Type o) [EnrichedCategory SSet.{v} C] [DaggerSimplicialStructure C] :
    DaggerSimplicialCat.{o, v} :=
  ⟨SimplicialCat.of C, show DaggerSimplicialStructure C from inferInstance⟩

/-- A dagger simplicial functor consists of its actual enriched functor and dagger compatibility. -/
structure Hom (C D : DaggerSimplicialCat.{o, v}) extends
    EnrichedFunctor SSet.{v} C.Obj D.Obj where
  map_dagger (X Y : C.Obj) :
    map X Y ≫ DaggerSimplicialStructure.dagger (obj X) (obj Y) =
      DaggerSimplicialStructure.dagger X Y ≫ map Y X

@[ext]
theorem Hom.ext {C D : DaggerSimplicialCat.{o, v}} {F G : Hom C D}
    (h : F.toEnrichedFunctor = G.toEnrichedFunctor) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- The identity preserves the actual simplicial dagger maps. -/
def Hom.id (C : DaggerSimplicialCat.{o, v}) : Hom C C where
  toEnrichedFunctor := EnrichedFunctor.id SSet C.Obj
  map_dagger X Y := by simp

/-- Composition of dagger simplicial functors. -/
def Hom.comp {C D E : DaggerSimplicialCat.{o, v}} (F : Hom C D) (G : Hom D E) :
    Hom C E where
  toEnrichedFunctor := F.toEnrichedFunctor.comp SSet G.toEnrichedFunctor
  map_dagger X Y := by
    dsimp
    rw [Category.assoc, G.map_dagger, ← Category.assoc, F.map_dagger, Category.assoc]

instance : Category DaggerSimplicialCat.{o, v} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp F := by
    apply Hom.ext
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [Hom.id, Hom.comp, EnrichedFunctor.id, EnrichedFunctor.comp]
  comp_id F := by
    apply Hom.ext
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [Hom.id, Hom.comp, EnrichedFunctor.id, EnrichedFunctor.comp]
  assoc F G H := by
    apply Hom.ext
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [Hom.comp, EnrichedFunctor.comp, Category.assoc]

@[simp] theorem id_obj (C : DaggerSimplicialCat.{o, v}) (X : C.Obj) :
    (𝟙 C : Hom C C).obj X = X := rfl

@[simp] theorem comp_obj {C D E : DaggerSimplicialCat.{o, v}} (F : C ⟶ D) (G : D ⟶ E)
    (X : C.Obj) : (F ≫ G).obj X = G.obj (F.obj X) := rfl

@[simp] theorem id_map (C : DaggerSimplicialCat.{o, v}) (X Y : C.Obj) :
    (𝟙 C : Hom C C).map X Y = 𝟙 (X ⟶[SSet.{v}] Y) := rfl

@[simp] theorem comp_map {C D E : DaggerSimplicialCat.{o, v}} (F : C ⟶ D) (G : D ⟶ E)
    (X Y : C.Obj) : (F ≫ G).map X Y = F.map X Y ≫ G.map (F.obj X) (F.obj Y) := rfl

/-- Dagger simplicial functors induce ordinary dagger functors in degree zero. -/
instance Hom.underlyingDaggerFunctor {C D : DaggerSimplicialCat.{o, v}} (F : Hom C D) :
    DaggerFunctor F.toEnrichedFunctor.forget where
  map_dagger f := by
    change (ForgetEnrichment.homTo SSet f ≫ DaggerSimplicialStructure.dagger _ _) ≫
      F.map _ _ = (ForgetEnrichment.homTo SSet f ≫ F.map _ _) ≫
        DaggerSimplicialStructure.dagger _ _
    rw [Category.assoc, ← F.map_dagger, ← Category.assoc]

/-- The original forgetful functor from dagger simplicial categories to simplicial categories. -/
def forget : DaggerSimplicialCat.{o, v} ⥤ SimplicialCat.{o, v} where
  obj C := C.toSimplicialCat
  map F := F.toEnrichedFunctor

instance : forget.{o, v}.Faithful where
  map_injective := Hom.ext

end DaggerSimplicialCat
end DaggerModels
