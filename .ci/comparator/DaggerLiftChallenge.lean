import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Enriched.Opposite
import Mathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.AlgebraicTopology.SimplicialNerve
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Adjunction.Unique

/-! Full `dj.lem.lift` for the original Yoneda-extension adjunction, at any common universe.
All category, dagger, and forgetting data are explicit; only theorem proofs are markers.
Both free adjunctions are witnesses, not hypotheses. Their universal properties use the
original forgetful functors; the ordinary-category pushout presentation is separate. -/
open CategoryTheory Limits MonoidalCategory BraidedCategory Opposite Simplicial
universe o v u
namespace DaggerModels

structure SimplicialCat where
  Obj : Type o
  enriched : EnrichedCategory SSet.{v} Obj
attribute [instance] SimplicialCat.enriched

namespace SimplicialCat
instance : CoeSort (SimplicialCat.{o, v}) (Type o) := ⟨Obj⟩
def of (C : Type o) [EnrichedCategory SSet.{v} C] : SimplicialCat.{o, v} :=
  ⟨C, inferInstance⟩
instance : Category (SimplicialCat.{o, v}) where
  Hom C D := EnrichedFunctor SSet.{v} C.Obj D.Obj
  id C := EnrichedFunctor.id SSet C.Obj
  comp F G := EnrichedFunctor.comp SSet F G
  id_comp F := by
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [EnrichedFunctor.comp, EnrichedFunctor.id]
  comp_id F := by
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [EnrichedFunctor.comp, EnrichedFunctor.id]
  assoc F G H := by
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [EnrichedFunctor.comp, Category.assoc]
end SimplicialCat

noncomputable instance sSetBraidedCategory : BraidedCategory SSet.{v} :=
  .ofCartesianMonoidalCategory

class DaggerSimplicialStructure (C : Type o) [EnrichedCategory SSet.{v} C] where
  dagger (X Y : C) : (X ⟶[SSet.{v}] Y) ⟶ (Y ⟶[SSet.{v}] X)
  dagger_involutive (X Y : C) : dagger X Y ≫ dagger Y X = 𝟙 _
  dagger_id (X : C) : eId SSet X ≫ dagger X X = eId SSet X
  dagger_comp (X Y Z : C) :
    eComp SSet X Y Z ≫ dagger X Z =
      (dagger X Y ⊗ₘ dagger Y Z) ≫
        (β_ (Y ⟶[SSet.{v}] X) (Z ⟶[SSet.{v}] Y)).hom ≫ eComp SSet Z Y X

structure DaggerSimplicialCat where
  toSimplicialCat : SimplicialCat.{o, v}
  daggerStructure : DaggerSimplicialStructure toSimplicialCat.Obj
namespace DaggerSimplicialCat
abbrev Obj (C : DaggerSimplicialCat.{o, v}) := C.toSimplicialCat.Obj
instance : CoeSort (DaggerSimplicialCat.{o, v}) (Type o) := ⟨Obj⟩
instance enriched (C : DaggerSimplicialCat.{o, v}) : EnrichedCategory SSet.{v} C.Obj :=
  C.toSimplicialCat.enriched
instance daggerStructureInstance (C : DaggerSimplicialCat.{o, v}) :
    DaggerSimplicialStructure C.Obj := C.daggerStructure

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

def Hom.id (C : DaggerSimplicialCat.{o, v}) : Hom C C where
  toEnrichedFunctor := EnrichedFunctor.id SSet C.Obj
  map_dagger X Y := by simp

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

def forget : DaggerSimplicialCat.{o, v} ⥤ SimplicialCat.{o, v} where
  obj C := C.toSimplicialCat
  map F := F.toEnrichedFunctor

end DaggerSimplicialCat

structure DaggerSSet where
  toSSet : SSet.{u}
  dagger : toSSet ⟶ toSSet.op
  involutive (n : ℕ) (x : toSSet _⦋n⦌) :
    SSet.opObjEquiv (dagger.app (op ⦋n⦌)
      (SSet.opObjEquiv (dagger.app (op ⦋n⦌) x))) = x
  fixedVertices (x : toSSet _⦋0⦌) : SSet.opObjEquiv (dagger.app (op ⦋0⦌) x) = x
namespace DaggerSSet
structure Hom (X Y : DaggerSSet.{u}) where
  hom : X.toSSet ⟶ Y.toSSet
  comm : hom ≫ Y.dagger = X.dagger ≫ SSet.opFunctor.map hom
@[ext] theorem Hom.ext {X Y : DaggerSSet.{u}} {f g : Hom X Y}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl
instance : Category DaggerSSet.{u} where
  Hom := Hom
  id X := ⟨𝟙 X.toSSet, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    rw [Category.assoc, g.comm, ← Category.assoc, f.comm,
      Category.assoc, Functor.map_comp]⟩
  id_comp f := by apply Hom.ext; simp
  comp_id f := by apply Hom.ext; simp
  assoc f g h := by apply Hom.ext; simp [Category.assoc]
def forget : DaggerSSet.{u} ⥤ SSet.{u} where
  obj X := X.toSSet
  map f := f.hom
end DaggerSSet

set_option warningAsError false in
theorem simplicialCatHasColimits : HasColimits.{u} SimplicialCat.{u, u} := by sorry

namespace OrdinaryRigidification

noncomputable def simplexThickening (n : SimplexCategory) : SimplicialCat.{u, u} :=
  SimplicialCat.of (SimplicialThickening (ULift.{u} (Fin (n.len + 1))))

noncomputable def cosimplicialThickening : SimplexCategory ⥤ SimplicialCat.{u, u} where
  obj := simplexThickening
  map f := SimplicialThickening.functor f.toOrderHom.uliftMap
  map_id n := by
    exact SimplicialThickening.functor_id _
  map_comp f g := by
    exact SimplicialThickening.functor_comp f.toOrderHom.uliftMap g.toOrderHom.uliftMap

noncomputable def coherentNerve : SimplicialCat.{u, u} ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{u} cosimplicialThickening

local instance : HasColimits.{u} SimplicialCat.{u, u} := simplicialCatHasColimits

local instance : HasColimitsOfSize.{0, u} SimplicialCat.{u, u} :=
  hasColimitsOfSizeShrink.{0, u} SimplicialCat.{u, u}

noncomputable def rigidification : SSet.{u} ⥤ SimplicialCat.{u, u} :=
  uliftYoneda.{u}.leftKanExtension cosimplicialThickening

noncomputable def rigidificationCoherentNerveAdjunction :
    rigidification.{u} ⊣ coherentNerve.{u} := by
  unfold rigidification coherentNerve
  exact Presheaf.uliftYonedaAdjunction _
    (uliftYoneda.{u}.leftKanExtensionUnit cosimplicialThickening)

/-- Full lift, including the original Hom correspondence and the canonical comparison. -/
structure DaggerLiftWitness where
  freeSSet : SSet.{u} ⥤ DaggerSSet.{u}
  freeSSetAdjunction : freeSSet ⊣ DaggerSSet.forget
  freeSCat : SimplicialCat.{u, u} ⥤ DaggerSimplicialCat.{u, u}
  freeSCatAdjunction : freeSCat ⊣ DaggerSimplicialCat.forget
  freeSCat_objects (C : SimplicialCat.{u, u}) : (freeSCat.obj C).Obj = C.Obj
  freeSCat_unit_objects (C : SimplicialCat.{u, u}) :
    HEq (freeSCatAdjunction.unit.app C).obj (id : C.Obj → C.Obj)
  left : DaggerSSet.{u} ⥤ DaggerSimplicialCat.{u, u}
  right : DaggerSimplicialCat.{u, u} ⥤ DaggerSSet.{u}
  adjunction : left ⊣ right
  left_forget : left ⋙ DaggerSimplicialCat.forget = DaggerSSet.forget ⋙ rigidification
  right_forget : right ⋙ DaggerSSet.forget = DaggerSimplicialCat.forget ⋙ coherentNerve
  homEquiv_compatibility (X : DaggerSSet.{u}) (C : DaggerSimplicialCat.{u, u})
      (f : left.obj X ⟶ C) :
    rigidificationCoherentNerveAdjunction.homEquiv X.toSSet C.toSimplicialCat
        ((eqToIso left_forget).inv.app X ≫ DaggerSimplicialCat.forget.map f) =
      (adjunction.homEquiv X C f).hom ≫ (eqToIso right_forget).hom.app C
  homEquiv_symm_compatibility (X : DaggerSSet.{u}) (C : DaggerSimplicialCat.{u, u})
      (g : X ⟶ right.obj C) :
    (rigidificationCoherentNerveAdjunction.homEquiv X.toSSet C.toSimplicialCat).symm
        (g.hom ≫ (eqToIso right_forget).hom.app C) =
      (eqToIso left_forget).inv.app X ≫
        DaggerSimplicialCat.forget.map ((adjunction.homEquiv X C).symm g)
  unit_compatibility (X : DaggerSSet.{u}) :
    (adjunction.unit.app X).hom ≫ (eqToIso right_forget).hom.app (left.obj X) ≫
        coherentNerve.map ((eqToIso left_forget).hom.app X) =
      rigidificationCoherentNerveAdjunction.unit.app X.toSSet
  counit_compatibility (C : DaggerSimplicialCat.{u, u}) :
    rigidification.map ((eqToIso right_forget).inv.app C) ≫
        (eqToIso left_forget).inv.app (right.obj C) ≫
        DaggerSimplicialCat.forget.map (adjunction.counit.app C) =
      rigidificationCoherentNerveAdjunction.counit.app C.toSimplicialCat
  comparison : freeSSet ⋙ left ≅ rigidification ⋙ freeSCat
  comparison_canonical : comparison = Adjunction.leftAdjointUniq
    ((freeSSetAdjunction.comp adjunction).ofNatIsoRight (eqToIso right_forget))
    (rigidificationCoherentNerveAdjunction.comp freeSCatAdjunction)
  comparison_unit (X : SSet.{u}) :
    ((freeSSetAdjunction.comp adjunction).ofNatIsoRight
        (eqToIso right_forget)).unit.app X ≫
        (DaggerSimplicialCat.forget ⋙ coherentNerve).map (comparison.hom.app X) =
      (rigidificationCoherentNerveAdjunction.comp freeSCatAdjunction).unit.app X
  comparison_counit (C : DaggerSimplicialCat.{u, u}) :
    comparison.hom.app (coherentNerve.obj C.toSimplicialCat) ≫
        (rigidificationCoherentNerveAdjunction.comp freeSCatAdjunction).counit.app C =
      ((freeSSetAdjunction.comp adjunction).ofNatIsoRight
        (eqToIso right_forget)).counit.app C

set_option warningAsError false in
theorem exists_daggerRigidificationLift : Nonempty (DaggerLiftWitness.{u}) := by sorry

end OrdinaryRigidification
end DaggerModels
