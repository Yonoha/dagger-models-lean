import DaggerModels.DaggerDiscreteObjects

/-! Literal C plus the original identity-only point, with empty mixed Hom spaces. -/
open CategoryTheory MonoidalCategory DaggerModels
universe u
namespace DaggerPointCoproduct
noncomputable section
set_option maxHeartbeats 300000

def emptyHom : SSet.{u} := (Functor.const SimplexCategoryᵒᵖ).obj PEmpty.{u + 1}

def hom (C : DaggerSimplicialCat.{u, u}) :
    C.Obj ⊕ PUnit.{u + 1} → C.Obj ⊕ PUnit.{u + 1} → SSet.{u}
  | .inl x, .inl y => C.enriched.Hom x y
  | .inr x, .inr y => DaggerDiscreteObjects.point.enriched.Hom x y
  | _, _ => emptyHom

def identity (C : DaggerSimplicialCat.{u, u}) (x : C.Obj ⊕ PUnit.{u + 1}) :
    𝟙_ SSet.{u} ⟶ hom C x x := by
  cases x with
  | inl x => exact C.enriched.id x
  | inr x => exact DaggerDiscreteObjects.point.enriched.id x

def composition (C : DaggerSimplicialCat.{u, u})
    (x y z : C.Obj ⊕ PUnit.{u + 1}) : hom C x y ⊗ hom C y z ⟶ hom C x z := by
  cases x <;> cases y <;> cases z
  · exact C.enriched.comp _ _ _
  all_goals first
    | exact DaggerDiscreteObjects.point.enriched.comp _ _ _
    | exact { app := fun _ p ↦ by first | exact PEmpty.elim p.1 | exact PEmpty.elim p.2,
              naturality := by
                intros; funext p
                first | exact PEmpty.elim p.1 | exact PEmpty.elim p.2 }

def enrichment (C : DaggerSimplicialCat.{u, u}) :
    EnrichedCategory SSet.{u} (C.Obj ⊕ PUnit.{u + 1}) where
  Hom := hom C
  id := identity C
  comp := composition C
  id_comp x y := by
    rcases x with x | x <;> rcases y with y | y
    · exact C.enriched.id_comp x y
    · apply NatTrans.ext; funext q p; exact PEmpty.elim p
    · apply NatTrans.ext; funext q p; exact PEmpty.elim p
    · exact DaggerDiscreteObjects.point.enriched.id_comp x y
  comp_id x y := by
    rcases x with x | x <;> rcases y with y | y
    · exact C.enriched.comp_id x y
    · apply NatTrans.ext; funext q p; exact PEmpty.elim p
    · apply NatTrans.ext; funext q p; exact PEmpty.elim p
    · exact DaggerDiscreteObjects.point.enriched.comp_id x y
  assoc x y z t := by
    rcases x with x | x <;> rcases y with y | y <;>
      rcases z with z | z <;> rcases t with t | t
    case inl.inl.inl.inl => exact C.enriched.assoc x y z t
    case inr.inr.inr.inr => exact DaggerDiscreteObjects.point.enriched.assoc x y z t
    all_goals
      apply NatTrans.ext
      funext q p
      first | exact PEmpty.elim p.1 | exact PEmpty.elim p.2.1 | exact PEmpty.elim p.2.2

def dagger (C : DaggerSimplicialCat.{u, u})
    (x y : C.Obj ⊕ PUnit.{u + 1}) : hom C x y ⟶ hom C y x := by
  cases x <;> cases y
  · exact C.daggerStructure.dagger _ _
  all_goals first
    | exact DaggerDiscreteObjects.point.daggerStructure.dagger _ _
    | exact { app := fun _ p ↦ PEmpty.elim p,
              naturality := by intros; funext p; exact PEmpty.elim p }

def daggerStructure (C : DaggerSimplicialCat.{u, u}) :
    @DaggerSimplicialStructure.{u, u} (C.Obj ⊕ PUnit.{u + 1}) (enrichment C) := by
  letI := enrichment C
  exact {
    dagger := dagger C
    dagger_involutive x y := by
      cases x <;> cases y
      · exact C.daggerStructure.dagger_involutive _ _
      all_goals first
        | apply NatTrans.ext
          funext q p
          exact PEmpty.elim p
        | exact DaggerDiscreteObjects.point.daggerStructure.dagger_involutive _ _
    dagger_id x := by
      cases x
      · exact C.daggerStructure.dagger_id _
      · exact DaggerDiscreteObjects.point.daggerStructure.dagger_id _
    dagger_comp x y z := by
      cases x <;> cases y <;> cases z
      · exact C.daggerStructure.dagger_comp _ _ _
      all_goals first
        | apply NatTrans.ext
          funext q p
          first | exact PEmpty.elim p.1 | exact PEmpty.elim p.2
        | exact DaggerDiscreteObjects.point.daggerStructure.dagger_comp _ _ _
  }

/-- The original object type and original same-summand Homs are retained literally. -/
def cat (C : DaggerSimplicialCat.{u, u}) : DaggerSimplicialCat.{u, u} :=
  ⟨⟨C.Obj ⊕ PUnit.{u + 1}, enrichment C⟩, daggerStructure C⟩

def inOld (C : DaggerSimplicialCat.{u, u}) : C ⟶ cat C where
  obj := Sum.inl
  map _ _ := 𝟙 _
  map_id _ := by change _ ≫ (𝟙 _) = _; exact Category.comp_id _
  map_comp x y z := by
    change C.enriched.comp x y z ≫ (𝟙 _) = ((𝟙 _) ⊗ₘ (𝟙 _)) ≫ C.enriched.comp x y z
    simp
  map_dagger x y := by
    change (𝟙 _) ≫ C.daggerStructure.dagger x y = C.daggerStructure.dagger x y ≫ (𝟙 _)
    simp

def inPoint (C : DaggerSimplicialCat.{u, u}) : DaggerDiscreteObjects.point ⟶ cat C where
  obj := Sum.inr
  map _ _ := 𝟙 _
  map_id _ := by change _ ≫ (𝟙 _) = _; exact Category.comp_id _
  map_comp x y z := by
    change DaggerDiscreteObjects.point.enriched.comp x y z ≫ (𝟙 _) =
      ((𝟙 _) ⊗ₘ (𝟙 _)) ≫ DaggerDiscreteObjects.point.enriched.comp x y z
    simp
  map_dagger x y := by
    change (𝟙 _) ≫ DaggerDiscreteObjects.point.daggerStructure.dagger x y =
      DaggerDiscreteObjects.point.daggerStructure.dagger x y ≫ (𝟙 _)
    simp

@[simp] theorem inOld_obj (C : DaggerSimplicialCat.{u, u}) (x : C.Obj) :
    (inOld C).obj x = Sum.inl x := rfl
@[simp] theorem inPoint_obj (C : DaggerSimplicialCat.{u, u}) (x : PUnit.{u + 1}) :
    (inPoint C).obj x = Sum.inr x := rfl
@[simp] theorem inOld_map (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) :
    (inOld C).map x y = 𝟙 (C.enriched.Hom x y) := rfl
@[simp] theorem inPoint_map (C : DaggerSimplicialCat.{u, u}) (x y : PUnit.{u + 1}) :
    (inPoint C).map x y = 𝟙 (DaggerDiscreteObjects.point.enriched.Hom x y) := rfl

theorem inOld_obj_injective (C : DaggerSimplicialCat.{u, u}) :
    Function.Injective (inOld C).obj := Sum.inl_injective

instance inOld_map_isIso (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) :
    IsIso ((inOld C).map x y) := by change IsIso (𝟙 _); infer_instance

end
end DaggerPointCoproduct
