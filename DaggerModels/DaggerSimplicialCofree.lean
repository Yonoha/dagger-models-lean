import DaggerModels.DaggerSimplicialCategory
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
Supplement for Part I `bg.lem.reduction`: the actual ordinary dagger
forgetful functor has a right adjoint. Its mapping spaces are Cartesian pairs
of oppositely directed arrows. No colimit existence hypothesis is used.
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits

universe o v w w'

noncomputable section

namespace DaggerModels.DaggerSimplicialCat.Cofree

def hom (C : SimplicialCat.{o, v}) (X Y : C.Obj) : SSet.{v} :=
  (X ⟶[SSet] Y) ⊗ (Y ⟶[SSet] X)

def identity (C : SimplicialCat.{o, v}) (X : C.Obj) : 𝟙_ SSet ⟶ hom C X X where
  app n p := ((eId SSet X).app n p, (eId SSet X).app n p)
  naturality := by
    intro n m α
    funext p
    exact Prod.ext (congrFun ((eId SSet X).naturality α) p)
      (congrFun ((eId SSet X).naturality α) p)

def composition (C : SimplicialCat.{o, v}) (X Y Z : C.Obj) :
    hom C X Y ⊗ hom C Y Z ⟶ hom C X Z where
  app n p := ((eComp SSet X Y Z).app n (p.1.1, p.2.1),
    (eComp SSet Z Y X).app n (p.2.2, p.1.2))
  naturality := by
    intro n m α
    funext p
    exact Prod.ext (congrFun ((eComp SSet X Y Z).naturality α) (p.1.1, p.2.1))
      (congrFun ((eComp SSet Z Y X).naturality α) (p.2.2, p.1.2))

/-- Only the bundle will install this enrichment; the original category stays available. -/
def enriched (C : SimplicialCat.{o, v}) : EnrichedCategory SSet.{v} C.Obj where
  Hom := hom C
  id := identity C
  comp := composition C
  id_comp X Y := by
    ext n p
    apply Prod.ext
    · exact congrArg (fun f ↦ f.app n p.1) (e_id_comp SSet X Y)
    · exact congrArg (fun f ↦ f.app n p.2) (e_comp_id SSet Y X)
  comp_id X Y := by
    ext n p
    apply Prod.ext
    · exact congrArg (fun f ↦ f.app n p.1) (e_comp_id SSet X Y)
    · exact congrArg (fun f ↦ f.app n p.2) (e_id_comp SSet Y X)
  assoc X Y Z T := by
    ext n p
    apply Prod.ext
    · exact congrArg (fun f ↦ f.app n (p.1.1, p.2.1.1, p.2.2.1))
        (e_assoc SSet X Y Z T)
    · exact (congrArg (fun f ↦ f.app n (p.2.2.2, p.2.1.2, p.1.2))
        (e_assoc SSet T Z Y X)).symm

def dagger (C : SimplicialCat.{o, v}) (X Y : C.Obj) : hom C X Y ⟶ hom C Y X where
  app _ p := (p.2, p.1)

def daggerStructure (C : SimplicialCat.{o, v}) :
    @DaggerSimplicialStructure C.Obj (enriched C) := by
  letI := enriched C
  refine { dagger := dagger C, dagger_involutive := ?_, dagger_id := ?_, dagger_comp := ?_ }
  · intro X Y
    ext n p
    rfl
  · intro X
    ext n p
    rfl
  · intro X Y Z
    ext n p
    simp only [SSet.comp_app]
    rfl

def category (C : SimplicialCat.{o, v}) : DaggerSimplicialCat.{o, v} :=
  ⟨⟨C.Obj, enriched C⟩, daggerStructure C⟩

/-- Project the forward component, retaining all original objects. -/
def projection (C : SimplicialCat.{o, v}) : forget.obj (category C) ⟶ C where
  obj := id
  map X Y := { app := fun _ p ↦ p.1 }
  map_id X := by ext n p; rfl
  map_comp X Y Z := by ext n p; rfl

@[simp]
theorem projection_app (C : SimplicialCat.{o, v}) (X Y : C.Obj)
    (n : SimplexCategoryᵒᵖ) (p : (hom C X Y).obj n) :
    ((projection C).map X Y).app n p = p.1 := rfl

/-- Pair an enriched functor with its evaluation on the original simplicial dagger. -/
def lift {D : DaggerSimplicialCat.{o, v}} (C : SimplicialCat.{o, v})
    (F : forget.obj D ⟶ C) : D ⟶ category C where
  obj := F.obj
  map X Y :=
    { app := fun n p ↦ ((F.map X Y).app n p,
        (F.map Y X).app n ((DaggerSimplicialStructure.dagger X Y).app n p))
      naturality := by
        intro n m α
        funext p
        apply Prod.ext
        · exact congrFun ((F.map X Y).naturality α) p
        · exact congrFun ((DaggerSimplicialStructure.dagger X Y ≫ F.map Y X).naturality α)
            p }
  map_id X := by
    ext n p
    apply Prod.ext
    · exact congrArg (fun f ↦ f.app n p) (F.map_id X)
    · have h := DaggerSimplicialStructure.dagger_id X
      have hF := F.map_id X
      exact congrArg (fun f ↦ f.app n p)
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun f ↦ f ≫ F.map X X) h).trans hF))
  map_comp X Y Z := by
    ext n p
    apply Prod.ext
    · exact congrArg (fun f ↦ f.app n p) (F.map_comp X Y Z)
    · rcases p with ⟨p, q⟩
      have h := DaggerSimplicialStructure.dagger_comp_app X Y Z n p q
      change (F.map Z X).app n _ = _
      rw [h]
      exact congrArg (fun f ↦ f.app n
        ((DaggerSimplicialStructure.dagger Y Z).app n q,
          (DaggerSimplicialStructure.dagger X Y).app n p)) (F.map_comp Z Y X)
  map_dagger X Y := by
    ext n p
    apply Prod.ext
    · rfl
    · exact (congrArg (fun p ↦ (F.map X Y).app n p)
        (congrFun (NatTrans.congr_app
          (DaggerSimplicialStructure.dagger_involutive X Y) n) p)).symm

@[simp]
theorem lift_obj {D : DaggerSimplicialCat.{o, v}} (C : SimplicialCat.{o, v})
    (F : forget.obj D ⟶ C) (X : D.Obj) : (lift C F).obj X = F.obj X := rfl

@[simp]
theorem lift_map_app {D : DaggerSimplicialCat.{o, v}} (C : SimplicialCat.{o, v})
    (F : forget.obj D ⟶ C) (X Y : D.Obj) (n : SimplexCategoryᵒᵖ)
    (p : (X ⟶[SSet] Y).obj n) :
    ((lift C F).map X Y).app n p =
      ((F.map X Y).app n p,
        (F.map Y X).app n ((DaggerSimplicialStructure.dagger X Y).app n p)) := rfl

def project {D : DaggerSimplicialCat.{o, v}} {C : SimplicialCat.{o, v}}
    (F : D ⟶ category C) : forget.obj D ⟶ C := forget.map F ≫ projection C

@[simp]
theorem project_lift {D : DaggerSimplicialCat.{o, v}} (C : SimplicialCat.{o, v})
    (F : forget.obj D ⟶ C) : project (lift C F) = F := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  rfl

@[simp]
theorem lift_project {D : DaggerSimplicialCat.{o, v}} {C : SimplicialCat.{o, v}}
    (F : D ⟶ category C) : lift C (project F) = F := by
  apply Hom.ext
  apply EnrichedFunctor.ext SSet
    (F := (lift C (project F)).toEnrichedFunctor) (G := F.toEnrichedFunctor) (fun _ ↦ rfl)
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  ext n p
  apply Prod.ext
  · rfl
  · exact (congrArg Prod.fst (congrFun (NatTrans.congr_app (F.map_dagger X Y) n) p)).symm

/-- The actual unrestricted enriched functors classify the dagger lifts. -/
def homEquiv (D : DaggerSimplicialCat.{o, v}) (C : SimplicialCat.{o, v}) :
    (forget.obj D ⟶ C) ≃ (D ⟶ category C) where
  toFun := lift C
  invFun := project
  left_inv := project_lift C
  right_inv := lift_project

@[simp]
theorem homEquiv_naturality_left {D' D : DaggerSimplicialCat.{o, v}}
    (C : SimplicialCat.{o, v}) (F : D' ⟶ D) (G : forget.obj D ⟶ C) :
    homEquiv D' C (forget.map F ≫ G) = F ≫ homEquiv D C G := by
  apply (homEquiv D' C).symm.injective
  change project (lift C (forget.map F ≫ G)) = project (F ≫ lift C G)
  rw [project_lift]
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  rfl

/-- The actual right adjoint, obtained from the complete natural Hom equivalence. -/
def functor : SimplicialCat.{o, v} ⥤ DaggerSimplicialCat.{o, v} :=
  Adjunction.rightAdjointOfEquiv homEquiv (fun _ _ C F G ↦ homEquiv_naturality_left C F G)

def adjunction : forget.{o, v} ⊣ functor :=
  Adjunction.adjunctionOfEquivRight homEquiv
    (fun _ _ C F G ↦ homEquiv_naturality_left C F G)

@[simp]
theorem adjunction_counit (C : SimplicialCat.{o, v}) :
    adjunction.counit.app C = projection C := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  rfl

@[simp]
theorem functor_obj (C : SimplicialCat.{o, v}) : functor.obj C = category C := rfl

@[simp]
theorem functor_map_obj {C E : SimplicialCat.{o, v}} (F : C ⟶ E) (X : C.Obj) :
    (functor.map F).obj X = F.obj X := rfl

/-- Both oppositely directed components use the same actual enriched functor. -/
@[simp]
theorem functor_map_app {C E : SimplicialCat.{o, v}} (F : C ⟶ E) (X Y : C.Obj)
    (n : SimplexCategoryᵒᵖ) (p : (hom C X Y).obj n) :
    ((functor.map F).map X Y).app n p =
      ((F.map X Y).app n p.1, (F.map Y X).app n p.2) := rfl

@[simp]
theorem projection_naturality {C E : SimplicialCat.{o, v}} (F : C ⟶ E) :
    forget.map (functor.map F) ≫ projection E = projection C ≫ F := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  rfl

@[simp]
theorem homEquiv_naturality_right {D : DaggerSimplicialCat.{o, v}}
    {C E : SimplicialCat.{o, v}} (F : forget.obj D ⟶ C) (G : C ⟶ E) :
    homEquiv D E (F ≫ G) = homEquiv D C F ≫ functor.map G :=
  adjunction.homEquiv_naturality_right F G

/-- Colimit preservation has no existence hypothesis on ordinary simplicial categories. -/
theorem forget_preservesColimitsOfSize : PreservesColimitsOfSize.{w, w'} forget.{o, v} :=
  adjunction.leftAdjoint_preservesColimits

end DaggerModels.DaggerSimplicialCat.Cofree
