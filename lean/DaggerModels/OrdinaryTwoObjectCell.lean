import DaggerModels.SimplicialCat
import DaggerModels.TwoObjectDaggerGraph

/-!
Part I `bg.not.cells`: the ordinary one-edge simplicial category
and its complete enriched universal property. The target object images may
coincide, and no condition is imposed on the source simplicial set.
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe u

namespace DaggerModels.OrdinaryTwoObjectCell

open TwoObjectDaggerGraph (Vertex left right empty emptyMap emptyMap_unique)

def hom (K : SSet.{u}) : Vertex.{u} → Vertex.{u} → SSet.{u}
  | ⟨false⟩, ⟨false⟩ => 𝟙_ SSet
  | ⟨false⟩, ⟨true⟩ => K
  | ⟨true⟩, ⟨false⟩ => empty
  | ⟨true⟩, ⟨true⟩ => 𝟙_ SSet

def identity (K : SSet.{u}) : ∀ x : Vertex.{u}, 𝟙_ SSet.{u} ⟶ hom K x x
  | ⟨false⟩ => 𝟙 _
  | ⟨true⟩ => 𝟙 _

noncomputable def composition (K : SSet.{u}) :
    ∀ x y z : Vertex.{u}, hom K x y ⊗ hom K y z ⟶ hom K x z
  | ⟨false⟩, ⟨false⟩, ⟨false⟩ => isTerminalTensorUnit.from _
  | ⟨false⟩, ⟨false⟩, ⟨true⟩ => (λ_ K).hom
  | ⟨false⟩, ⟨true⟩, ⟨false⟩ =>
      { app := fun _ p ↦ p.2.elim
        naturality := by intro n m α; funext p; exact p.2.elim }
  | ⟨false⟩, ⟨true⟩, ⟨true⟩ => (ρ_ K).hom
  | ⟨true⟩, ⟨false⟩, ⟨false⟩ =>
      { app := fun _ p ↦ p.1.elim
        naturality := by intro n m α; funext p; exact p.1.elim }
  | ⟨true⟩, ⟨false⟩, ⟨true⟩ =>
      { app := fun _ p ↦ p.1.elim
        naturality := by intro n m α; funext p; exact p.1.elim }
  | ⟨true⟩, ⟨true⟩, ⟨false⟩ =>
      { app := fun _ p ↦ p.2.elim
        naturality := by intro n m α; funext p; exact p.2.elim }
  | ⟨true⟩, ⟨true⟩, ⟨true⟩ => isTerminalTensorUnit.from _

/-- The actual enrichment, without installing a competing global instance. -/
noncomputable def enriched (K : SSet.{u}) : EnrichedCategory SSet.{u} Vertex.{u} where
  Hom := hom K
  id := identity K
  comp := composition K
  id_comp x y := by
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    cases x <;> cases y
    · exact isTerminalTensorUnit.hom_ext _ _
    · ext n p; rfl
    · ext n p; exact p.elim
    · exact isTerminalTensorUnit.hom_ext _ _
  comp_id x y := by
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    cases x <;> cases y
    · exact isTerminalTensorUnit.hom_ext _ _
    · ext n p; rfl
    · ext n p; exact p.elim
    · exact isTerminalTensorUnit.hom_ext _ _
  assoc x y z t := by
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    rcases z with ⟨z⟩
    rcases t with ⟨t⟩
    cases x <;> cases y <;> cases z <;> cases t <;> ext n p
    all_goals first | exact p.1.elim | exact p.2.1.elim | exact p.2.2.elim | rfl

noncomputable def cell (K : SSet.{u}) : SimplicialCat.{u, u} := ⟨Vertex, enriched K⟩

@[simp] theorem hom_left_left (K : SSet.{u}) : hom K left left = 𝟙_ SSet := rfl

@[simp] theorem hom_left_right (K : SSet.{u}) : hom K left right = K := rfl

@[simp] theorem hom_right_left (K : SSet.{u}) : hom K right left = empty := rfl

@[simp] theorem hom_right_right (K : SSet.{u}) : hom K right right = 𝟙_ SSet := rfl

/-- Read the two arbitrary object images and the sole nonidentity generating edge. -/
def classify {K : SSet.{u}} {C : SimplicialCat.{u, u}} (F : cell K ⟶ C) :
    Σ x : C.Obj, Σ y : C.Obj, (K ⟶ (x ⟶[SSet] y)) :=
  ⟨F.obj left, F.obj right, F.map left right⟩

noncomputable def fromData (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (x y : C.Obj) (f : K ⟶ (x ⟶[SSet] y)) : cell K ⟶ C where
  obj
    | ⟨false⟩ => x
    | ⟨true⟩ => y
  map
    | ⟨false⟩, ⟨false⟩ => eId SSet x
    | ⟨false⟩, ⟨true⟩ => f
    | ⟨true⟩, ⟨false⟩ => emptyMap _
    | ⟨true⟩, ⟨true⟩ => eId SSet y
  map_id a := by
    rcases a with ⟨a⟩
    cases a <;> simp [eId, identity, cell, enriched]
  map_comp a b c := by
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    rcases c with ⟨c⟩
    cases a <;> cases b <;> cases c
    · ext n p
      rcases p with ⟨⟨⟩, ⟨⟩⟩
      exact (congrArg (fun g ↦ g.app n ((eId SSet x).app n PUnit.unit))
        (e_id_comp SSet x x)).symm
    · ext n p
      rcases p with ⟨⟨⟩, t⟩
      exact (congrArg (fun g ↦ g.app n (f.app n t)) (e_id_comp SSet x y)).symm
    · ext n p; exact p.2.elim
    · ext n p
      rcases p with ⟨t, ⟨⟩⟩
      exact (congrArg (fun g ↦ g.app n (f.app n t)) (e_comp_id SSet x y)).symm
    · ext n p; exact p.1.elim
    · ext n p; exact p.1.elim
    · ext n p; exact p.2.elim
    · ext n p
      rcases p with ⟨⟨⟩, ⟨⟩⟩
      exact (congrArg (fun g ↦ g.app n ((eId SSet y).app n PUnit.unit))
        (e_id_comp SSet y y)).symm

@[simp]
theorem fromData_obj_left (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (x y : C.Obj) (f : K ⟶ (x ⟶[SSet] y)) : (fromData K C x y f).obj left = x := rfl

@[simp]
theorem fromData_obj_right (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (x y : C.Obj) (f : K ⟶ (x ⟶[SSet] y)) : (fromData K C x y f).obj right = y := rfl

@[simp]
theorem fromData_map_left_right (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (x y : C.Obj) (f : K ⟶ (x ⟶[SSet] y)) : (fromData K C x y f).map left right = f := rfl

@[simp]
theorem classify_fromData (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (x y : C.Obj) (f : K ⟶ (x ⟶[SSet] y)) :
    classify (fromData K C x y f) = ⟨x, y, f⟩ := rfl

@[simp]
theorem fromData_classify {K : SSet.{u}} {C : SimplicialCat.{u, u}}
    (F : cell K ⟶ C) :
    fromData K C (F.obj left) (F.obj right) (F.map left right) = F := by
  apply EnrichedFunctor.ext SSet
    (F := fromData K C (F.obj left) (F.obj right) (F.map left right))
    (G := F) (fun a ↦ by rcases a with ⟨a⟩; cases a <;> rfl)
  intro a b
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  cases a <;> cases b <;> simp only [eqToHom_refl, Category.comp_id]
  · have h := F.map_id left
    change 𝟙 _ ≫ F.map left left = eId SSet (F.obj left) at h
    simpa only [Category.id_comp] using h.symm
  · rfl
  · exact (emptyMap_unique (F.map right left)).symm
  · have h := F.map_id right
    change 𝟙 _ ≫ F.map right right = eId SSet (F.obj right) at h
    simpa only [Category.id_comp] using h.symm

/-- The full enriched universal property, with arbitrary and possibly equal endpoints. -/
noncomputable def homEquiv (K : SSet.{u}) (C : SimplicialCat.{u, u}) :
    (cell K ⟶ C) ≃ Σ x : C.Obj, Σ y : C.Obj, (K ⟶ (x ⟶[SSet] y)) where
  toFun := classify
  invFun p := fromData K C p.1 p.2.1 p.2.2
  left_inv := fromData_classify
  right_inv p := by rcases p with ⟨x, y, f⟩; rfl

@[simp]
theorem homEquiv_apply (K : SSet.{u}) (C : SimplicialCat.{u, u}) (F : cell K ⟶ C) :
    homEquiv K C F = ⟨F.obj left, F.obj right, F.map left right⟩ := rfl

@[simp]
theorem homEquiv_symm_apply (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (p : Σ x : C.Obj, Σ y : C.Obj, (K ⟶ (x ⟶[SSet] y))) :
    (homEquiv K C).symm p = fromData K C p.1 p.2.1 p.2.2 := rfl

noncomputable def map {K L : SSet.{u}} (f : K ⟶ L) : cell K ⟶ cell L :=
  fromData K (cell L) left right f

/-- Apply a simplicial map to the unique nonidentity generating mapping space. -/
noncomputable def functor : SSet.{u} ⥤ SimplicialCat.{u, u} where
  obj := cell
  map := map
  map_id K := by
    apply (homEquiv K (cell K)).injective
    rfl
  map_comp f g := by
    apply (homEquiv _ _).injective
    rfl

@[simp]
theorem homEquiv_naturality_left {K L : SSet.{u}} {C : SimplicialCat.{u, u}}
    (f : K ⟶ L) (F : cell L ⟶ C) :
    homEquiv K C (functor.map f ≫ F) =
      ⟨F.obj left, F.obj right, f ≫ F.map left right⟩ := rfl

def postData {K : SSet.{u}} {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (p : Σ x : C.Obj, Σ y : C.Obj, (K ⟶ (x ⟶[SSet] y))) :
    Σ x : D.Obj, Σ y : D.Obj, (K ⟶ (x ⟶[SSet] y)) :=
  ⟨F.obj p.1, F.obj p.2.1, p.2.2 ≫ F.map p.1 p.2.1⟩

@[simp]
theorem homEquiv_naturality_right {K : SSet.{u}} {C D : SimplicialCat.{u, u}}
    (F : cell K ⟶ C) (G : C ⟶ D) :
    homEquiv K D (F ≫ G) = postData G (homEquiv K C F) := rfl

@[simp]
theorem fromData_naturality_left {K L : SSet.{u}} (C : SimplicialCat.{u, u})
    (f : K ⟶ L) (x y : C.Obj) (g : L ⟶ (x ⟶[SSet] y)) :
    fromData K C x y (f ≫ g) = functor.map f ≫ fromData L C x y g := by
  apply (homEquiv K C).injective
  rfl

@[simp]
theorem fromData_naturality_right {K : SSet.{u}} {C D : SimplicialCat.{u, u}}
    (F : C ⟶ D) (x y : C.Obj) (f : K ⟶ (x ⟶[SSet] y)) :
    fromData K C x y f ≫ F =
      fromData K D (F.obj x) (F.obj y) (f ≫ F.map x y) := by
  apply (homEquiv K D).injective
  rfl

end DaggerModels.OrdinaryTwoObjectCell
