import DaggerModels.DaggerSimplicialForget

/-!
# Descent of enriched functors along graph-split quotients

A graph map whose composite with an enriched dagger functor preserves units and
composition inherits those laws when that functor has a section on underlying
graphs. The section need not preserve units or composition. Dependent arrow and
composable-pair types retain endpoints when the object map is not the identity.
This is used to construct the split coequalizers in Part I `bg.lem.presentable`.
-/

open CategoryTheory MonoidalCategory

universe u

namespace DaggerModels.DaggerSimplicialCat.GraphDescent

abbrev Arrow (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) :=
  Σ x : G.Obj, Σ y : G.Obj, (G.Hom x y).obj n

abbrev Pair (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) :=
  Σ x : G.Obj, Σ y : G.Obj, Σ z : G.Obj, (G.Hom x y).obj n × (G.Hom y z).obj n

def arrowMap {G H : DaggerSimplicialGraph.{u}} (k : G ⟶ H) (n : SimplexCategoryᵒᵖ) :
    Arrow G n → Arrow H n
  | ⟨x, y, e⟩ => ⟨k.obj x, k.obj y, (k.map x y).app n e⟩

def pairMap {G H : DaggerSimplicialGraph.{u}} (k : G ⟶ H) (n : SimplexCategoryᵒᵖ) :
    Pair G n → Pair H n
  | ⟨x, y, z, e, f⟩ =>
      ⟨k.obj x, k.obj y, k.obj z, (k.map x y).app n e, (k.map y z).app n f⟩

@[simp] theorem arrowMap_comp {G H K : DaggerSimplicialGraph.{u}} (a : G ⟶ H)
    (b : H ⟶ K) (n : SimplexCategoryᵒᵖ) (e : Arrow G n) :
    arrowMap (a ≫ b) n e = arrowMap b n (arrowMap a n e) := rfl

@[simp] theorem pairMap_comp {G H K : DaggerSimplicialGraph.{u}} (a : G ⟶ H)
    (b : H ⟶ K) (n : SimplexCategoryᵒᵖ) (e : Pair G n) :
    pairMap (a ≫ b) n e = pairMap b n (pairMap a n e) := rfl

@[simp] theorem arrowMap_id (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    (e : Arrow G n) : arrowMap (𝟙 G) n e = e := by cases e; rfl

@[simp] theorem pairMap_id (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    (e : Pair G n) : pairMap (𝟙 G) n e = e := by cases e; rfl

def identity (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) (x : C.Obj) :
    Arrow (underlyingGraph C) n := ⟨x, x, (eId SSet x).app n PUnit.unit⟩

def composition (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    Pair (underlyingGraph C) n → Arrow (underlyingGraph C) n
  | ⟨x, y, z, e, f⟩ => ⟨x, z, (eComp SSet (show C.Obj from x) y z).app n (e, f)⟩

theorem identity_functor {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
    (n : SimplexCategoryᵒᵖ) (x : C.Obj) :
    arrowMap (underlyingGraphMap F) n (identity C n x) = identity D n (F.obj x) := by
  have h := congrArg (fun k ↦ k.app n PUnit.unit) (F.map_id x)
  exact congrArg (fun e ↦ (⟨F.obj x, F.obj x, e⟩ : Arrow (underlyingGraph D) n)) h

theorem composition_functor {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
    (n : SimplexCategoryᵒᵖ) (e : Pair (underlyingGraph C) n) :
    arrowMap (underlyingGraphMap F) n (composition C n e) =
      composition D n (pairMap (underlyingGraphMap F) n e) := by
  rcases e with ⟨x, y, z, e, f⟩
  have h := congrArg (fun k ↦ k.app n (e, f)) (F.map_comp x y z)
  exact congrArg (fun e ↦ (⟨F.obj x, F.obj z, e⟩ : Arrow (underlyingGraph D) n)) h

variable {C D E : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
  (s : underlyingGraph D ⟶ underlyingGraph C)
  (hs : s ≫ underlyingGraphMap F = 𝟙 (underlyingGraph D))
  (h : underlyingGraph D ⟶ underlyingGraph E) (G : C ⟶ E)
  (hfac : underlyingGraphMap F ≫ h = underlyingGraphMap G)

include F s hs G hfac

theorem identity_preservation (n : SimplexCategoryᵒᵖ) (x : D.Obj) :
    arrowMap h n (identity D n x) = identity E n (h.obj x) := by
  have hx : F.obj (s.obj x) = x := congrArg (fun k ↦ k.obj x) hs
  have hh : G.obj (s.obj x) = h.obj x := by
    have hh := congrArg (fun k ↦ k.obj (s.obj x)) hfac
    change h.obj (F.obj (s.obj x)) = G.obj (s.obj x) at hh
    simpa only [hx] using hh.symm
  calc
    _ = arrowMap h n (arrowMap (underlyingGraphMap F) n (identity C n (s.obj x))) := by
      rw [identity_functor, hx]
    _ = arrowMap (underlyingGraphMap G) n (identity C n (s.obj x)) := by
      rw [← arrowMap_comp, hfac]
    _ = _ := by rw [identity_functor, hh]

theorem composition_preservation (n : SimplexCategoryᵒᵖ)
    (e : Pair (underlyingGraph D) n) :
    arrowMap h n (composition D n e) = composition E n (pairMap h n e) := by
  calc
    _ = arrowMap h n (composition D n
        (pairMap (underlyingGraphMap F) n (pairMap s n e))) := by
      rw [← pairMap_comp, hs, pairMap_id]
    _ = arrowMap h n (arrowMap (underlyingGraphMap F) n
        (composition C n (pairMap s n e))) := by rw [composition_functor]
    _ = arrowMap (underlyingGraphMap G) n (composition C n (pairMap s n e)) := by
      rw [← arrowMap_comp, hfac]
    _ = composition E n (pairMap (underlyingGraphMap G) n (pairMap s n e)) :=
      composition_functor G n _
    _ = _ := by rw [← hfac, pairMap_comp, ← pairMap_comp s, hs, pairMap_id]

/-- Descent along a dagger enriched functor split on its underlying graph. -/
def lift : Hom D E where
  obj := h.obj
  map := h.map
  map_dagger := h.map_dagger
  map_id x := by
    ext n e
    cases e
    have he := identity_preservation F s hs h G hfac n x
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he).2)).2
  map_comp x y z := by
    ext n e
    rcases e with ⟨e, f⟩
    have he := composition_preservation F s hs h G hfac n ⟨x, y, z, e, f⟩
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he).2)).2

@[simp] theorem underlyingGraphMap_lift :
    underlyingGraphMap (lift F s hs h G hfac) = h := rfl

@[simp] theorem comp_lift : F ≫ lift F s hs h G hfac = G := by
  apply forgetGraph.map_injective
  exact hfac

end DaggerModels.DaggerSimplicialCat.GraphDescent
