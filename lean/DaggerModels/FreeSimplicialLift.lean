import DaggerModels.FreeSimplicialPaths
import DaggerModels.SimplicialEnrichment

/-!
# Extending edge assignments to enriched functors

An assignment of the edges of a simplicial graph to a simplicial category
extends by composition of finite paths. This constructs the enriched part
of the free-category universal property in Part I `bg.lem.presentable`.
-/

open CategoryTheory MonoidalCategory

universe u

namespace DaggerModels.FreeSimplicialExtension

attribute [local instance] FreeSimplicialPaths.enrichedCategory

variable (G : DaggerSimplicialGraph.{u}) {C : Type u}
  [EnrichedCategory SSet.{u} C]
  (f : G.Obj → C) (φ : ∀ x y, G.Hom x y ⟶ (f x ⟶[SSet.{u}] f y))

/-- The edge assignment in one degree, before freely composing paths. -/
def edgeMap (n : SimplexCategoryᵒᵖ) :
    FreeSimplicialPaths.At G n ⥤q SimplicialEnrichment.At C n where
  obj := f
  map {x y} e := (φ x y).app n e

/-- Freely compose an assigned path in the target degreewise category. -/
def extendAt (n : SimplexCategoryᵒᵖ) :
    Paths (FreeSimplicialPaths.At G n) ⥤ SimplicialEnrichment.At C n :=
  Paths.lift (edgeMap G f φ n)

/-- The value of the extension on an actual finite path. -/
def value (n : SimplexCategoryᵒᵖ) {x y : G.Obj} (p : FreeSimplicialPaths.Path G n x y) :
    (f x ⟶[SSet.{u}] f y).obj n := (extendAt G f φ n).map p

@[simp] theorem value_nil (n : SimplexCategoryᵒᵖ) (x : G.Obj) :
    value G f φ n (Quiver.Path.nil : FreeSimplicialPaths.Path G n x x) =
      (eId SSet (f x)).app n PUnit.unit := rfl

@[simp] theorem value_cons (n : SimplexCategoryᵒᵖ) {x y z : G.Obj}
    (p : FreeSimplicialPaths.Path G n x y) (e : (G.Hom y z).obj n) :
    value G f φ n (p.cons e) =
      (eComp SSet (f x) (f y) (f z)).app n (value G f φ n p, (φ y z).app n e) := rfl

@[simp] theorem value_comp (n : SimplexCategoryᵒᵖ) {x y z : G.Obj}
    (p : FreeSimplicialPaths.Path G n x y) (q : FreeSimplicialPaths.Path G n y z) :
    value G f φ n (p.comp q) =
      (eComp SSet (f x) (f y) (f z)).app n (value G f φ n p, value G f φ n q) :=
  (extendAt G f φ n).map_comp p q

@[simp] theorem value_singleton (n : SimplexCategoryᵒᵖ) {x y : G.Obj}
    (e : (G.Hom x y).obj n) :
    value G f φ n (Quiver.Hom.toPath e) = (φ x y).app n e :=
  Paths.lift_toPath (edgeMap G f φ n) e

/-- Extension respects the same simplicial operator on every edge. -/
theorem value_naturality {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) {x y : G.Obj}
    (p : FreeSimplicialPaths.Path G n x y) :
    (f x ⟶[SSet.{u}] f y).map α (value G f φ n p) =
      value G f φ m (FreeSimplicialPaths.map G α p) := by
  induction p with
  | nil =>
    exact (congrArg (fun p ↦ p PUnit.unit) ((eId SSet (f x)).naturality α)).symm
  | @cons y z p e ih =>
    rw [FreeSimplicialPaths.map_cons, value_cons, value_cons]
    have hc := congrArg (fun h ↦ h (value G f φ n p, (φ y z).app n e))
      ((eComp SSet (f x) (f y) (f z)).naturality α)
    change (eComp SSet (f x) (f y) (f z)).app m
      ((f x ⟶[SSet.{u}] f y).map α (value G f φ n p),
        (f y ⟶[SSet.{u}] f z).map α ((φ y z).app n e)) =
      (f x ⟶[SSet.{u}] f z).map α
        ((eComp SSet (f x) (f y) (f z)).app n (value G f φ n p, (φ y z).app n e)) at hc
    rw [← hc, ih]
    have he : (f y ⟶[SSet.{u}] f z).map α ((φ y z).app n e) =
        (φ y z).app m ((G.Hom y z).map α e) :=
      (congrArg (fun h ↦ h e) ((φ y z).naturality α)).symm
    rw [he]

/-- The enriched functor obtained by freely composing the assigned edges. -/
def extend : EnrichedFunctor SSet.{u} G.Obj C where
  obj := f
  map x y :=
    { app := fun n p ↦ value G f φ n p
      naturality := fun n m α ↦ by
        funext p
        exact (value_naturality G f φ α p).symm }
  map_id x := by
    ext n e
    exact value_nil G f φ n x
  map_comp x y z := by
    ext n p
    exact value_comp G f φ n p.1 p.2

/-- On singleton edges, the extension is the specified simplicial edge map. -/
theorem inclusion_extend (x y : G.Obj) :
    FreeSimplicialPaths.inclusion G x y ≫ (extend G f φ).map x y = φ x y := by
  ext n e
  exact value_singleton G f φ n e

/-- Evaluating a path using a functor's edge restriction recovers that functor. -/
theorem value_restrict (F : EnrichedFunctor SSet.{u} G.Obj C)
    (n : SimplexCategoryᵒᵖ) {x y : G.Obj} (p : FreeSimplicialPaths.Path G n x y) :
    value G F.obj (fun x y ↦ FreeSimplicialPaths.inclusion G x y ≫ F.map x y) n p =
      (F.map x y).app n p := by
  induction p with
  | nil =>
    exact (congrArg (fun h ↦ h.app n PUnit.unit) (F.map_id x)).symm
  | @cons y z p e ih =>
    rw [value_cons, ih]
    exact (congrArg (fun h ↦ h.app n (p, Quiver.Hom.toPath e))
      (F.map_comp x y z)).symm

/-- The extension is determined by its values on the original edges. -/
theorem extend_restrict (F : EnrichedFunctor SSet.{u} G.Obj C) :
    extend G F.obj (fun x y ↦ FreeSimplicialPaths.inclusion G x y ≫ F.map x y) = F := by
  apply EnrichedFunctor.ext SSet
  case h_obj =>
    intro x
    rfl
  case h_map =>
    intro x y
    simp only [eqToHom_refl, Category.comp_id]
    ext n p
    exact value_restrict G F n p

end DaggerModels.FreeSimplicialExtension
