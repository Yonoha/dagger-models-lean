import DaggerModels.DaggerGraphIndex
import DaggerModels.DaggerSimplicialGraph

/-!
# From index presheaves to dagger simplicial graphs

Hom spaces are the exact endpoint fibers. Ordinary simplex maps restrict to
these fibers; the index involution exchanges the source and target vertices.
-/

open CategoryTheory Opposite

universe u

namespace DaggerModels.DaggerGraphPresheaf

open DaggerGraphIndex

/-- The degreewise fiber with the specified source and target vertices. -/
def fiber (F : Objᵒᵖ ⥤ Type u) (x y : F.obj (op Obj.vertex))
    (n : SimplexCategoryᵒᵖ) : Type u :=
  {e : F.obj (op (Obj.edge n.unop)) //
    F.map (source n.unop).op e = x ∧ F.map (target n.unop).op e = y}

/-- Restriction along an ordinary simplex operator, preserving endpoints. -/
def fiberMap (F : Objᵒᵖ ⥤ Type u) {x y : F.obj (op Obj.vertex)}
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) (e : fiber F x y n) : fiber F x y m :=
  ⟨F.map (simplex α.unop).op e.val, by
    constructor
    · rw [← FunctorToTypes.map_comp_apply, ← op_comp, source_simplex]
      exact e.property.1
    · rw [← FunctorToTypes.map_comp_apply, ← op_comp, target_simplex]
      exact e.property.2⟩

@[simp] theorem fiberMap_val (F : Objᵒᵖ ⥤ Type u) {x y : F.obj (op Obj.vertex)}
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) (e : fiber F x y n) :
    (fiberMap F α e).val = F.map (simplex α.unop).op e.val := rfl

/-- The simplicial set of edges from `x` to `y`. -/
def hom (F : Objᵒᵖ ⥤ Type u) (x y : F.obj (op Obj.vertex)) : SSet.{u} where
  obj n := fiber F x y n
  map α := fiberMap F α
  map_id n := by
    funext e
    apply Subtype.ext
    change F.map (𝟙 (op (Obj.edge n.unop))) e.val = e.val
    exact FunctorToTypes.map_id_apply F e.val
  map_comp α β := by
    funext e
    apply Subtype.ext
    change F.map ((simplex α.unop).op ≫ (simplex β.unop).op) e.val =
      F.map (simplex β.unop).op (F.map (simplex α.unop).op e.val)
    exact FunctorToTypes.map_comp_apply F _ _ e.val

/-- The index involution acts on fibers by exchanging their endpoints. -/
def swapFiber (F : Objᵒᵖ ⥤ Type u) (n : SimplexCategoryᵒᵖ)
    {x y : F.obj (op Obj.vertex)} (e : fiber F x y n) : fiber F y x n :=
  ⟨F.map (swap n.unop).op e.val, by
    constructor
    · rw [← FunctorToTypes.map_comp_apply, ← op_comp, source_swap]
      exact e.property.2
    · rw [← FunctorToTypes.map_comp_apply, ← op_comp, target_swap]
      exact e.property.1⟩

@[simp] theorem swapFiber_val (F : Objᵒᵖ ⥤ Type u) (n : SimplexCategoryᵒᵖ)
    {x y : F.obj (op Obj.vertex)} (e : fiber F x y n) :
    (swapFiber F n e).val = F.map (swap n.unop).op e.val := rfl

@[simp] theorem swapFiber_involutive (F : Objᵒᵖ ⥤ Type u) (n : SimplexCategoryᵒᵖ)
    {x y : F.obj (op Obj.vertex)} (e : fiber F x y n) :
    swapFiber F n (swapFiber F n e) = e := by
  apply Subtype.ext
  dsimp only [swapFiber]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, swap_involutive, op_id,
    FunctorToTypes.map_id_apply]

/-- Dagger is an ordinary simplicial map, without reversing simplex operators. -/
def dagger (F : Objᵒᵖ ⥤ Type u) (x y : F.obj (op Obj.vertex)) : hom F x y ⟶ hom F y x where
  app n := swapFiber F n
  naturality {n m} α := by
    funext e
    apply Subtype.ext
    change F.map (swap m.unop).op (F.map (simplex α.unop).op e.val) =
      F.map (simplex α.unop).op (F.map (swap n.unop).op e.val)
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
      ← op_comp, ← op_comp, simplex_swap]

/-- The graph reconstructed from the presheaf's vertex value and endpoint fibers. -/
def graph (F : Objᵒᵖ ⥤ Type u) : DaggerSimplicialGraph.{u} where
  Obj := F.obj (op Obj.vertex)
  Hom := hom F
  dagger := dagger F
  dagger_involutive x y := by
    ext n e
    exact swapFiber_involutive F n e

/-- A natural transformation sends a fiber to the fiber of its image endpoints. -/
def fiberNatMap {F H : Objᵒᵖ ⥤ Type u} (η : F ⟶ H)
    {x y : F.obj (op Obj.vertex)} (n : SimplexCategoryᵒᵖ) (e : fiber F x y n) :
    fiber H (η.app (op Obj.vertex) x) (η.app (op Obj.vertex) y) n :=
  ⟨η.app (op (Obj.edge n.unop)) e.val, by
    constructor
    · exact (congrFun (η.naturality (source n.unop).op) e.val).symm.trans
        (congrArg (η.app (op Obj.vertex)) e.property.1)
    · exact (congrFun (η.naturality (target n.unop).op) e.val).symm.trans
        (congrArg (η.app (op Obj.vertex)) e.property.2)⟩

@[simp] theorem fiberNatMap_val {F H : Objᵒᵖ ⥤ Type u} (η : F ⟶ H)
    {x y : F.obj (op Obj.vertex)} (n : SimplexCategoryᵒᵖ) (e : fiber F x y n) :
    (fiberNatMap η n e).val = η.app (op (Obj.edge n.unop)) e.val := rfl

/-- The simplicial maps on hom fibers induced by a natural transformation. -/
def homMap {F H : Objᵒᵖ ⥤ Type u} (η : F ⟶ H) (x y : F.obj (op Obj.vertex)) :
    hom F x y ⟶ hom H (η.app (op Obj.vertex) x) (η.app (op Obj.vertex) y) where
  app n := fiberNatMap η n
  naturality {n m} α := by
    funext e
    apply Subtype.ext
    exact congrFun (η.naturality (simplex α.unop).op) e.val

/-- The induced graph map allows an arbitrary natural transformation on vertices. -/
def graphMap {F H : Objᵒᵖ ⥤ Type u} (η : F ⟶ H) : graph F ⟶ graph H where
  obj := η.app (op Obj.vertex)
  map := homMap η
  map_dagger x y := by
    ext n e
    apply Subtype.ext
    exact (congrFun (η.naturality (swap n.unop).op) e.val).symm

@[simp] theorem graphMap_obj {F H : Objᵒᵖ ⥤ Type u} (η : F ⟶ H) :
    (graphMap η).obj = η.app (op Obj.vertex) := rfl

@[simp] theorem graphMap_map_val {F H : Objᵒᵖ ⥤ Type u} (η : F ⟶ H)
    (x y : F.obj (op Obj.vertex)) (n : SimplexCategoryᵒᵖ) (e : fiber F x y n) :
    (((graphMap η).map x y).app n e).val =
      η.app (op (Obj.edge n.unop)) e.val := rfl

/-- Reconstruction of a graph from an index presheaf, including its morphisms. -/
def inverse : (Objᵒᵖ ⥤ Type u) ⥤ DaggerSimplicialGraph.{u} where
  obj := graph
  map := graphMap
  map_id F := by
    apply DaggerSimplicialGraph.Map.ext rfl
    apply heq_of_eq
    funext x y
    ext n e
    rfl
  map_comp η θ := by
    apply DaggerSimplicialGraph.Map.ext rfl
    apply heq_of_eq
    funext x y
    ext n e
    rfl


end DaggerModels.DaggerGraphPresheaf
