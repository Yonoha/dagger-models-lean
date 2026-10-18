import DaggerModels.DaggerSimplicialGraph

/-! The literal fixed-object graph category of Part I `bg.not.fixed-object`.
Objects have the original object type `O`; every arrow has object map `id O`.
The hom spaces and dagger are full simplicial-set data in arbitrary universe `u`.
-/

open CategoryTheory

universe u

namespace DaggerModels

structure FixedDaggerSimplicialGraph (O : Type u) where
  Hom : O → O → SSet.{u}
  dagger : ∀ x y, Hom x y ⟶ Hom y x
  dagger_involutive : ∀ x y, dagger x y ≫ dagger y x = 𝟙 (Hom x y)

namespace FixedDaggerSimplicialGraph

variable {O : Type u}

@[ext]
structure Map (G H : FixedDaggerSimplicialGraph O) where
  map : ∀ x y, G.Hom x y ⟶ H.Hom x y
  map_dagger : ∀ x y, map x y ≫ H.dagger x y = G.dagger x y ≫ map y x

instance : Category (FixedDaggerSimplicialGraph O) where
  Hom := Map
  id G := { map := fun x y ↦ 𝟙 (G.Hom x y), map_dagger := fun _ _ ↦ by simp }
  comp f g :=
    { map := fun x y ↦ f.map x y ≫ g.map x y
      map_dagger := fun x y ↦ by
        rw [Category.assoc, g.map_dagger, ← Category.assoc, f.map_dagger, Category.assoc] }
  id_comp f := by ext x y; simp
  comp_id f := by ext x y; simp
  assoc f g h := by ext x y; simp [Category.assoc]

@[simp] theorem id_map (G : FixedDaggerSimplicialGraph O) (x y : O) :
    (𝟙 G : G ⟶ G).map x y = 𝟙 (G.Hom x y) := rfl

@[simp] theorem comp_map {G H K : FixedDaggerSimplicialGraph O} (f : G ⟶ H)
    (g : H ⟶ K) (x y : O) : (f ≫ g).map x y = f.map x y ≫ g.map x y := rfl

def toGraph (G : FixedDaggerSimplicialGraph O) : DaggerSimplicialGraph.{u} where
  Obj := O
  Hom := G.Hom
  dagger := G.dagger
  dagger_involutive := G.dagger_involutive

def toGraphMap {G H : FixedDaggerSimplicialGraph O} (f : G ⟶ H) :
    G.toGraph ⟶ H.toGraph where
  obj := id
  map := f.map
  map_dagger := f.map_dagger

def forget : FixedDaggerSimplicialGraph O ⥤ DaggerSimplicialGraph.{u} where
  obj := toGraph
  map := toGraphMap
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem toGraph_obj (G : FixedDaggerSimplicialGraph O) : G.toGraph.Obj = O := rfl

@[simp] theorem toGraphMap_obj {G H : FixedDaggerSimplicialGraph O} (f : G ⟶ H) :
    (toGraphMap f).obj = id := rfl

@[simp] theorem toGraphMap_map {G H : FixedDaggerSimplicialGraph O} (f : G ⟶ H)
    (x y : O) : (toGraphMap f).map x y = f.map x y := rfl

/-- Every existing graph arrow whose object map is literally `id` is a fixed-O arrow. -/
def fromGraphMap {G H : FixedDaggerSimplicialGraph O} (f : G.toGraph ⟶ H.toGraph)
    (hf : f.obj = id) : G ⟶ H := by
  rcases f with ⟨obj, map, map_dagger⟩
  cases hf
  exact ⟨map, map_dagger⟩

@[simp] theorem fromGraphMap_map {G H : FixedDaggerSimplicialGraph O}
    (f : G.toGraph ⟶ H.toGraph) (hf : f.obj = id) (x y : O) :
    (fromGraphMap f hf).map x y ≍ f.map x y := by
  rcases f with ⟨obj, map, map_dagger⟩
  cases hf
  rfl

def mapEquiv {G H : FixedDaggerSimplicialGraph O} :
    (G ⟶ H) ≃ {f : G.toGraph ⟶ H.toGraph // f.obj = id} where
  toFun f := ⟨toGraphMap f, rfl⟩
  invFun f := fromGraphMap f.1 f.2
  left_inv f := by cases f; rfl
  right_inv f := by
    rcases f with ⟨⟨obj, map, map_dagger⟩, hf⟩
    cases hf
    rfl

def mkIso {G H : FixedDaggerSimplicialGraph O} (e : ∀ x y, G.Hom x y ≅ H.Hom x y)
    (he : ∀ x y, (e x y).hom ≫ H.dagger x y = G.dagger x y ≫ (e y x).hom) :
    G ≅ H where
  hom := { map := fun x y ↦ (e x y).hom, map_dagger := he }
  inv :=
    { map := fun x y ↦ (e x y).inv
      map_dagger := fun x y ↦ by
        apply (cancel_mono (e y x).hom).1
        rw [Category.assoc, ← he, ← Category.assoc]
        simp [Category.assoc] }
  hom_inv_id := by
    apply Map.ext
    funext x y
    exact (e x y).hom_inv_id
  inv_hom_id := by
    apply Map.ext
    funext x y
    exact (e x y).inv_hom_id

end FixedDaggerSimplicialGraph
end DaggerModels
