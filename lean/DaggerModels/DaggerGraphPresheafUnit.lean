import DaggerModels.DaggerGraphPresheafForward
import DaggerModels.DaggerGraphPresheafInverse

/-!
# Recovering a dagger graph from its total-edge presheaf

The unit retains every vertex and identifies each original edge space with
the exact fiber of its endpoints. It is natural for arbitrary graph maps.
-/

open CategoryTheory Opposite

universe u

namespace DaggerModels.DaggerGraphPresheaf

open DaggerGraphIndex
open DaggerSimplicialGraph.TotalSpace

/-- Insert an edge simplex into its exact endpoint fiber. -/
def unitHomMap (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) :
    G.Hom x y ⟶ hom (presheaf G) x y where
  app n e := ⟨⟨x, y, e⟩, rfl, rfl⟩
  naturality {n m} α := by
    funext e
    rfl

/-- Recover the original edge simplex from its total-edge fiber. -/
def unitInvMap (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) :
    hom (presheaf G) x y ⟶ G.Hom x y where
  app n e := fiberEquiv G x y n e
  naturality {n m} α := by
    funext e
    exact fiberEquiv_naturality G x y α e

@[simp] theorem unitHomMap_app_val (G : DaggerSimplicialGraph.{u}) (x y : G.Obj)
    (n : SimplexCategoryᵒᵖ) (e : (G.Hom x y).obj n) :
    ((unitHomMap G x y).app n e).val = ⟨x, y, e⟩ := rfl

@[simp] theorem unitInvMap_unitHomMap (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) :
    unitHomMap G x y ≫ unitInvMap G x y = 𝟙 (G.Hom x y) := by
  ext n e
  rfl

@[simp] theorem unitHomMap_unitInvMap (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) :
    unitInvMap G x y ≫ unitHomMap G x y = 𝟙 (hom (presheaf G) x y) := by
  ext n e
  exact (fiberEquiv G x y n).symm_apply_apply e

/-- The graph map retaining vertices and inserting typed edges into total edges. -/
def unitHom (G : DaggerSimplicialGraph.{u}) : G ⟶ graph (presheaf G) where
  obj := id
  map := unitHomMap G
  map_dagger x y := by
    ext n e
    apply Subtype.ext
    change (DaggerSimplicialGraph.TotalSpace.dagger G).app n
      ((edges G).map (𝟙 n) ⟨x, y, e⟩) =
      ⟨y, x, (G.dagger x y).app n e⟩
    rw [FunctorToTypes.map_id_apply]
    rfl

/-- The inverse graph map recovers the original typed edge spaces. -/
def unitInv (G : DaggerSimplicialGraph.{u}) : graph (presheaf G) ⟶ G where
  obj := id
  map := unitInvMap G
  map_dagger x y := by
    ext n e
    rcases e with ⟨⟨x', y', e⟩, hx, hy⟩
    change x' = x at hx
    change y' = y at hy
    subst x'
    subst y'
    change (G.dagger x y).app n e =
      fiberEquiv G y x n
        ⟨(DaggerSimplicialGraph.TotalSpace.dagger G).app n
          ((edges G).map (𝟙 n) ⟨x, y, e⟩), _⟩
    simp only [FunctorToTypes.map_id_apply]
    rfl

/-- The vertex and endpoint-fiber identification is an actual graph isomorphism. -/
def unitIsoApp (G : DaggerSimplicialGraph.{u}) : G ≅ graph (presheaf G) where
  hom := unitHom G
  inv := unitInv G
  hom_inv_id := by
    apply DaggerSimplicialGraph.Map.ext rfl
    apply heq_of_eq
    funext x y
    exact unitInvMap_unitHomMap G x y
  inv_hom_id := by
    apply DaggerSimplicialGraph.Map.ext
      (f := unitInv G ≫ unitHom G) (g := 𝟙 (graph (presheaf G)))
    · rfl
    apply heq_of_eq
    funext x y
    exact unitHomMap_unitInvMap G x y

/-- Recovery of a graph from its presheaf is natural for every graph map. -/
def unitIso : 𝟭 DaggerSimplicialGraph.{u} ≅ functor ⋙ inverse :=
  NatIso.ofComponents unitIsoApp (fun k ↦ by
    apply DaggerSimplicialGraph.Map.ext rfl
    apply heq_of_eq
    funext x y
    ext n e
    rfl)

@[simp] theorem unitIso_hom_app (G : DaggerSimplicialGraph.{u}) :
    unitIso.hom.app G = unitHom G := rfl

@[simp] theorem unitIso_inv_app (G : DaggerSimplicialGraph.{u}) :
    unitIso.inv.app G = unitInv G := rfl

@[simp] theorem unitHom_obj (G : DaggerSimplicialGraph.{u}) : (unitHom G).obj = id := rfl

@[simp] theorem unitInv_obj (G : DaggerSimplicialGraph.{u}) : (unitInv G).obj = id := rfl

@[simp] theorem unitHom_map_val (G : DaggerSimplicialGraph.{u}) (x y : G.Obj)
    (n : SimplexCategoryᵒᵖ) (e : (G.Hom x y).obj n) :
    (((unitHom G).map x y).app n e).val = ⟨x, y, e⟩ := rfl

@[simp] theorem unitInv_map (G : DaggerSimplicialGraph.{u}) (x y : G.Obj)
    (n : SimplexCategoryᵒᵖ) (e : fiber (presheaf G) x y n) :
    ((unitInv G).map x y).app n e = fiberEquiv G x y n e := rfl

end DaggerModels.DaggerGraphPresheaf
