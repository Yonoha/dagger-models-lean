import ChosenNecklaceVertices

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

theorem stdSimplex_vertex_naturality {X : SSet.{u}} {N n : ℕ} (f : X ⟶ Δ[N])
    (x : X.obj (op ⦋n⦌)) (i : Fin (n + 1)) :
    f.app _ x i = SSet.stdSimplex.obj₀Equiv
      (f.app _ (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op x)) := by
  have h := congrFun (f.naturality (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op) x
  exact (congrArg (fun y : (Δ[N] : SSet.{u}).obj (op ⦋0⦌) ↦ y 0) h).symm

/-- A map into a standard simplex is determined by its full original vertex map. -/
theorem stdSimplex_hom_ext {X : SSet.{u}} {N : ℕ} (f g : X ⟶ Δ[N])
    (h : ∀ x : X.obj (op ⦋0⦌), f.app _ x = g.app _ x) : f = g := by
  ext q x
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ n
  apply SSet.stdSimplex.ext
  intro i
  rw [stdSimplex_vertex_naturality, stdSimplex_vertex_naturality]
  exact congrArg SSet.stdSimplex.obj₀Equiv (h _)

namespace NecklaceCode

variable {T U V : NecklaceCode}

def mapVertices (f : toSSet.{u} T ⟶ toSSet.{u} U) : Vertices.{u} T → Vertices.{u} U :=
  fun v ↦ U.verticesEquiv (f.app _ (T.verticesEquiv.symm v))

theorem mapVertices_id : mapVertices (𝟙 (toSSet.{u} T)) = id := by
  funext v
  exact T.verticesEquiv.apply_symm_apply v

theorem mapVertices_comp (f : toSSet.{u} T ⟶ toSSet.{u} U)
    (g : toSSet.{u} U ⟶ toSSet.{u} V) :
    mapVertices (f ≫ g) = mapVertices g ∘ mapVertices f := by
  funext v
  dsimp [mapVertices]
  rw [U.verticesEquiv.symm_apply_apply]

theorem hom_ext_vertices (f g : toSSet.{u} T ⟶ toSSet.{u} U)
    (h : mapVertices f = mapVertices g) : f = g := by
  apply (cancel_mono U.inclusion).1
  apply stdSimplex_hom_ext
  intro x
  apply SSet.stdSimplex.obj₀Equiv.injective
  change (U.verticesEquiv (f.app _ x)).down = (U.verticesEquiv (g.app _ x)).down
  have hv := congrFun h (T.verticesEquiv x)
  dsimp [mapVertices] at hv
  rw [T.verticesEquiv.symm_apply_apply] at hv
  exact congrArg ULift.down hv

end NecklaceCode

end

end DaggerChosenRigidificationNecklace
