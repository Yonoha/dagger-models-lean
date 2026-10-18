import OriginalCounitRightCone
import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal

/-!
# The actual right cones form a cosimplicial simplicial set

The object at `[n]` is exactly `DaggerOriginalCounitRightCone.cone n`,
the previously chosen pushout. Ordinal sum with `[0]` supplies its
large-simplex maps; the collapsed face maps by the identity of `Δ[0]`.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Simplicial

universe u

namespace DaggerOriginalCounitRightConeFunctor

open DaggerOriginalCounitRightCone

noncomputable section

/-- Append the final ordinal point to a simplex morphism. -/
def joinHom {m n : SimplexCategory} (α : m ⟶ n) :
    SimplexCategory.mk (m.len + 1) ⟶ SimplexCategory.mk (n.len + 1) :=
  AugmentedSimplexCategory.tensorHomOf α (𝟙 (SimplexCategory.mk 0))

/-- The corresponding map of the actual large standard simplices. -/
def joinMap {m n : SimplexCategory} (α : m ⟶ n) :
    (Δ[m.len + 1] : SSet.{u}) ⟶ Δ[n.len + 1] :=
  SSet.stdSimplex.map (joinHom α)

/-- The chosen last-face inclusion is the ordinal-sum left inclusion. -/
theorem face_eq_inl (n : ℕ) :
    face.{u} n =
      SSet.stdSimplex.map
        (AugmentedSimplexCategory.inl' (SimplexCategory.mk n)
          (SimplexCategory.mk 0)) := by
  change SSet.stdSimplex.map (SimplexCategory.δ (Fin.last (n + 1))) = _
  congr 1
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  have h := AugmentedSimplexCategory.inl'_eval
    (SimplexCategory.mk n) (SimplexCategory.mk 0) i
  have hv : ((AugmentedSimplexCategory.inl'
      (SimplexCategory.mk n) (SimplexCategory.mk 0)).toOrderHom i).val = i.val := by
    simpa using congrArg Fin.val h
  apply Fin.ext
  calc
    ((SimplexCategory.δ (Fin.last (n + 1))).toOrderHom i).val = i.val := by
      simp [SimplexCategory.δ, Fin.succAbove_last]
    _ = _ := hv.symm

/-- The chosen last vertex is the ordinal-sum right inclusion. -/
theorem lastVertex_eq_inr (n : ℕ) :
    lastVertex.{u} n =
      SSet.stdSimplex.map
        (AugmentedSimplexCategory.inr' (SimplexCategory.mk n)
          (SimplexCategory.mk 0)) := by
  apply SSet.yonedaEquiv.injective
  change SSet.stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)) =
    SSet.stdSimplex.objEquiv.symm
      (AugmentedSimplexCategory.inr' (SimplexCategory.mk n)
        (SimplexCategory.mk 0))
  apply SSet.stdSimplex.obj₀Equiv.injective
  change Fin.last (n + 1) =
    (AugmentedSimplexCategory.inr' (SimplexCategory.mk n)
      (SimplexCategory.mk 0)).toOrderHom 0
  rw [AugmentedSimplexCategory.inr'_eval]
  apply Fin.ext
  rfl

/-- The large-simplex maps preserve the actual attaching faces. -/
theorem face_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    face.{u} m.len ≫ joinMap.{u} α =
      SSet.stdSimplex.map α ≫ face.{u} n.len := by
  rw [face_eq_inl, face_eq_inl]
  simp only [joinMap, ← Functor.map_comp]
  congr 1
  have h := AugmentedSimplexCategory.inl_comp_tensorHom
    (AugmentedSimplexCategory.inclusion.map α)
    (𝟙 (AugmentedSimplexCategory.inclusion.obj (SimplexCategory.mk 0)))
  change AugmentedSimplexCategory.inl' m (SimplexCategory.mk 0) ≫ joinHom α =
    α ≫ AugmentedSimplexCategory.inl' n (SimplexCategory.mk 0) at h
  exact h

/-- Collapsing the old face commutes with every simplex morphism. -/
theorem collapse_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    collapse.{u} m.len ≫ 𝟙 (Δ[0] : SSet.{u}) =
      SSet.stdSimplex.map α ≫ collapse.{u} n.len := by
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The actual pushout map induced by the ordinal-sum square. -/
def coneMap {m n : SimplexCategory} (α : m ⟶ n) :
    cone.{u} m.len ⟶ cone.{u} n.len :=
  pushout.map (face.{u} m.len) (collapse.{u} m.len)
    (face.{u} n.len) (collapse.{u} n.len)
    (joinMap.{u} α) (𝟙 (Δ[0] : SSet.{u})) (SSet.stdSimplex.map α)
    (face_naturality.{u} α) (collapse_naturality.{u} α)

/-- The large-simplex pushout leg is natural for the actual cone map. -/
theorem simplexIncl_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    simplexIncl.{u} m.len ≫ coneMap.{u} α =
      joinMap.{u} α ≫ simplexIncl.{u} n.len := by
  simp [simplexIncl, coneMap, pushout.map]

/-- The collapsed-face pushout leg is fixed by the actual cone map. -/
theorem baseIncl_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    baseIncl.{u} m.len ≫ coneMap.{u} α = baseIncl.{u} n.len := by
  simp [baseIncl, coneMap, pushout.map]

/-- Appending a final ordinal point respects identities. -/
theorem joinMap_id (m : SimplexCategory) :
    joinMap.{u} (𝟙 m) = 𝟙 (Δ[m.len + 1] : SSet.{u}) := by
  have h := AugmentedSimplexCategory.tensor_id
    (AugmentedSimplexCategory.inclusion.obj m)
    (AugmentedSimplexCategory.inclusion.obj (SimplexCategory.mk 0))
  change joinHom (𝟙 m) = 𝟙 (SimplexCategory.mk (m.len + 1)) at h
  simpa [joinMap] using congrArg SSet.stdSimplex.map h

/-- Appending a final ordinal point respects composition. -/
theorem joinMap_comp {m n p : SimplexCategory} (α : m ⟶ n) (β : n ⟶ p) :
    joinMap.{u} (α ≫ β) = joinMap.{u} α ≫ joinMap.{u} β := by
  have h := AugmentedSimplexCategory.tensorHom_comp_tensorHom
    (AugmentedSimplexCategory.inclusion.map α)
    (𝟙 (AugmentedSimplexCategory.inclusion.obj (SimplexCategory.mk 0)))
    (AugmentedSimplexCategory.inclusion.map β)
    (𝟙 (AugmentedSimplexCategory.inclusion.obj (SimplexCategory.mk 0)))
  change joinHom α ≫ joinHom β = joinHom (α ≫ β) at h
  rw [joinMap, joinMap, joinMap, ← SSet.stdSimplex.map_comp, h]

/-- The actual last vertex is preserved by the ordinal-sum maps. -/
theorem lastVertex_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    lastVertex.{u} m.len ≫ joinMap.{u} α = lastVertex.{u} n.len := by
  rw [lastVertex_eq_inr, lastVertex_eq_inr]
  simp only [joinMap, ← Functor.map_comp]
  congr 1
  have h := AugmentedSimplexCategory.inr_comp_tensorHom
    (AugmentedSimplexCategory.inclusion.map α)
    (𝟙 (AugmentedSimplexCategory.inclusion.obj (SimplexCategory.mk 0)))
  change AugmentedSimplexCategory.inr' m (SimplexCategory.mk 0) ≫ joinHom α =
    𝟙 (SimplexCategory.mk 0) ≫
      AugmentedSimplexCategory.inr' n (SimplexCategory.mk 0) at h
  simpa only [Category.id_comp] using h

/-- The original pushout cones form a cosimplicial object. -/
def coneFunctor : SimplexCategory ⥤ SSet.{u} where
  obj m := cone.{u} m.len
  map α := coneMap.{u} α
  map_id m := by
    apply pushout.hom_ext
    · change simplexIncl.{u} m.len ≫ coneMap.{u} (𝟙 m) =
        simplexIncl.{u} m.len ≫ 𝟙 (cone.{u} m.len)
      rw [simplexIncl_naturality, joinMap_id]
      simp only [Category.id_comp, Category.comp_id]
    · change baseIncl.{u} m.len ≫ coneMap.{u} (𝟙 m) =
        baseIncl.{u} m.len ≫ 𝟙 (cone.{u} m.len)
      rw [baseIncl_naturality]
      simp only [Category.comp_id]
  map_comp α β := by
    apply pushout.hom_ext
    · change simplexIncl.{u} _ ≫ coneMap.{u} (α ≫ β) =
        simplexIncl.{u} _ ≫ coneMap.{u} α ≫ coneMap.{u} β
      rw [simplexIncl_naturality, ← Category.assoc,
        simplexIncl_naturality, Category.assoc, simplexIncl_naturality,
        ← Category.assoc, ← joinMap_comp]
    · change baseIncl.{u} _ ≫ coneMap.{u} (α ≫ β) =
        baseIncl.{u} _ ≫ coneMap.{u} α ≫ coneMap.{u} β
      rw [baseIncl_naturality, ← Category.assoc,
        baseIncl_naturality, baseIncl_naturality]

/-- The collapsed formal endpoint is natural along the cone functor. -/
theorem alphaMap_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    alphaMap.{u} m.len ≫ coneFunctor.{u}.map α = alphaMap.{u} n.len :=
  baseIncl_naturality.{u} α

/-- The terminal formal endpoint is natural along the cone functor. -/
theorem omegaMap_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    omegaMap.{u} m.len ≫ coneFunctor.{u}.map α = omegaMap.{u} n.len := by
  change (lastVertex.{u} m.len ≫ simplexIncl.{u} m.len) ≫ coneMap.{u} α =
    lastVertex.{u} n.len ≫ simplexIncl.{u} n.len
  rw [Category.assoc, simplexIncl_naturality, ← Category.assoc,
    lastVertex_naturality]

end
end DaggerOriginalCounitRightConeFunctor
