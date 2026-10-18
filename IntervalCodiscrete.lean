import ChosenNecklaceMapVertices
import Mathlib.CategoryTheory.CodiscreteCategory

open CategoryTheory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerIntervalNecklaceCompletion

noncomputable section

abbrev IntervalCategory := Codiscrete (ULift.{u} Bool)

/-- The literal nerve of the original codiscrete category with Unit Hom. -/
abbrev E : SSet.{u} := nerve (IntervalCategory.{u})

instance interval_isThin : Quiver.IsThin (IntervalCategory.{u}) := by
  intro x y
  change Subsingleton Unit
  infer_instance

def endpoint (b : Bool) : (E.{u}).obj (op ⦋0⦌) :=
  nerveEquiv.symm (Codiscrete.mk (ULift.up b))

def endpointMap (b : Bool) : 𝟙_ SSet.{u} ⟶ E.{u} := SSet.const (endpoint b)

theorem interval_hom (x y : IntervalCategory.{u}) : (x ⟶ y) = Unit := rfl

theorem vertex_naturality {X : SSet.{u}} (f : X ⟶ E.{u}) {n : ℕ}
    (x : X.obj (op ⦋n⦌)) (i : Fin (n + 1)) :
    (f.app _ x).obj i =
      nerveEquiv (f.app _ (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op x)) := by
  have h := congrFun (f.naturality (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op) x
  exact (congrArg nerveEquiv h).symm

/-- Whole simplicial maps to this nerve are determined by their zero simplices. -/
theorem hom_ext_vertices {X : SSet.{u}} (f g : X ⟶ E.{u})
    (h : ∀ x : X.obj (op ⦋0⦌), f.app _ x = g.app _ x) : f = g := by
  apply NatTrans.ext
  funext q x
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ n
  apply nerve.ext_of_isThin
  funext i
  rw [vertex_naturality, vertex_naturality]
  exact congrArg nerveEquiv (h _)

open DaggerChosenRigidificationNecklace NecklaceCode

def vertexWord (T : NecklaceCode) (p : T.toSSet ⟶ E.{u})
    (k : Fin (T.len + 1)) : IntervalCategory.{u} :=
  nerveEquiv (p.app _ (T.verticesEquiv.symm (ULift.up k)))

/-- Every vertex word extends using the original codiscrete Unit arrows. -/
def completionSimplex (T : NecklaceCode) (p : T.toSSet ⟶ E.{u}) :
    ComposableArrows (IntervalCategory.{u}) T.len :=
  Codiscrete.functor (fun k ↦ (vertexWord T p k).as)

theorem completionSimplex_obj (T : NecklaceCode) (p : T.toSSet ⟶ E.{u})
    (k : Fin (T.len + 1)) : (completionSimplex T p).obj k = vertexWord T p k := rfl

def completeMap (T : NecklaceCode) (p : T.toSSet ⟶ E.{u}) : Δ[T.len] ⟶ E.{u} :=
  SSet.yonedaEquiv.symm (completionSimplex T p)

theorem completeMap_app_obj (T : NecklaceCode) (p : T.toSSet ⟶ E.{u}) {n : ℕ}
    (x : (Δ[T.len] : SSet.{u}).obj (op ⦋n⦌)) (i : Fin (n + 1)) :
    ((completeMap T p).app _ x).obj i = vertexWord T p (x i) := rfl

theorem completeMap_operator (T : NecklaceCode) (p : T.toSSet ⟶ E.{u})
    {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) (x : (Δ[T.len] : SSet.{u}).obj q) :
    (E.{u}).map α ((completeMap T p).app q x) =
      (completeMap T p).app r ((Δ[T.len] : SSet.{u}).map α x) :=
  (congrFun ((completeMap T p).naturality α) x).symm

theorem completeMap_vertex (T : NecklaceCode) (p : T.toSSet ⟶ E.{u})
    (k : Fin (T.len + 1)) :
    (completeMap T p).app _ (SSet.stdSimplex.obj₀Equiv.symm k) =
      p.app _ (T.verticesEquiv.symm (ULift.up k)) := by
  apply nerveEquiv.injective
  rfl

/-- The same original union inclusion gives the full extension triangle. -/
theorem inclusion_completeMap (T : NecklaceCode) (p : T.toSSet ⟶ E.{u}) :
    T.inclusion ≫ completeMap T p = p := by
  apply hom_ext_vertices
  intro x
  apply nerveEquiv.injective
  change vertexWord T p (SSet.stdSimplex.obj₀Equiv (T.inclusion.app _ x)) = _
  rw [← T.verticesEquiv_down]
  dsimp only [vertexWord]
  have hx : ULift.up (T.verticesEquiv x).down = T.verticesEquiv x := rfl
  rw [hx, T.verticesEquiv.symm_apply_apply]
  rfl

/-- Uniqueness is for the entire SSet map, including every operator. -/
theorem completeMap_unique (T : NecklaceCode) (p : T.toSSet ⟶ E.{u})
    (f : (Δ[T.len] : SSet.{u}) ⟶ E.{u}) (hf : T.inclusion ≫ f = p) :
    f = completeMap T p := by
  apply hom_ext_vertices
  intro x
  obtain ⟨k, rfl⟩ := SSet.stdSimplex.obj₀Equiv.symm.surjective x
  have hv : T.inclusion.app _ (T.verticesEquiv.symm (ULift.up k)) =
      SSet.stdSimplex.obj₀Equiv.symm k := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    exact T.inclusion_vertex (ULift.up k)
  have h := congrFun (NatTrans.congr_app hf (op ⦋0⦌))
    (T.verticesEquiv.symm (ULift.up k))
  change f.app _ (T.inclusion.app _ _) = p.app _ _ at h
  rw [hv] at h
  exact h.trans (completeMap_vertex T p k).symm

end

end DaggerIntervalNecklaceCompletion
