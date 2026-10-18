import NativeSSetCoproductHomotopy
import OriginalSimplicialCategoryGroupoidHomTransport
import OriginalSimplicialCategoryWholeBarFibreIso

/-!
# Original vertex transport on the entire original Hom coproduct

Keep every original endpoint. Native coproduct homotopies assemble the actual
original Hom precomposition maps before realization. Original component
relations then give homotopies of the whole maps with Kan target.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialCategoryBarCoproductDegrees
open DaggerNativeSSetCoproductHomotopy
open DaggerOriginalSimplicialCategoryVertexComposition
open DaggerOriginalSimplicialCategoryVertexEdgeHomotopy
open DaggerOriginalSimplicialCategoryWholeBarFibreIso
universe u
namespace DaggerOriginalSimplicialCategoryWholeHomTransport
noncomputable section

/-- Original precomposition keeps every original endpoint in the whole original Hom coproduct. -/
def wholeHomPrecompose (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    originalHomSum C y ⟶ originalHomSum C x :=
  Limits.Sigma.map (fun z ↦ precomposeVertex C a z)

/-- Whole original transport acts by exactly the original precomposition on each component. -/
theorem wholeHomPrecompose_apply (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) (n : SimplexCategoryᵒᵖ) (z : C.Obj)
    (b : (C.enriched.Hom y z).obj n) :
    (wholeHomPrecompose C a).app n
        (coproductDegreeEquiv (fun z ↦ C.enriched.Hom y z) n ⟨z, b⟩) =
      coproductDegreeEquiv (fun z ↦ C.enriched.Hom x z) n
        ⟨z, (precomposeVertex C a z).app n b⟩ :=
  coproductMap_apply (fun z ↦ precomposeVertex C a z) n z b

/-- The whole original identity transport is the identity on the entire original Hom sum. -/
theorem wholeHomPrecompose_id (C : SimplicialCat.{u, u}) (x : C.Obj) :
    wholeHomPrecompose C ((C.enriched.id x).app (op ⦋0⦌) PUnit.unit) =
      𝟙 (originalHomSum C x) := by
  simp only [wholeHomPrecompose, precomposeVertex_id, Sigma.map_id]
  rfl

/-- Whole original transport retains the full original vertex composition. -/
theorem wholeHomPrecompose_comp (C : SimplicialCat.{u, u}) {w x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌))
    (b : (C.enriched.Hom w x).obj (op ⦋0⦌)) :
    wholeHomPrecompose C a ≫ wholeHomPrecompose C b =
      wholeHomPrecompose C ((C.enriched.comp w x y).app (op ⦋0⦌) (b, a)) := by
  change Limits.Sigma.map (fun z ↦ precomposeVertex C a z) ≫
      Limits.Sigma.map (fun z ↦ precomposeVertex C b z) = _
  rw [Sigma.map_comp_map]
  exact congrArg (fun f ↦ Limits.Sigma.map f) (funext (fun z ↦ precomposeVertex_comp C a b z))

/-- Each original vertex edge gives a homotopy of the whole original endpoint-preserving maps. -/
def wholeHomPrecomposeEdgeHomotopy (C : SimplicialCat.{u, u}) {x y : C.Obj}
    {a b : (C.enriched.Hom x y).obj (op ⦋0⦌)} (e : SSet.Edge a b) :
    SSet.Homotopy (wholeHomPrecompose C a) (wholeHomPrecompose C b) :=
  coproductHomotopy (fun z ↦ precomposeVertexEdgeHomotopy C e z)

/-- Original component equality controls the entire original Hom sum after realization. -/
theorem wholeHomPrecompose_componentHomotopy (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a b : (C.enriched.Hom x y).obj (op ⦋0⦌)) (h : SSet.π₀.mk a = SSet.π₀.mk b) :
    Nonempty (SSet.Homotopy (DaggerNerveHomotopy.R.map (wholeHomPrecompose C a))
      (DaggerNerveHomotopy.R.map (wholeHomPrecompose C b))) := by
  have he : Relation.EqvGen (@SSet.π₀Rel (C.enriched.Hom x y)) a b := Quot.eq.mp h
  clear h
  induction he with
  | rel a b h =>
      obtain ⟨e, h₀, h₁⟩ := h
      exact ⟨(wholeHomPrecomposeEdgeHomotopy C ⟨e, h₀, h₁⟩).toTop.toSSet⟩
  | refl a =>
      exact ⟨SSet.Subcomplex.RelativeMorphism.Homotopy.ofEq rfl⟩
  | symm a b _ ih =>
      obtain ⟨h⟩ := ih
      exact ⟨SSet.Subcomplex.RelativeMorphism.Homotopy.symm h⟩
  | trans a b c _ _ ih₁ ih₂ =>
      obtain ⟨h₁⟩ := ih₁
      obtain ⟨h₂⟩ := ih₂
      exact ⟨SSet.Homotopy.trans h₁ h₂⟩

end
end DaggerOriginalSimplicialCategoryWholeHomTransport
