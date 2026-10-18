import DaggerModels.OrdinaryRigidification
import DaggerModels.NerveVertices
import DaggerModels.SSetBoundaryCells
import IinjBridge
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace DaggerOrdinaryRigidificationCof

noncomputable section

abbrev SC := DaggerModels.SimplicialCat.{u, u}
abbrev C := DaggerModels.OrdinaryRigidification.rigidification.{u}
abbrev N := DaggerModels.OrdinaryRigidification.coherentNerve.{u}
abbrev T := DaggerModels.OrdinaryRigidification.cosimplicialThickening.{u}

def geometric {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map f))

def ordinaryTrivialFibrations : MorphismProperty SC.{u} := fun _ _ p =>
  Function.Surjective p.obj ∧ ∀ x y, Fibration (p.map x y) ∧ geometric (p.map x y)

def ordinaryCofibrations : MorphismProperty SC.{u} := ordinaryTrivialFibrations.llp

theorem scalar_iff_rlp {X Y : SSet.{u}} (p : X ⟶ Y) :
    (Fibration p ∧ geometric p) ↔ SSet.modelCategoryQuillen.I.rlp p := by
  rw [← DaggerModels.KanQuillenReuse.boundary_lifting_iff_rlp,
    DaggerModels.KanQuillenReuse.boundary_lifting_iff_trivial,
    DaggerModels.KanQuillenReuse.weakEquivalence_iff_geometric]
  rfl

theorem scalar_lifting {X Y K L : SSet.{u}} (p : X ⟶ Y) (i : K ⟶ L)
    (hp : Fibration p) (hw : geometric p) [Mono i] : HasLiftingProperty i p := by
  have h := (scalar_iff_rlp p).mp ⟨hp, hw⟩
  rw [DaggerModels.SSetBoundaryCells.I_rlp_eq_monomorphisms_rlp] at h
  exact h i (show Mono i from inferInstance)

namespace BoundaryData

variable {A B : SC.{u}} {n : SimplexCategory}

/-- Every proper ordinal simplex is evaluated in the SAME supplied boundary map. -/
def simplex (a : (SSet.boundary n.len).toSSet ⟶ N.obj A)
    {m : SimplexCategory} (φ : m ⟶ n) (hφ : ¬ Function.Surjective φ.toOrderHom) :
    T.obj m ⟶ A :=
  (a.app (op m) ⟨SSet.stdSimplex.objEquiv.symm φ, hφ⟩).down

theorem simplex_precompose (a : (SSet.boundary n.len).toSSet ⟶ N.obj A)
    {m l : SimplexCategory} (φ : m ⟶ n) (hφ : ¬ Function.Surjective φ.toOrderHom)
    (ψ : l ⟶ m) :
    T.map ψ ≫ simplex a φ hφ =
      simplex a (ψ ≫ φ) (fun h => hφ (Function.Surjective.of_comp h)) := by
  have h := congrFun (a.naturality ψ.op) ⟨SSet.stdSimplex.objEquiv.symm φ, hφ⟩
  exact (congrArg ULift.down h).symm

/-- The original top simplex, including its full enriched maps. -/
def top (b : SSet.stdSimplex.obj n ⟶ N.obj B) : T.obj n ⟶ B :=
  (SSet.yonedaEquiv b).down

theorem simplex_over (a : (SSet.boundary n.len).toSSet ⟶ N.obj A)
    (b : SSet.stdSimplex.obj n ⟶ N.obj B) (p : A ⟶ B)
    (sq : CommSq a (SSet.boundary n.len).ι (N.map p) b)
    {m : SimplexCategory} (φ : m ⟶ n) (hφ : ¬ Function.Surjective φ.toOrderHom) :
    simplex a φ hφ ≫ p = T.map φ ≫ top b := by
  have h := congrFun (congrArg (fun f => f.app (op m)) sq.w)
    ⟨SSet.stdSimplex.objEquiv.symm φ, hφ⟩
  have hb : b.app (op m) (SSet.stdSimplex.objEquiv.symm φ) =
      (N.obj B).map φ.op (SSet.yonedaEquiv b) := by
    conv_lhs => rw [← SSet.yonedaEquiv.symm_apply_apply b]
    rfl
  exact (congrArg ULift.down h).trans (congrArg ULift.down hb)

end BoundaryData

end

end DaggerOrdinaryRigidificationCof
