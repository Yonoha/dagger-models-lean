import DaggerModels.DaggerGraphFiniteWords
import DaggerModels.DaggerGraphAccessibility
import DaggerModels.TypeFunctorPullback
import DaggerModels.TypeFunctorSigma
import DaggerModels.FreeSimplicialMap

/-!
# Finitarity of the original free word monad

For Part I `bg.lem.presentable`, each fixed path length is a finite iteration
of endpoint pullbacks, and all lengths form a disjoint sum. We identify these
functors with the actual free-category total edges and prove that the original
free/forgetful word endofunctor preserves all small filtered colimits.
-/

open CategoryTheory Limits

universe u

namespace DaggerModels.FreeWordFinitary

open DaggerGraphFiniteWords FreeSimplicialPaths

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- Finite composable words, functorial for arbitrary vertex and edge maps. -/
def stageFunctor (n : SimplexCategoryᵒᵖ) (k : ℕ) : DaggerSimplicialGraph.{u} ⥤ Type u where
  obj G := Word G n k
  map a := graphMap a n k
  map_id G := by funext w; exact graphMap_id G n k w
  map_comp a b := by funext w; exact graphMap_comp a b n k w

def source (n : SimplexCategoryᵒᵖ) (k : ℕ) :
    stageFunctor.{u} n k ⟶ DaggerGraphEvaluation.vertices where
  app G := (stage G n k).source
  naturality {G H} a := by funext w; exact graphMap_source a n k w

def target (n : SimplexCategoryᵒᵖ) (k : ℕ) :
    stageFunctor.{u} n k ⟶ DaggerGraphEvaluation.vertices where
  app G := (stage G n k).target
  naturality {G H} a := by funext w; exact graphMap_target a n k w

def zeroIso (n : SimplexCategoryᵒᵖ) :
    stageFunctor.{u} n 0 ≅ DaggerGraphEvaluation.vertices := Iso.refl _

def successorIso (n : SimplexCategoryᵒᵖ) (k : ℕ) :
    stageFunctor.{u} n (k + 1) ≅
      TypeFunctorPullback.functor (target n k) (DaggerGraphEvaluation.source n) :=
  Iso.refl _

/-- Each fixed length uses only finitely many endpoint pullbacks. -/
theorem stage_isCardinalAccessible (n : SimplexCategoryᵒᵖ) (k : ℕ) :
    (stageFunctor.{u} n k).IsCardinalAccessible Cardinal.aleph0.{u} := by
  letI := DaggerGraphEvaluation.vertices_preservesColimits.{u}
  letI := DaggerGraphEvaluation.edges_preservesColimits.{u} n
  induction k with
  | zero =>
    exact Functor.isCardinalAccessible_of_natIso (zeroIso n).symm Cardinal.aleph0
  | succ k ih =>
    letI := ih
    letI := TypeFunctorPullback.isCardinalAccessible
      (target n k) (DaggerGraphEvaluation.source n)
    exact Functor.isCardinalAccessible_of_natIso (successorIso n k).symm Cardinal.aleph0

/-- All finite lengths as an actual disjoint sum of composable words. -/
def words (n : SimplexCategoryᵒᵖ) : DaggerSimplicialGraph.{u} ⥤ Type u :=
  TypeFunctorSigma.functor (fun k : ℕ ↦ stageFunctor n k)

theorem words_isCardinalAccessible (n : SimplexCategoryᵒᵖ) :
    (words.{u} n).IsCardinalAccessible Cardinal.aleph0.{u} := by
  letI := stage_isCardinalAccessible.{u} n
  exact TypeFunctorSigma.isCardinalAccessible (fun k : ℕ ↦ stageFunctor n k)

/-- Forget the length label, which is uniquely determined by the actual path. -/
def lengthTotalEquiv (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) :
    (Σ k : ℕ, LengthPath G n k) ≃ (Σ x : G.Obj, Σ y : G.Obj, Path G n x y) where
  toFun w := ⟨w.2.1, w.2.2.1, w.2.2.2.val⟩
  invFun p := ⟨p.2.2.length, p.1, p.2.1, p.2.2, rfl⟩
  left_inv w := by
    rcases w with ⟨k, x, y, p, h⟩
    cases h
    rfl
  right_inv p := by rcases p with ⟨x, y, p⟩; rfl

/-- All finite composability fibers give exactly the original finite paths. -/
def wordsPathEquiv (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) :
    (words n).obj G ≃ (Σ x : G.Obj, Σ y : G.Obj, Path G n x y) :=
  (Equiv.sigmaCongrRight (fun k ↦ wordPathEquiv G n k)).trans (lengthTotalEquiv G n)

/-- The identified edges belong to the original free category, including its map action. -/
noncomputable def wordsIso (n : SimplexCategoryᵒᵖ) :
    words.{u} n ≅ (FreeDaggerSimplicialCategory.functor ⋙ DaggerSimplicialCat.forgetGraph) ⋙
      DaggerGraphEvaluation.edges n :=
  NatIso.ofComponents (fun G ↦ (wordsPathEquiv G n).toIso) (by
    intro G H a
    funext w
    rcases w with ⟨k, w⟩
    have h := congrArg
      (fun p : LengthPath H n k ↦ (⟨p.1, p.2.1, p.2.2.val⟩ :
        Σ x : H.Obj, Σ y : H.Obj, Path H n x y))
      (wordPathEquiv_graphMap a n k w)
    change wordsPathEquiv H n ⟨k, graphMap a n k w⟩ =
      ⟨a.obj ((wordPathEquiv G n k w).1), a.obj ((wordPathEquiv G n k w).2.1),
        ((FreeDaggerSimplicialCategory.functor.map a).map _ _).app n
          (wordPathEquiv G n k w).2.2.val⟩
    rw [FreeDaggerSimplicialCategory.functor_map_app]
    exact h)

/-- The actual word endofunctor leaves the vertices and arbitrary vertex maps unchanged. -/
noncomputable def verticesIso :
    (FreeDaggerSimplicialCategory.functor.{u} ⋙ DaggerSimplicialCat.forgetGraph) ⋙
      DaggerGraphEvaluation.vertices ≅ DaggerGraphEvaluation.vertices := Iso.refl _

/-- The original free/forgetful word endofunctor preserves every small filtered colimit. -/
theorem isCardinalAccessible :
    Functor.IsCardinalAccessible
      (FreeDaggerSimplicialCategory.functor.{u} ⋙ DaggerSimplicialCat.forgetGraph)
      Cardinal.aleph0.{u} := by
  letI := DaggerGraphEvaluation.vertices_preservesColimits.{u}
  letI := Functor.isCardinalAccessible_of_natIso verticesIso.symm Cardinal.aleph0.{u}
  letI : ∀ n,
      ((FreeDaggerSimplicialCategory.functor.{u} ⋙ DaggerSimplicialCat.forgetGraph) ⋙
        DaggerGraphEvaluation.edges n).IsCardinalAccessible Cardinal.aleph0.{u} := fun n ↦ by
    letI := words_isCardinalAccessible.{u} n
    exact Functor.isCardinalAccessible_of_natIso (wordsIso n) Cardinal.aleph0
  exact DaggerGraphEvaluation.isCardinalAccessible_of_evaluations _

end DaggerModels.FreeWordFinitary

namespace DaggerModels.DaggerSimplicialCat

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- The original forgetful functor has a left adjoint whose word endofunctor is finitary. -/
theorem exists_finitary_freeDaggerSimplicialCategoryAdjunction :
    ∃ F : DaggerSimplicialGraph.{u} ⥤ DaggerSimplicialCat.{u, u},
      Nonempty (F ⊣ forgetGraph) ∧
        (F ⋙ forgetGraph).IsCardinalAccessible Cardinal.aleph0.{u} :=
  ⟨FreeDaggerSimplicialCategory.functor, ⟨FreeDaggerSimplicialCategory.adjunction⟩,
    FreeWordFinitary.isCardinalAccessible⟩

end DaggerModels.DaggerSimplicialCat
