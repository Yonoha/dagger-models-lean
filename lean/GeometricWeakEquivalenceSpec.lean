import Mathlib.AlgebraicTopology.SimplicialSet.RelativeMorphism
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.Data.Quot

/-! Mathlib-only geometric weak-equivalence specification.
Correspondence with the original definitions is proved in separate bridge modules. -/

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.GeometricWeakEquivalenceSpec

noncomputable section

abbrev Vertex (X : SSet.{u}) := X.obj (Opposite.op ⦋0⦌)

/-- A full simplicial edge with its source and target maps, in that order. -/
structure Edge (X : SSet.{u}) (x y : Vertex X) where
  map : (Δ[1] : SSet.{u}) ⟶ X
  source_eq : SSet.stdSimplex.δ (1 : Fin 2) ≫ map = SSet.const x
  target_eq : SSet.stdSimplex.δ (0 : Fin 2) ≫ map = SSet.const y

def Edge.pushforward {X Y : SSet.{u}} {x y : Vertex X}
    (p : Edge X x y) (f : X ⟶ Y) : Edge Y (f.app _ x) (f.app _ y) where
  map := p.map ≫ f
  source_eq := by rw [← Category.assoc, p.source_eq, SSet.const_comp]
  target_eq := by rw [← Category.assoc, p.target_eq, SSet.const_comp]

/-- The whole cylinder is stationary on the whole boundary, in every degree. -/
structure EdgeHomotopy {X : SSet.{u}} {x y : Vertex X} (p q : Edge X x y) where
  h : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X
  h₀ : SSet.ι₀ ≫ h = p.map
  h₁ : SSet.ι₁ ≫ h = q.map
  rel : (SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ h =
    fst _ _ ≫ (SSet.boundary 1).ι ≫ p.map

def EdgeHomotopy.pushforward {X Y : SSet.{u}} {x y : Vertex X}
    {p q : Edge X x y} (H : EdgeHomotopy p q) (f : X ⟶ Y) :
    EdgeHomotopy (p.pushforward f) (q.pushforward f) where
  h := H.h ≫ f
  h₀ := by rw [← Category.assoc, H.h₀]; rfl
  h₁ := by rw [← Category.assoc, H.h₁]; rfl
  rel := by
    dsimp [Edge.pushforward]
    rw [← Category.assoc, H.rel]
    simp only [Category.assoc]

def EdgeClass (X : SSet.{u}) (x y : Vertex X) : Type u :=
  Quot (fun p q : Edge X x y ↦ Nonempty (EdgeHomotopy p q))

def edgeMap {X Y : SSet.{u}} (f : X ⟶ Y) (x y : Vertex X) :
    EdgeClass X x y → EdgeClass Y (f.app _ x) (f.app _ y) :=
  Quot.map (fun p ↦ p.pushforward f) (fun _ _ ⟨H⟩ ↦ ⟨H.pushforward f⟩)

/-- Pointed relative homotopy classes; zero is included in the dimension. -/
def Pi (n : ℕ) (X : SSet.{u}) (x : Vertex X) : Type u :=
  SSet.RelativeMorphism.HomotopyClass
    (SSet.boundary n) (SSet.Subcomplex.ofSimplex x)
    (SSet.const ⟨x, SSet.Subcomplex.mem_ofSimplex_obj x⟩)

def mapPi {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
    (x : Vertex X) (y : Vertex Y) (h : f.app _ x = y) : Pi n X x → Pi n Y y :=
  fun p ↦ p.postcomp (.ofSimplex₀ f x y h) (by rw [SSet.comp_const])

/-- Full Hom bijectivity, essential surjectivity, and every pointed quotient map. -/
def kanW : MorphismProperty SSet.{u} := fun X Y f ↦
  ∃ (_ : SSet.KanComplex X) (_ : SSet.KanComplex Y),
    (∀ (x y : Vertex X), Function.Bijective (edgeMap f x y)) ∧
    (∀ y : Vertex Y, ∃ x : Vertex X, Nonempty (EdgeClass Y (f.app _ x) y)) ∧
    ∀ (n : ℕ) (x : Vertex X) (y : Vertex Y) (h : f.app _ x = y),
      Function.Bijective (mapPi f n x y h)

/-- Literal singular complex after literal geometric realization, on arbitrary inputs. -/
def geometricW : MorphismProperty SSet.{u} :=
  kanW.inverseImage (SSet.toTop ⋙ TopCat.toSSet)

end

end DaggerModels.GeometricWeakEquivalenceSpec
