import GeometricWeakEquivalenceSpec
import TopCatModelCategory.SSet.HomotopyGroup
import Mathlib.Logic.Equiv.Defs

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.GeometricWeakEquivalenceSpec

noncomputable section

variable {X Y Z : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
  (φ : (A : SSet) ⟶ (B : SSet))

/-- Both directions retain the original relative simplicial map and boundary equation. -/
def relativeMapEquiv : SSet.Subcomplex.RelativeMorphism A B φ ≃
    SSet.RelativeMorphism A B φ where
  toFun p := ⟨p.map, p.comm⟩
  invFun p := ⟨p.map, p.comm⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma relativeMapEquiv_map (p : SSet.Subcomplex.RelativeMorphism A B φ) :
    (relativeMapEquiv A B φ p).map = p.map := rfl

/-- Full cylinder, both endpoints, and the entire relative stationarity equation. -/
def relativeHomotopyEquiv (p q : SSet.Subcomplex.RelativeMorphism A B φ) :
    SSet.Subcomplex.RelativeMorphism.Homotopy p q ≃
      SSet.RelativeMorphism.Homotopy (relativeMapEquiv A B φ p)
        (relativeMapEquiv A B φ q) where
  toFun H := ⟨H.h, H.h₀, H.h₁, H.rel⟩
  invFun H := ⟨H.h, H.h₀, H.h₁, H.rel⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equivalence of the actual relative homotopy quotients. -/
def relativeClassEquiv : SSet.Subcomplex.RelativeMorphism.HomotopyClass A B φ ≃
    SSet.RelativeMorphism.HomotopyClass A B φ :=
  Quot.congr (relativeMapEquiv A B φ) (fun p q ↦
    ⟨fun ⟨H⟩ ↦ ⟨relativeHomotopyEquiv A B φ p q H⟩,
      fun ⟨H⟩ ↦ ⟨(relativeHomotopyEquiv A B φ p q).symm H⟩⟩)

@[simp] lemma relativeClassEquiv_mk (p : SSet.Subcomplex.RelativeMorphism A B φ) :
    relativeClassEquiv A B φ p.homotopyClass =
      (relativeMapEquiv A B φ p).homotopyClass := rfl

variable {A B φ} {C : Z.Subcomplex} {ψ : (B : SSet) ⟶ (C : SSet)}

lemma relativeClassEquiv_postcomp
    (p : SSet.Subcomplex.RelativeMorphism.HomotopyClass A B φ)
    (f' : SSet.Subcomplex.RelativeMorphism B C ψ)
    {φψ : (A : SSet) ⟶ (C : SSet)} (fac : φ ≫ ψ = φψ) :
    relativeClassEquiv A C φψ (p.postcomp f' fac) =
      (relativeClassEquiv A B φ p).postcomp (relativeMapEquiv B C ψ f') fac := by
  induction p using Quot.induction_on with
  | h p => rfl

/-- Includes degree zero and every original source basepoint. -/
def pointedEquiv (n : ℕ) (X : SSet.{u}) (x : Vertex X) :
    SSet.KanComplex.π n X x ≃ Pi n X x :=
  relativeClassEquiv _ _ _

lemma pointedEquiv_map (f : X ⟶ Y) (n : ℕ) (x : Vertex X) (y : Vertex Y)
    (h : f.app _ x = y) (p : SSet.KanComplex.π n X x) :
    pointedEquiv n Y y (SSet.KanComplex.mapπ f n x y h p) =
      mapPi f n x y h (pointedEquiv n X x p) := by
  induction p using Quot.induction_on with
  | h p => rfl

end

end DaggerModels.GeometricWeakEquivalenceSpec
