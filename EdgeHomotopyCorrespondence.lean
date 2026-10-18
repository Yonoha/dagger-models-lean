import RelativeHomotopyCorrespondence
import TopCatModelCategory.SSet.FundamentalGroupoid

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.GeometricWeakEquivalenceSpec

noncomputable section

variable (X : SSet.{u}) (x y : Vertex X)

/-- The inverse is the original boundary-one construction, with the same full edge map. -/
def edgeEquiv : SSet.KanComplex.FundamentalGroupoid.Edge
    (SSet.KanComplex.FundamentalGroupoid.objEquiv.symm x)
    (SSet.KanComplex.FundamentalGroupoid.objEquiv.symm y) ≃ Edge X x y where
  toFun p := ⟨p.map, p.comm₀, p.comm₁⟩
  invFun p := SSet.KanComplex.FundamentalGroupoid.Edge.mk p.map p.source_eq p.target_eq
  left_inv p := by apply SSet.KanComplex.FundamentalGroupoid.Edge.ext; rfl
  right_inv p := by cases p; rfl

@[simp] lemma edgeEquiv_map (p : SSet.KanComplex.FundamentalGroupoid.Edge
    (SSet.KanComplex.FundamentalGroupoid.objEquiv.symm x)
    (SSet.KanComplex.FundamentalGroupoid.objEquiv.symm y)) :
    (edgeEquiv X x y p).map = p.map := rfl

/-- Stationarity on the entire boundary is retained, not just its vertices. -/
def edgeHomotopyEquiv
    (p q : SSet.KanComplex.FundamentalGroupoid.Edge
      (SSet.KanComplex.FundamentalGroupoid.objEquiv.symm x)
      (SSet.KanComplex.FundamentalGroupoid.objEquiv.symm y)) :
    SSet.Subcomplex.RelativeMorphism.Homotopy p q ≃
      EdgeHomotopy (edgeEquiv X x y p) (edgeEquiv X x y q) where
  toFun H :=
    { h := H.h
      h₀ := H.h₀
      h₁ := H.h₁
      rel := by
        change _ = fst _ _ ≫ (SSet.boundary 1).ι ≫ p.map
        rw [p.comm]
        exact H.rel }
  invFun H :=
    { h := H.h
      h₀ := H.h₀
      h₁ := H.h₁
      rel := by
        rw [← p.comm]
        exact H.rel }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Full equivalence of the existing groupoid Hom quotient and the explicit edge quotient. -/
def edgeClassEquiv : SSet.KanComplex.FundamentalGroupoid.Hom
    (SSet.KanComplex.FundamentalGroupoid.objEquiv.symm x)
    (SSet.KanComplex.FundamentalGroupoid.objEquiv.symm y) ≃ EdgeClass X x y :=
  Quot.congr (edgeEquiv X x y) (fun p q ↦
    ⟨fun ⟨H⟩ ↦ ⟨edgeHomotopyEquiv X x y p q H⟩,
      fun ⟨H⟩ ↦ ⟨(edgeHomotopyEquiv X x y p q).symm H⟩⟩)

@[simp] lemma edgeClassEquiv_mk (p : SSet.KanComplex.FundamentalGroupoid.Edge
    (SSet.KanComplex.FundamentalGroupoid.objEquiv.symm x)
    (SSet.KanComplex.FundamentalGroupoid.objEquiv.symm y)) :
    edgeClassEquiv X x y p.homotopyClass =
      Quot.mk _ (edgeEquiv X x y p) := rfl

variable {X} {Y : SSet.{u}}

lemma edgeClassEquiv_map (f : X ⟶ Y) (x y : Vertex X)
    (p : SSet.KanComplex.FundamentalGroupoid.Hom
      (SSet.KanComplex.FundamentalGroupoid.objEquiv.symm x)
      (SSet.KanComplex.FundamentalGroupoid.objEquiv.symm y)) :
    edgeClassEquiv Y (f.app _ x) (f.app _ y) (p.map f) =
      edgeMap f x y (edgeClassEquiv X x y p) := by
  induction p using Quot.induction_on with
  | h p => rfl

end

end DaggerModels.GeometricWeakEquivalenceSpec
