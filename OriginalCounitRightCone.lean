import OriginalCounitObjects
import OriginalEnrichedHomTransport
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# The actual right cone and the original counit evaluation

The cone is a pushout of standard simplices. Its two formal vertices are kept
even when a map to a coherent nerve sends them to the same target object.
The enriched comparison is the original adjunction counit, with both dependent
Hom endpoints transported explicitly.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerModels DaggerOriginalEnrichedHomTransport
open DaggerModels.OrdinaryRigidification
open DaggerChosenRigidificationNecklace

universe u

namespace DaggerOriginalCounitRightCone

noncomputable section

private abbrev C := OrdinaryRigidification.rigidification.{u}
private abbrev N := OrdinaryRigidification.coherentNerve.{u}
private abbrev A := OrdinaryRigidification.rigidificationCoherentNerveAdjunction.{u}

/-- The last face includes the first `n + 1` vertices of `Δ[n + 1]`. -/
def face (n : ℕ) : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1] :=
  SSet.stdSimplex.δ (Fin.last (n + 1))

/-- Collapse the first face to the terminal standard simplex. -/
def collapse (n : ℕ) : (Δ[n] : SSet.{u}) ⟶ Δ[0] :=
  SSet.stdSimplex.isTerminalObj₀.from _

/-- The actual right cone `Δ[n + 1] ⨿_{Δ[n]} Δ[0]`. -/
def cone (n : ℕ) : SSet.{u} := pushout (face.{u} n) (collapse.{u} n)

/-- The large-simplex inclusion into the pushout. -/
def simplexIncl (n : ℕ) : (Δ[n + 1] : SSet.{u}) ⟶ cone.{u} n :=
  pushout.inl (face.{u} n) (collapse.{u} n)

/-- The collapsed-face inclusion into the pushout. -/
def baseIncl (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ cone.{u} n :=
  pushout.inr (face.{u} n) (collapse.{u} n)

/-- The actual pushout equation on the attaching face. -/
theorem face_eq_collapse (n : ℕ) :
    face.{u} n ≫ simplexIncl.{u} n = collapse.{u} n ≫ baseIncl.{u} n :=
  pushout.condition (f := face.{u} n) (g := collapse.{u} n)

/-- The last vertex of the large simplex, as a map from `Δ[0]`. -/
def lastVertex (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[n + 1] :=
  SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)))

/-- The collapsed formal endpoint of the actual cone. -/
def alphaMap (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ cone.{u} n := baseIncl.{u} n

/-- The terminal formal endpoint of the actual cone. -/
def omegaMap (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ cone.{u} n :=
  lastVertex.{u} n ≫ simplexIncl.{u} n

def alpha (n : ℕ) : (cone.{u} n).obj (op ⦋0⦌) :=
  (alphaMap.{u} n).app (op ⦋0⦌)
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))

def omega (n : ℕ) : (cone.{u} n).obj (op ⦋0⦌) :=
  (omegaMap.{u} n).app (op ⦋0⦌)
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))

/-- A map out of the cone is the actual pushout descent of compatible data. -/
def desc {X : SSet.{u}} (n : ℕ)
    (f : (Δ[n + 1] : SSet.{u}) ⟶ X) (g : (Δ[0] : SSet.{u}) ⟶ X)
    (h : face.{u} n ≫ f = collapse.{u} n ≫ g) : cone.{u} n ⟶ X :=
  pushout.desc f g h

theorem simplexIncl_desc {X : SSet.{u}} (n : ℕ)
    (f : (Δ[n + 1] : SSet.{u}) ⟶ X) (g : (Δ[0] : SSet.{u}) ⟶ X)
    (h : face.{u} n ≫ f = collapse.{u} n ≫ g) :
    simplexIncl.{u} n ≫ desc.{u} n f g h = f :=
  pushout.inl_desc (f := face.{u} n) (g := collapse.{u} n) f g h

theorem baseIncl_desc {X : SSet.{u}} (n : ℕ)
    (f : (Δ[n + 1] : SSet.{u}) ⟶ X) (g : (Δ[0] : SSet.{u}) ⟶ X)
    (h : face.{u} n ≫ f = collapse.{u} n ≫ g) :
    baseIncl.{u} n ≫ desc.{u} n f g h = g :=
  pushout.inr_desc (f := face.{u} n) (g := collapse.{u} n) f g h

/-- The original rigidification objects of the two actual cone endpoints. -/
def alphaObj (n : ℕ) : (C.obj (cone.{u} n)).Obj :=
  RigidificationVertices.vertexEquiv (cone.{u} n) (alpha.{u} n)

def omegaObj (n : ℕ) : (C.obj (cone.{u} n)).Obj :=
  RigidificationVertices.vertexEquiv (cone.{u} n) (omega.{u} n)

/-- The same original left adjoint and the same original counit, for every cone simplex. -/
theorem evaluation_functor (D : SimplicialCat.{u, u}) (n : ℕ)
    (σ : cone.{u} n ⟶ N.obj D) :
    C.map σ ≫ A.counit.app D = (A.homEquiv (cone.{u} n) D).symm σ :=
  (A.homEquiv_counit (g := σ)).symm

/-- The left target endpoint is the original coherent-nerve vertex value. -/
theorem evaluation_alpha_obj (D : SimplicialCat.{u, u}) (n : ℕ)
    (σ : cone.{u} n ⟶ N.obj D) :
    (A.counit.app D).obj ((C.map σ).obj (alphaObj.{u} n)) =
      NerveVertices.vertexEquiv D (σ.app (op ⦋0⦌) (alpha.{u} n)) := by
  rw [alphaObj, RigidificationVertices.vertexEquiv_naturality σ (alpha.{u} n)]
  exact DaggerOriginalCounitObjects.counit_obj_vertex D _

/-- The right target endpoint is the original coherent-nerve vertex value. -/
theorem evaluation_omega_obj (D : SimplicialCat.{u, u}) (n : ℕ)
    (σ : cone.{u} n ⟶ N.obj D) :
    (A.counit.app D).obj ((C.map σ).obj (omegaObj.{u} n)) =
      NerveVertices.vertexEquiv D (σ.app (op ⦋0⦌) (omega.{u} n)) := by
  rw [omegaObj, RigidificationVertices.vertexEquiv_naturality σ (omega.{u} n)]
  exact DaggerOriginalCounitObjects.counit_obj_vertex D _

/-- The source for the next `Qⁿ` comparison is this exact original Hom. -/
def Q (n : ℕ) : SSet.{u} :=
  (C.obj (cone.{u} n)).enriched.Hom (alphaObj.{u} n) (omegaObj.{u} n)

/-- The original evaluation, including both endpoint transports to the values of `σ`. -/
def evaluation (D : SimplicialCat.{u, u}) (n : ℕ)
    (σ : cone.{u} n ⟶ N.obj D) :
    Q.{u} n ⟶ D.enriched.Hom
      (NerveVertices.vertexEquiv D (σ.app (op ⦋0⦌) (alpha.{u} n)))
      (NerveVertices.vertexEquiv D (σ.app (op ⦋0⦌) (omega.{u} n))) :=
  (C.map σ).map (alphaObj.{u} n) (omegaObj.{u} n) ≫
    (A.counit.app D).map _ _ ≫
      targetHomTransport (evaluation_alpha_obj.{u} D n σ) (evaluation_omega_obj.{u} D n σ)

/-- Whole-functor equality gives the full dependent Hom equality, with both casts. -/
theorem evaluation_hom (D : SimplicialCat.{u, u}) (n : ℕ)
    (σ : cone.{u} n ⟶ N.obj D) :
    (C.map σ ≫ A.counit.app D).map (alphaObj.{u} n) (omegaObj.{u} n) ≫
        targetHomTransport
          (functorObjEq (evaluation_functor.{u} D n σ) (alphaObj.{u} n))
          (functorObjEq (evaluation_functor.{u} D n σ) (omegaObj.{u} n)) =
      ((A.homEquiv (cone.{u} n) D).symm σ).map (alphaObj.{u} n) (omegaObj.{u} n) :=
  functorHomEq (evaluation_functor.{u} D n σ) (alphaObj.{u} n) (omegaObj.{u} n)

end

end DaggerOriginalCounitRightCone
