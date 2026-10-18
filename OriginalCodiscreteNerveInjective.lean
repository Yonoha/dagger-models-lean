import OriginalSimplicialActionModelCategory
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.CodiscreteCategory

/-!
# Injectivity of the actual codiscrete nerve

Use the native codiscrete functor in every dimension. A monomorphism is injective
on vertices, so Function.extend extends their labels. Thin-nerve extensionality
proves full naturality and the full extension equation. No homogeneous Hom
universe assumption is imposed. Native lifting identifies the map to any terminal
target as a trivial fibration.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalCodiscreteNerveInjective
noncomputable section

/-- The literal original codiscrete nerve functor. -/
def codiscreteNerve : Type u ⥤ SSet.{u} := Codiscrete.functorToCat ⋙ nerveFunctor

/-- All original codiscrete Hom sets have at most one element. -/
instance codiscreteIsThin (T : Type u) : Quiver.IsThin (Codiscrete T) := by
  intro a b
  change Subsingleton Unit
  infer_instance

/-- The same thinness on Mathlib's bundled codiscrete category used by the nerve functor. -/
instance codiscreteCatIsThin (T : Type u) : Quiver.IsThin (Codiscrete.functorToCat.obj T) := by
  intro a b
  change Subsingleton Unit
  infer_instance

/-- A function on the original vertices determines a full codiscrete-nerve map. -/
def mapOfVertices {T : Type u} (X : SSet.{u}) (φ : X.obj (op ⦋0⦌) → T) :
    X ⟶ codiscreteNerve.obj T where
  app n s := Codiscrete.functor (fun j : Fin (n.unop.len + 1) ↦
    φ (X.map ((⦋0⦌ : SimplexCategory).const n.unop j).op s))
  naturality {n m} i := by
    funext s
    apply nerve.ext_of_isThin
    funext j
    apply Codiscrete.ext
    change φ (X.map ((⦋0⦌ : SimplexCategory).const m.unop j).op (X.map i s)) =
      φ (X.map ((⦋0⦌ : SimplexCategory).const n.unop (i.unop.toOrderHom j)).op s)
    rw [← FunctorToTypes.map_comp_apply]
    change φ (X.map (i.unop.op ≫ ((⦋0⦌ : SimplexCategory).const m.unop j).op) s) = _
    rw [← op_comp, SimplexCategory.const_comp]

/-- The unchanged labels of the original zero-simplices. -/
def vertexLabels {T : Type u} {X : SSet.{u}} (f : X ⟶ codiscreteNerve.obj T) :
    X.obj (op ⦋0⦌) → T := fun x ↦ (nerveEquiv (f.app (op ⦋0⦌) x)).as

/-- Naturality identifies each label with the corresponding vertex of every original simplex. -/
theorem vertexLabels_natural {T : Type u} {X : SSet.{u}}
    (f : X ⟶ codiscreteNerve.obj T) (n : SimplexCategoryᵒᵖ) (s : X.obj n)
    (j : Fin (n.unop.len + 1)) :
    vertexLabels f (X.map ((⦋0⦌ : SimplexCategory).const n.unop j).op s) =
      ((f.app n s).obj j).as := by
  have h := congrFun (f.naturality ((⦋0⦌ : SimplexCategory).const n.unop j).op) s
  have h' := congrArg (fun z : (nerve (Codiscrete T)).obj (op ⦋0⦌) ↦ (nerveEquiv z).as) h
  exact h'

/-- Native function extension supplies labels at all original target vertices. -/
def extendedLabels {T : Type u} [Nonempty T] {A B : SSet.{u}} (i : A ⟶ B)
    (f : A ⟶ codiscreteNerve.obj T) : B.obj (op ⦋0⦌) → T :=
  Function.extend (i.app (op ⦋0⦌)) (vertexLabels f)
    (fun _ ↦ Classical.choice (inferInstance : Nonempty T))

/-- Extend the original full nerve map using the native injective-function extension. -/
def extension {T : Type u} [Nonempty T] {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (f : A ⟶ codiscreteNerve.obj T) : B ⟶ codiscreteNerve.obj T :=
  mapOfVertices B (extendedLabels i f)

/-- The extension agrees with the entire original map in every dimension and operator. -/
theorem extension_spec {T : Type u} [Nonempty T] {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (f : A ⟶ codiscreteNerve.obj T) : i ≫ extension i f = f := by
  apply NatTrans.ext
  funext n s
  apply nerve.ext_of_isThin
  funext j
  apply Codiscrete.ext
  change extendedLabels i f
    (B.map ((⦋0⦌ : SimplexCategory).const n.unop j).op (i.app n s)) =
      ((f.app n s).obj j).as
  have hn : i.app (op ⦋0⦌)
      (A.map ((⦋0⦌ : SimplexCategory).const n.unop j).op s) =
      B.map ((⦋0⦌ : SimplexCategory).const n.unop j).op (i.app n s) :=
    congrFun (i.naturality ((⦋0⦌ : SimplexCategory).const n.unop j).op) s
  rw [← hn]
  have hi : Function.Injective (i.app (op ⦋0⦌)) :=
    (CategoryTheory.mono_iff_injective _).1 inferInstance
  change Function.extend (i.app (op ⦋0⦌)) (vertexLabels f)
    (fun _ ↦ Classical.choice (inferInstance : Nonempty T))
      (i.app (op ⦋0⦌) (A.map ((⦋0⦌ : SimplexCategory).const n.unop j).op s)) = _
  rw [hi.extend_apply]
  exact vertexLabels_natural f n s j

/-- The actual codiscrete nerve has trivial-fibration projection to any terminal target. -/
theorem toTerminal_trivialFibration {T : Type u} [Nonempty T] {Y : SSet.{u}}
    (p : codiscreteNerve.obj T ⟶ Y) (hY : IsTerminal Y) : trivialFibrations SSet.{u} p := by
  rw [← cofibrations_rlp]
  intro A B i hi
  have : Cofibration i := (cofibration_iff i).2 hi
  have : Mono i := inferInstance
  constructor
  intro f g sq
  exact CommSq.HasLift.mk'
    ⟨extension i f, extension_spec i f, hY.hom_ext _ _⟩

end
end DaggerOriginalCodiscreteNerveInjective
