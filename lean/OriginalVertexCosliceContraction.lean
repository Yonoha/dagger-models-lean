import OriginalCosliceContractionOperators
import OriginalLeftMappingVertices
import TopCatModelCategory.SSet.Contractible

/-!
# Contraction of the actual original vertex coslice

The original vertex coslice is contracted onto the original identity-edge
vertex. The cylinder map is built from the native ordinal operators, with
their prefix and naturality identities. No Kan hypothesis is needed for
this contraction, and neither the source simplicial set nor its projection
is replaced by another model.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory
open DaggerOriginalOrdinalJoinLeft DaggerOriginalSimplexCoslice
open DaggerOriginalCosliceContractionOperators DaggerOriginalLeftMappingVertices

universe u

namespace DaggerOriginalVertexCosliceContraction

noncomputable section

/-- Contravariant evaluation of an exact composite simplex operator. -/
theorem map_comp_op_apply (X : SSet.{u}) {a b c : SimplexCategory}
    (f : a ⟶ b) (g : b ⟶ c) (s : X.obj (op c)) :
    X.map f.op (X.map g.op s) = X.map (f ≫ g).op s :=
  (congrFun (X.map_comp g.op f.op) s).symm

/-- The actual constant joined edge at the original vertex. -/
def coslicePoint (X : SSet.{u}) (x : X.obj (op ⦋0⦌)) :
    (simplexCoslice ⦋0⦌ X x).obj (op ⦋0⦌) :=
  ⟨X.map (((ordinalJoinLeft ⦋0⦌).obj ⦋0⦌).const ⦋0⦌ 0).op x, by
    change X.map (AugmentedSimplexCategory.inl' ⦋0⦌ ⦋0⦌).op
      (X.map (((ordinalJoinLeft ⦋0⦌).obj ⦋0⦌).const ⦋0⦌ 0).op x) = x
    rw [map_comp_op_apply]
    have h : AugmentedSimplexCategory.inl' ⦋0⦌ ⦋0⦌ ≫
        ((ordinalJoinLeft ⦋0⦌).obj ⦋0⦌).const ⦋0⦌ 0 = 𝟙 ⦋0⦌ :=
      Subsingleton.elim _ _
    rw [h, op_id, X.map_id]
    rfl⟩

/-- This contraction point is the vertex of the same original identity edge. -/
theorem coslicePoint_eq_identity_edge (X : SSet.{u}) (x : X.obj (op ⦋0⦌)) :
    coslicePoint X x = (edgeVertex X x x (SSet.Edge.id x)).val := by
  apply Subtype.ext
  change X.map (((ordinalJoinLeft ⦋0⦌).obj ⦋0⦌).const ⦋0⦌ 0).op x =
    X.map (SimplexCategory.σ (0 : Fin 1)).op x
  have h : ((ordinalJoinLeft ⦋0⦌).obj ⦋0⦌).const ⦋0⦌ 0 =
      SimplexCategory.σ (0 : Fin 1) := Subsingleton.elim _ _
  rw [h]

/-- The zero contraction operator factors through the exact original prefix. -/
theorem contractionOperator_zero_factor (n : SimplexCategory) :
    contractionOperator n (n.const ⦋1⦌ 0) =
      ((ordinalJoinLeft ⦋0⦌).obj n).const ⦋0⦌ 0 ≫
        AugmentedSimplexCategory.inl' ⦋0⦌ n := by
  rw [contractionOperator_const_zero]
  rw [SimplexCategory.const_comp]
  congr 1
  apply Fin.ext
  rw [AugmentedSimplexCategory.inl'_eval]
  rfl

/-- Apply the exact contraction operator to an original joined simplex. -/
def contraction (X : SSet.{u}) (x : X.obj (op ⦋0⦌)) :
    simplexCoslice ⦋0⦌ X x ⊗ Δ[1] ⟶ simplexCoslice ⦋0⦌ X x where
  app n st := ⟨X.map (contractionOperator n.unop (SSet.stdSimplex.objEquiv st.2)).op
      st.1.val, by
    change X.map (AugmentedSimplexCategory.inl' ⦋0⦌ n.unop).op
      (X.map (contractionOperator n.unop (SSet.stdSimplex.objEquiv st.2)).op st.1.val) = x
    rw [map_comp_op_apply, prefix_comp_contractionOperator]
    exact st.1.property⟩
  naturality a b φ := by
    funext st
    apply Subtype.ext
    change X.map (contractionOperator b.unop
        (φ.unop ≫ SSet.stdSimplex.objEquiv st.2)).op
        (X.map ((ordinalJoinLeft ⦋0⦌).map φ.unop).op st.1.val) =
      X.map ((ordinalJoinLeft ⦋0⦌).map φ.unop).op
        (X.map (contractionOperator a.unop (SSet.stdSimplex.objEquiv st.2)).op st.1.val)
    rw [map_comp_op_apply, map_comp_op_apply, ← contractionOperator_naturality]

/-- The zero endpoint is the constant map at the actual identity-edge vertex. -/
theorem contraction_zero (X : SSet.{u}) (x : X.obj (op ⦋0⦌)) :
    SSet.ι₀ ≫ contraction X x = SSet.const (coslicePoint X x) := by
  ext n s : 2
  apply Subtype.ext
  change X.map (contractionOperator n.unop (n.unop.const ⦋1⦌ 0)).op s.val =
    X.map ((ordinalJoinLeft ⦋0⦌).map (n.unop.const ⦋0⦌ 0)).op
      (X.map (((ordinalJoinLeft ⦋0⦌).obj ⦋0⦌).const ⦋0⦌ 0).op x)
  rw [contractionOperator_zero_factor, ← map_comp_op_apply]
  have hs : X.map (AugmentedSimplexCategory.inl' ⦋0⦌ n.unop).op s.val = x :=
    s.property
  rw [hs, map_comp_op_apply]
  congr 2

/-- The one endpoint retains every original coslice simplex. -/
theorem contraction_one (X : SSet.{u}) (x : X.obj (op ⦋0⦌)) :
    SSet.ι₁ ≫ contraction X x = 𝟙 (simplexCoslice ⦋0⦌ X x) := by
  ext n s : 2
  apply Subtype.ext
  change X.map (contractionOperator n.unop (n.unop.const ⦋1⦌ 1)).op s.val = s.val
  rw [contractionOperator_const_one, op_id, X.map_id]
  rfl

/-- The actual cylinder is a native simplicial homotopy from the constant map to identity. -/
def contractionHomotopy (X : SSet.{u}) (x : X.obj (op ⦋0⦌)) :
    SSet.Homotopy (SSet.const (coslicePoint X x)) (𝟙 (simplexCoslice ⦋0⦌ X x)) where
  h := contraction X x
  h₀ := contraction_zero X x
  h₁ := contraction_one X x
  rel := by
    ext

/-- The original vertex coslice itself is contractible for every simplicial set. -/
def vertexCosliceContractible (X : SSet.{u}) (x : X.obj (op ⦋0⦌)) :
    SSet.Contractible (simplexCoslice ⦋0⦌ X x) where
  pt := coslicePoint X x
  h := contractionHomotopy X x

/-- Native propositional contractibility of the same original coslice. -/
theorem vertex_coslice_isContractible (X : SSet.{u}) (x : X.obj (op ⦋0⦌)) :
    SSet.IsContractible (simplexCoslice ⦋0⦌ X x) :=
  ⟨vertexCosliceContractible X x⟩

end

end DaggerOriginalVertexCosliceContraction
