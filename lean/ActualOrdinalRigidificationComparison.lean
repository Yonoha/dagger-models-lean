import ActualThinConstantCoherentNerve

/-! A comparison from the literal rigidified simplex to the constant enriched ordinal. -/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerActualConstantSimplicialCategory DaggerActualThickeningPathContractibility
open DaggerOriginalFlagFlankification DaggerNerveHomotopy
open scoped Simplicial SSet.modelCategoryQuillen
universe u

namespace DaggerActualOrdinalRigidificationComparison
noncomputable section

local instance (n : ℕ) : EnrichedCategory SSet.{u} (ULift.{u} (Fin (n + 1))) :=
  DaggerUnitaryDiscrete.ordinaryEnriched _

local instance (n : ℕ) (a b : ULift.{u} (Fin (n + 1))) (q : SimplexCategoryᵒᵖ) :
    Subsingleton ((a ⟶[SSet.{u}] b).obj q) := by
  change Subsingleton (a ⟶ b)
  infer_instance

variable {J : Type u} [LinearOrder J] (i j : J)

/-- The entire path category records its ordered-endpoint arrow, including empty cases. -/
def pathCollapse : CategoryTheory.SimplicialThickening.Path i j ⥤ Discrete (i ⟶ j) where
  obj p := Discrete.mk (homOfLE p.le)
  map _ := eqToHom (by congr 1)

/-- Every ordered-endpoint arrow has its actual shortest path. -/
def pathCenter : Discrete (i ⟶ j) ⥤ CategoryTheory.SimplicialThickening.Path i j where
  obj f := shortestPath i j (leOfHom f.as)
  map _ := eqToHom (by congr 1)

/-- The shortest path is included in every path, for all endpoint orders. -/
def pathCenterToId : pathCollapse i j ⋙ pathCenter i j ⟶
    𝟭 (CategoryTheory.SimplicialThickening.Path i j) where
  app p := InducedCategory.homMk (homOfLE (by
    change ({i, j} : Set J) ⊆ p.I
    intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl
    · exact p.left
    · exact p.right))
  naturality _ _ _ := by
    apply InducedCategory.hom_ext
    exact Subsingleton.elim _ _

/-- The other composite retains the original ordered-endpoint arrow. -/
def pathCollapseToId : pathCenter i j ⋙ pathCollapse i j ⟶ 𝟭 (Discrete (i ⟶ j)) where
  app _ := eqToHom (by congr 1)
  naturality _ _ _ := Subsingleton.elim _ _

/-- This is a weak equivalence on all Homs, including the empty reverse Homs. -/
theorem pathCollapse_GW : DaggerSSetGluing.GW (nerveMap (pathCollapse i j)) :=
  nerveMap_geometricW (pathCollapse i j) (pathCenter i j)
    (Relation.EqvGen.rel _ _ ⟨pathCenterToId i j⟩)
    (Relation.EqvGen.rel _ _ ⟨pathCollapseToId i j⟩)

/-- The constant enriched ordinal retains every vertex of the native thickening. -/
def thickeningProjection (n : ℕ) :
    cosimplicialThickening.obj ⦋n⦌ ⟶ constant (ULift.{u} (Fin (n + 1))) where
  obj i := i.as
  map i j :=
    { app := fun _ γ ↦ homOfLE
        (@CategoryTheory.SimplicialThickening.Path.le
          (ULift.{u} (Fin (n + 1))) _ i.as j.as (γ.obj 0))
      naturality := by intros; funext γ; exact Subsingleton.elim _ _ }
  map_id _ := by ext q γ; exact Subsingleton.elim _ _
  map_comp _ _ _ := by ext q γ; exact Subsingleton.elim _ _

/-- The literal original projection has weak maps on every native thickening Hom. -/
theorem thickeningProjection_hom_GW (n : ℕ)
    (i j : (cosimplicialThickening.obj ⦋n⦌).Obj) :
    DaggerSSetGluing.GW ((thickeningProjection.{u} n).map i j) := by
  let f := nerveMap (pathCollapse i.as j.as)
  let e := nerveDiscreteIso (i.as ⟶ j.as)
  have : WeakEquivalence f := (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
    (pathCollapse_GW i.as j.as)
  have he : f ≫ e.hom = (thickeningProjection n).map i j := by
    apply NatTrans.ext
    funext q γ
    change (_ : i.as ⟶ j.as) = _
    exact Subsingleton.elim _ _
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

/-- The actual rigidified simplex maps to the constant ordinal without changing vertices. -/
def comparison (n : ℕ) : rigidification.obj (Δ[n] : SSet.{u}) ⟶
    constant (ULift.{u} (Fin (n + 1))) :=
  (rigidificationSimplexIso.{u}.app ⦋n⦌).hom ≫ thickeningProjection n

/-- Every actual comparison Hom is weak, with no endpoint nonemptiness assumption. -/
theorem comparison_hom_GW (n : ℕ)
    (a b : (rigidification.obj (Δ[n] : SSet.{u})).Obj) :
    DaggerSSetGluing.GW ((comparison n).map a b) := by
  let e := rigidificationSimplexIso.{u}.app ⦋n⦌
  have : WeakEquivalence (e.hom.map a b) := inferInstance
  have : WeakEquivalence ((thickeningProjection n).map (e.hom.obj a) (e.hom.obj b)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr (thickeningProjection_hom_GW n _ _)
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  change WeakEquivalence (e.hom.map a b ≫ _)
  infer_instance

end
end DaggerActualOrdinalRigidificationComparison
