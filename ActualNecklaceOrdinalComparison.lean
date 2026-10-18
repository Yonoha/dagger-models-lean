import ActualFibrantSimplexContractibility
import ChosenNecklaceChosenComparison

/-! Compare every original necklace rigidification to its labelled constant enriched ordinal. -/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerActualConstantSimplicialCategory DaggerChosenRigidificationNecklace
open NecklaceCode NecklaceThickening
open DaggerOriginalFlagFlankification DaggerNerveHomotopy
open scoped Simplicial SSet.modelCategoryQuillen
universe u

namespace DaggerActualNecklaceOrdinalComparison
noncomputable section

local instance (n : ℕ) : EnrichedCategory SSet.{u} (ULift.{u} (Fin (n + 1))) :=
  DaggerUnitaryDiscrete.ordinaryEnriched _

local instance (n : ℕ) (a b : ULift.{u} (Fin (n + 1))) (q : SimplexCategoryᵒᵖ) :
    Subsingleton ((a ⟶[SSet.{u}] b).obj q) := by
  change Subsingleton (a ⟶ b)
  infer_instance

variable (T : NecklaceCode) (i j : Vertices.{u} T)

/-- The shortest admissible joint path retains both endpoints and every required interior joint. -/
def minimalJointPath (hij : i ≤ j) : JointPath i j where
  I := {i, j} ∪ {v | v.down ∈ T.joints ∧ i ≤ v ∧ v ≤ j}
  left := Or.inl (by simp)
  right := Or.inl (by simp)
  left_le k hk := by
    rcases hk with hk | hk
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      rcases hk with rfl | rfl
      · exact le_rfl
      · exact hij
    · exact hk.2.1
  le_right k hk := by
    rcases hk with hk | hk
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      rcases hk with rfl | rfl
      · exact hij
      · exact le_rfl
    · exact hk.2.2
  joints k hk hl hr := Or.inr ⟨hk, hl, hr⟩

/-- Minimality is the literal inclusion of sets of original necklace vertices. -/
theorem minimalJointPath_subset (hij : i ≤ j) (p : JointPath i j) :
    (minimalJointPath T i j hij).I ⊆ p.I := by
  intro k hk
  rcases hk with hk | hk
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl
    · exact p.left
    · exact p.right
  · rcases hk with ⟨hk, hl, hr⟩
    cases k with
    | up k => exact p.joints k hk hl hr

/-- Collapse the entire joint-path category to its ordered-endpoint arrow. -/
def collapse : JointPath i j ⥤ Discrete (i ⟶ j) where
  obj p := Discrete.mk (homOfLE p.le)
  map _ := eqToHom (by congr 1)

/-- Each ordered-endpoint arrow gives a minimal path containing the prescribed joints. -/
def center : Discrete (i ⟶ j) ⥤ JointPath i j where
  obj f := minimalJointPath T i j (leOfHom f.as)
  map _ := eqToHom (by congr 1)

/-- The minimal joint path maps to every actual joint path. -/
def centerToId : collapse T i j ⋙ center T i j ⟶ 𝟭 (JointPath i j) where
  app p := InducedCategory.homMk (homOfLE
    (minimalJointPath_subset T i j (JointPath.le p) p))
  naturality _ _ _ := by
    apply InducedCategory.hom_ext
    exact Subsingleton.elim _ _

/-- The reverse composite keeps the same ordered-endpoint arrow. -/
def collapseToId : center T i j ⋙ collapse T i j ⟶ 𝟭 (Discrete (i ⟶ j)) where
  app _ := eqToHom (by congr 1)
  naturality _ _ _ := Subsingleton.elim _ _

/-- The complete joint-path collapse is weak, including reverse and diagonal endpoint pairs. -/
theorem collapse_GW : DaggerSSetGluing.GW (nerveMap (collapse T i j)) :=
  nerveMap_geometricW (collapse T i j) (center T i j)
    (Relation.EqvGen.rel _ _ ⟨centerToId T i j⟩)
    (Relation.EqvGen.rel _ _ ⟨collapseToId T i j⟩)

/-- The original necklace thickening projects to the constant enriched vertex ordinal. -/
def thickeningProjection : NC.{u} T ⟶ constant T.Vertices where
  obj a := a.as
  map a b :=
    { app := fun _ γ ↦ homOfLE (JointPath.le (γ.obj 0))
      naturality := by intros; funext γ; exact Subsingleton.elim _ _ }
  map_id _ := by ext q γ; exact Subsingleton.elim _ _
  map_comp _ _ _ := by ext q γ; exact Subsingleton.elim _ _

/-- Every actual thickening Hom maps weakly to its constant ordered arrow. -/
theorem thickeningProjection_hom_GW (a b : (NC.{u} T).Obj) :
    DaggerSSetGluing.GW ((thickeningProjection T).map a b) := by
  let f := nerveMap (collapse T a.as b.as)
  let e := nerveDiscreteIso (a.as ⟶ b.as)
  have : WeakEquivalence f := (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
    (collapse_GW T a.as b.as)
  have he : f ≫ e.hom = (thickeningProjection T).map a b := by
    apply NatTrans.ext
    funext q γ
    change (_ : a.as ⟶ b.as) = _
    exact Subsingleton.elim _ _
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

/-- The previously constructed whole original C(T)-NC(T) isomorphism is reused literally. -/
def comparison : rigidification.obj T.toSSet ⟶ constant T.Vertices :=
  (chosenNecklaceIso.{u} T).hom ≫ thickeningProjection T

/-- The comparison retains the original vertex labels. -/
theorem comparison_vertex (x : (toSSet.{u} T).obj (op ⦋0⦌)) :
    (comparison T).obj (RigidificationVertices.vertexEquiv T.toSSet x) =
      T.verticesEquiv x := by
  change ((chosenNecklaceIso T).hom.obj (RV T.toSSet x)).as = _
  rw [chosenNecklaceIso_objects, canonicalNCObject_vertex]

/-- All objects occur in the actual comparison with their original labels. -/
theorem comparison_surjective : Function.Surjective (comparison.{u} T).obj := by
  intro y
  let e := chosenNecklaceIso.{u} T
  let z : (NC.{u} T).Obj := ⟨y⟩
  refine ⟨e.inv.obj z, ?_⟩
  change (e.hom.obj (e.inv.obj z)).as = y
  have h := congrArg (fun f : NC.{u} T ⟶ NC.{u} T ↦ f.obj z) e.inv_hom_id
  exact congrArg (fun w ↦ w.as) h

/-- Every original comparison Hom is weak, with no endpoint ordering premise. -/
theorem comparison_hom_GW (a b : (rigidification.obj (toSSet.{u} T)).Obj) :
    DaggerSSetGluing.GW ((comparison T).map a b) := by
  let e := chosenNecklaceIso.{u} T
  have : WeakEquivalence (e.hom.map a b) := inferInstance
  have : WeakEquivalence ((thickeningProjection T).map (e.hom.obj a) (e.hom.obj b)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr (thickeningProjection_hom_GW T _ _)
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  change WeakEquivalence (e.hom.map a b ≫ _)
  infer_instance

end
end DaggerActualNecklaceOrdinalComparison
