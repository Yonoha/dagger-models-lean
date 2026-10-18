import OriginalSingularCylinderParameterNaturality

/-!
# The original singular endpoint fiber and singular of the original continuous path space

The original endpoint hom equivalences are natural in every simplicial parameter. The native
Yoneda embedding therefore assembles them into an actual simplicial isomorphism. The original
space and both original points are retained. This is independent of rigidification or intervals.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial
open DaggerOriginalFullVertexSubcomplex DaggerOriginalContinuousEndpointCylinderFamilies
open DaggerOriginalSingularConstantEndpointCylinders
open DaggerOriginalSingularPathCylinderAdjunction DaggerOriginalSingularCylinderParameterNaturality

universe u

namespace DaggerOriginalSingularStrictContinuousPathIso

noncomputable section

/-- Precomposition acts on the same original parameter of a fixed-endpoint cylinder. -/
def constantCylinderPrecompose {E F T : TopCat.{u}} (k : E ⟶ F) {a b : T}
    (h : constantEndpointCylinders F T a b) : constantEndpointCylinders E T a b :=
  ⟨k ▷ TopCat.I ≫ h.val, by
    constructor
    · apply ConcreteCategory.hom_ext
      intro e
      exact ConcreteCategory.congr_hom h.property.1 (k e)
    · apply ConcreteCategory.hom_ext
      intro e
      exact ConcreteCategory.congr_hom h.property.2 (k e)⟩

/-- Native continuous currying commutes with the actual original parameter map. -/
theorem constantCylinderPathFamilyEquiv_parameter_naturality {E F T : TopCat.{u}}
    (k : E ⟶ F) (a b : T) (h : constantEndpointCylinders F T a b) :
    constantCylinderPathFamilyEquiv E T a b (constantCylinderPrecompose k h) =
      k ≫ constantCylinderPathFamilyEquiv F T a b h := by
  apply ConcreteCategory.hom_ext
  intro e
  apply Path.ext
  funext t
  rfl

/-- The same original endpoint hom equivalence, with explicit endpoint proof transport. -/
def singularStrictOriginalCylinderHomEquiv (T : TopCat.{u}) (A : SSet.{u})
    (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌)) :
    (A ⟶ (strictPathFiber (TopCat.toSSet.obj T) a b : SSet)) ≃
      constantEndpointCylinders (SSet.toTop.obj A) T
        (TopCat.toSSetObj₀Equiv a) (TopCat.toSSetObj₀Equiv b) :=
  (DaggerOriginalStrictPathFiberHomEquiv.singularStrictFiberHomCylinderEquiv T A a b).trans
    { toFun h := ⟨h.val, by simpa only [topologicalAdjoint_const] using h.property⟩
      invFun h := ⟨h.val, by simpa only [topologicalAdjoint_const] using h.property⟩
      left_inv h := Subtype.ext rfl
      right_inv h := Subtype.ext rfl }

/-- The exact original strict-fiber hom equivalence commutes with the same parameter map. -/
theorem singularStrictOriginalCylinderHomEquiv_parameter_naturality (T : TopCat.{u})
    {A B : SSet.{u}} (f : A ⟶ B)
    (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌))
    (q : B ⟶ (strictPathFiber (TopCat.toSSet.obj T) a b : SSet)) :
    singularStrictOriginalCylinderHomEquiv T A a b (f ≫ q) =
      constantCylinderPrecompose (SSet.toTop.map f)
        (singularStrictOriginalCylinderHomEquiv T B a b q) := by
  apply Subtype.ext
  change singularPathHomCylinderEquiv T A
    ((f ≫ q) ≫ (strictPathFiber (TopCat.toSSet.obj T) a b).ι) =
      SSet.toTop.map f ▷ TopCat.I ≫ singularPathHomCylinderEquiv T B
        (q ≫ (strictPathFiber (TopCat.toSSet.obj T) a b).ι)
  rw [Category.assoc, singularPathHomCylinderEquiv_parameter_naturality]

/-- Maps into the exact original strict singular endpoint fiber are maps into singular Path. -/
def singularStrictContinuousPathHomEquiv (T : TopCat.{u}) (A : SSet.{u})
    (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌)) :
    (A ⟶ (strictPathFiber (TopCat.toSSet.obj T) a b : SSet)) ≃
    (A ⟶ TopCat.toSSet.obj
      (continuousPathTop T (TopCat.toSSetObj₀Equiv a) (TopCat.toSSetObj₀Equiv b))) :=
  (singularStrictOriginalCylinderHomEquiv T A a b).trans
    ((constantCylinderPathFamilyEquiv (SSet.toTop.obj A) T
      (TopCat.toSSetObj₀Equiv a) (TopCat.toSSetObj₀Equiv b)).trans
      (sSetTopAdj.homEquiv A
        (continuousPathTop T (TopCat.toSSetObj₀Equiv a) (TopCat.toSSetObj₀Equiv b))))

/-- The same original strict-fiber-to-singular-Path hom equivalence is natural in the parameter.
-/
theorem singularStrictContinuousPathHomEquiv_parameter_naturality (T : TopCat.{u})
    {A B : SSet.{u}} (f : A ⟶ B)
    (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌))
    (q : B ⟶ (strictPathFiber (TopCat.toSSet.obj T) a b : SSet)) :
    singularStrictContinuousPathHomEquiv T A a b (f ≫ q) =
      f ≫ singularStrictContinuousPathHomEquiv T B a b q := by
  change (sSetTopAdj.homEquiv A _)
    (constantCylinderPathFamilyEquiv (SSet.toTop.obj A) T _ _
      (singularStrictOriginalCylinderHomEquiv T A a b (f ≫ q))) =
    f ≫ (sSetTopAdj.homEquiv B _)
      (constantCylinderPathFamilyEquiv (SSet.toTop.obj B) T _ _
        (singularStrictOriginalCylinderHomEquiv T B a b q))
  rw [singularStrictOriginalCylinderHomEquiv_parameter_naturality,
    constantCylinderPathFamilyEquiv_parameter_naturality,
    sSetTopAdj.homEquiv_naturality_left]

/-- The original strict endpoint fiber and singular Path represent naturally identical homs. -/
def singularStrictContinuousPathYonedaIso (T : TopCat.{u})
    (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌)) :
    yoneda.obj (strictPathFiber (TopCat.toSSet.obj T) a b : SSet) ≅
      yoneda.obj (TopCat.toSSet.obj
        (continuousPathTop T (TopCat.toSSetObj₀Equiv a) (TopCat.toSSetObj₀Equiv b))) :=
  NatIso.ofComponents
    (fun A ↦ (singularStrictContinuousPathHomEquiv T A.unop a b).toIso)
    (fun f ↦ by
      ext q
      exact singularStrictContinuousPathHomEquiv_parameter_naturality T f.unop a b q)

/-- The actual original strict singular endpoint fiber is simplicially isomorphic to singular
 of the original compact-open continuous path space with the same original endpoints. -/
def singularStrictContinuousPathIso (T : TopCat.{u})
    (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌)) :
    (strictPathFiber (TopCat.toSSet.obj T) a b : SSet) ≅
      TopCat.toSSet.obj
        (continuousPathTop T (TopCat.toSSetObj₀Equiv a) (TopCat.toSSetObj₀Equiv b)) :=
  yoneda.preimageIso (singularStrictContinuousPathYonedaIso T a b)

end

end DaggerOriginalSingularStrictContinuousPathIso
