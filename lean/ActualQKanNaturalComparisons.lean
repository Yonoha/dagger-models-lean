import ActualQSingularCotensorExchangeIso

/-! Both weak legs to the same original-Q cotensor diagonal are natural in the entire target. -/

set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalFixedObjectCotensorPoints DaggerSSetGluing
open DaggerOriginalCounitRightConeQFunctor
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerActualSSetCotensorExchange DaggerActualQSingularCotensorExchangeIso
open DaggerActualQSingularSimplexCotensorDiagonal
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualQKanNaturalComparisons
noncomputable section

/-- The original constant map commutes with every full simplicial target map. -/
theorem constantHom_target {X Y : SSet.{u}} (K : SSet.{u}) (f : X ⟶ Y) :
    constantHom K X ≫ (ihom K).map f = f ≫ constantHom K Y := by
  unfold constantHom
  rw [← curry_natural_right, ← curry_natural_left]
  congr 1

/-- Target maps between native cotensors, for any unchanged cosimplicial parameter. -/
def cotensorMap (A : SimplexCategory ⥤ SSet.{u}) {X Y : SSet.{u}} (f : X ⟶ Y) :
    A.op ⋙ DaggerActualKanCotensorParameterWeakEquivalences.parameterFunctor X ⟶
      A.op ⋙ DaggerActualKanCotensorParameterWeakEquivalences.parameterFunctor Y where
  app n := (ihom (A.obj n.unop)).map f
  naturality _ _ i := MonoidalClosed.pre_comm_ihom_map (A.map i.unop) f

/-- Every original Q degree uses precisely the native target internal-Hom map. -/
def mixedMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    DaggerActualQKanCotensorComparison.mixed X ⟶ DaggerActualQKanCotensorComparison.mixed Y :=
  cotensorMap QFunctor f

/-- Apply the same native target maps under the literal original singular functor. -/
def singularMixedMap {X Y : SSet.{u}} (f : X ⟶ Y) : singularMixed X ⟶ singularMixed Y :=
  Functor.whiskerRight (cotensorMap SSet.stdSimplex f) singular

/-- The first diagonal weak map is natural in the entire original Kan target. -/
theorem constants_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    f ≫ DaggerBisimplicialDiagonal.diagMap (DaggerActualQKanCotensorComparison.constants Y) =
      DaggerBisimplicialDiagonal.diagMap (DaggerActualQKanCotensorComparison.constants X) ≫
        DaggerBisimplicialDiagonal.diagMap (mixedMap f) := by
  apply NatTrans.ext
  funext q x
  exact (congrFun (congrArg (fun t ↦ t.app q)
    (constantHom_target (QFunctor.obj q.unop) f)) x).symm

/-- Standard-simplex constants commute with every actual singular target map. -/
theorem simplex_constants_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    singular.map f ≫ diagonalComparison Y =
      diagonalComparison X ≫ DaggerBisimplicialDiagonal.diagMap (singularMixedMap f) := by
  apply NatTrans.ext
  funext q t
  apply ULift.ext
  change (t.down ≫ f) ≫ constantHom (SSet.stdSimplex.obj q.unop) Y =
    (t.down ≫ constantHom (SSet.stdSimplex.obj q.unop) X) ≫
      (ihom (SSet.stdSimplex.obj q.unop)).map f
  simp only [Category.assoc, constantHom_target]

/-- The native exchange/Yoneda isomorphism commutes with every full target map. -/
theorem diagonalExchangeIso_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    DaggerBisimplicialDiagonal.diagMap (singularMixedMap f) ≫ (diagonalExchangeIso Y).hom =
      (diagonalExchangeIso X).hom ≫ DaggerBisimplicialDiagonal.diagMap (mixedMap f) := by
  apply NatTrans.ext
  funext q t
  change SSet.yonedaEquiv (exchangeHomEquiv (QFunctor.obj q.unop)
      (SSet.stdSimplex.obj q.unop) Y (t.down ≫ (ihom (SSet.stdSimplex.obj q.unop)).map f)) = _
  rw [exchangeHomEquiv_target, SSet.yonedaEquiv_comp]
  rfl

/-- The second weak leg is natural for precisely the same diagonal target functor. -/
theorem singularComparison_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    singular.map f ≫ singularComparison Y =
      singularComparison X ≫ DaggerBisimplicialDiagonal.diagMap (mixedMap f) := by
  dsimp only [singularComparison]
  rw [← Category.assoc, simplex_constants_naturality, Category.assoc,
    diagonalExchangeIso_naturality, ← Category.assoc]

/-- The actual diagonal target map detects and preserves geometric weakness between Kan objects. -/
theorem mixedMap_GW_iff {X Y : SSet.{u}} (f : X ⟶ Y) [X.KanComplex] [Y.KanComplex] :
    GW (DaggerBisimplicialDiagonal.diagMap (mixedMap f)) ↔ GW f := by
  have : WeakEquivalence
      (DaggerBisimplicialDiagonal.diagMap (DaggerActualQKanCotensorComparison.constants X)) :=
    (weakEquivalence_iff_GW _).2 (DaggerActualQKanCotensorComparison.diagonal_constants_GW X)
  have : WeakEquivalence
      (DaggerBisimplicialDiagonal.diagMap (DaggerActualQKanCotensorComparison.constants Y)) :=
    (weakEquivalence_iff_GW _).2 (DaggerActualQKanCotensorComparison.diagonal_constants_GW Y)
  constructor
  · intro h
    have : WeakEquivalence (DaggerBisimplicialDiagonal.diagMap (mixedMap f)) :=
      (weakEquivalence_iff_GW _).2 h
    exact (weakEquivalence_iff_GW _).1
      (weakEquivalence_of_postcomp_of_fac (constants_naturality f))
  · intro h
    have : WeakEquivalence f := (weakEquivalence_iff_GW _).2 h
    exact (weakEquivalence_iff_GW _).1
      (weakEquivalence_of_precomp_of_fac (constants_naturality f).symm)

/-- No reflection hypothesis is supplied: the two proved natural weak legs detect weakness. -/
theorem singular_reflects_GW {X Y : SSet.{u}} (f : X ⟶ Y) [X.KanComplex] [Y.KanComplex]
    (h : GW (singular.map f)) : GW f := by
  have : WeakEquivalence (singular.map f) := (weakEquivalence_iff_GW _).2 h
  have : WeakEquivalence (singularComparison X) :=
    (weakEquivalence_iff_GW _).2 (singularComparison_GW X)
  have : WeakEquivalence (singularComparison Y) :=
    (weakEquivalence_iff_GW _).2 (singularComparison_GW Y)
  have hm : WeakEquivalence (DaggerBisimplicialDiagonal.diagMap (mixedMap f)) :=
    weakEquivalence_of_precomp_of_fac (singularComparison_naturality f).symm
  exact (mixedMap_GW_iff f).1 ((weakEquivalence_iff_GW _).1 hm)

/-- The literal original singular functor creates the weak class on Kan targets. -/
theorem singular_GW_iff {X Y : SSet.{u}} (f : X ⟶ Y) [X.KanComplex] [Y.KanComplex] :
    GW (singular.map f) ↔ GW f :=
  ⟨singular_reflects_GW f, DaggerActualQSingularFibrantWeakEquivalences.singular_GW f⟩

end
end DaggerActualQKanNaturalComparisons
