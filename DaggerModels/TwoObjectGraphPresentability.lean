import DaggerModels.DaggerGraphEvaluation
import DaggerModels.TypeFunctorPullback
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable

/-!
Part I `bg.eq.A-univ`: fixed-endpoint maps are an actual pullback
of total-edge maps and pairs of vertices. No emptiness or connectivity
assumption is imposed on the source simplicial set.
-/

open CategoryTheory Limits Opposite

universe u

namespace DaggerModels.TwoObjectGraphPresentability

open DaggerSimplicialGraph.TotalSpace

def pairs : DaggerSimplicialGraph.{u} ⥤ Type u where
  obj G := G.Obj × G.Obj
  map k p := (k.obj p.1, k.obj p.2)

def pairConstants : DaggerSimplicialGraph.{u} ⥤ SSet.{u} :=
  pairs ⋙ Functor.const SimplexCategoryᵒᵖ

def endpoints : edgeFunctor.{u} ⟶ pairConstants where
  app G := { app := fun _ e ↦ (e.1, e.2.1) }

def constantMap (K : SSet.{u}) {X : Type u} (x : X) :
    K ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X where
  app _ _ := x

def edgeHoms (K : SSet.{u}) : DaggerSimplicialGraph.{u} ⥤ Type u :=
  edgeFunctor ⋙ coyoneda.obj (op K)

def constantHoms (K : SSet.{u}) : DaggerSimplicialGraph.{u} ⥤ Type u :=
  pairConstants ⋙ coyoneda.obj (op K)

def endpointMap (K : SSet.{u}) : edgeHoms K ⟶ constantHoms K where
  app G f := f ≫ endpoints.app G
  naturality {G H} k := by
    funext f
    change (f ≫ edgeMap k) ≫ endpoints.app H =
      (f ≫ endpoints.app G) ≫ pairConstants.map k
    have h : edgeMap k ≫ endpoints.app H = endpoints.app G ≫ pairConstants.map k :=
      endpoints.naturality k
    rw [Category.assoc, h, Category.assoc]

def constantMapNatural (K : SSet.{u}) : pairs ⟶ constantHoms K where
  app _ := constantMap K
  naturality {G H} k := by
    funext p
    change constantMap K (k.obj p.1, k.obj p.2) = constantMap K p ≫ pairConstants.map k
    ext n t
    rfl

def pullbackFunctor (K : SSet.{u}) : DaggerSimplicialGraph.{u} ⥤ Type u :=
  TypeFunctorPullback.functor (endpointMap K) (constantMapNatural K)

/-- The literal disjoint union over both endpoint choices, including empty `K`. -/
def sigmaFunctor (K : SSet.{u}) : DaggerSimplicialGraph.{u} ⥤ Type u where
  obj G := Σ x : G.Obj, Σ y : G.Obj, (K ⟶ G.Hom x y)
  map k p := ⟨k.obj p.1, k.obj p.2.1, p.2.2 ≫ k.map p.1 p.2.1⟩
  map_id G := by
    funext p
    rcases p with ⟨x, y, f⟩
    simp
  map_comp k l := by
    funext p
    rcases p with ⟨x, y, f⟩
    simp [Category.assoc]

def inclusion (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) :
    G.Hom x y ⟶ edges G where
  app _ e := ⟨x, y, e⟩

def fiberElement (K : SSet.{u}) (G : DaggerSimplicialGraph.{u}) (f : K ⟶ edges G)
    (x y : G.Obj) (h : f ≫ endpoints.app G = constantMap K (x, y))
    (n : SimplexCategoryᵒᵖ) (t : K.obj n) :
    {e : (edges G).obj n // e.1 = x ∧ e.2.1 = y} := by
  have ht := congrArg (fun a : K ⟶ pairConstants.obj G ↦ a.app n t) h
  change ((f.app n t).1, (f.app n t).2.1) = (x, y) at ht
  exact ⟨f.app n t, congrArg Prod.fst ht, congrArg Prod.snd ht⟩

/-- A total-edge map with constant endpoints factors through the exact hom fiber. -/
def fiberMap (K : SSet.{u}) (G : DaggerSimplicialGraph.{u}) (f : K ⟶ edges G)
    (x y : G.Obj) (h : f ≫ endpoints.app G = constantMap K (x, y)) : K ⟶ G.Hom x y where
  app n t := fiberEquiv G x y n (fiberElement K G f x y h n t)
  naturality {n m} α := by
    funext t
    let e := fiberElement K G f x y h n t
    have he : fiberElement K G f x y h m (K.map α t) =
        ⟨(edges G).map α e.val, e.property⟩ :=
      Subtype.ext (congrFun (f.naturality α) t)
    change fiberEquiv G x y m (fiberElement K G f x y h m (K.map α t)) =
      (G.Hom x y).map α (fiberEquiv G x y n e)
    rw [he]
    exact fiberEquiv_naturality G x y α e

def sigmaPullbackEquiv (K : SSet.{u}) (G : DaggerSimplicialGraph.{u}) :
    (sigmaFunctor K).obj G ≃ (pullbackFunctor K).obj G where
  toFun p := ⟨(p.2.2 ≫ inclusion G p.1 p.2.1, (p.1, p.2.1)), rfl⟩
  invFun e := ⟨e.val.2.1, e.val.2.2,
    fiberMap K G e.val.1 e.val.2.1 e.val.2.2 e.property⟩
  left_inv p := by
    rcases p with ⟨x, y, f⟩
    rfl
  right_inv e := by
    apply Subtype.ext
    apply Prod.ext
    · change fiberMap K G e.val.1 e.val.2.1 e.val.2.2 e.property ≫
        inclusion G e.val.2.1 e.val.2.2 = e.val.1
      ext n t
      exact congrArg Subtype.val ((fiberEquiv G e.val.2.1 e.val.2.2 n).left_inv
        (fiberElement K G e.val.1 e.val.2.1 e.val.2.2 e.property n t))
    · rfl

/-- The equivalence retains arbitrary vertex maps and all ordinary simplex operators. -/
def sigmaPullbackIso (K : SSet.{u}) : sigmaFunctor K ≅ pullbackFunctor K :=
  NatIso.ofComponents (fun G ↦ (sigmaPullbackEquiv K G).toIso) (by
    intro G H k
    funext p
    rcases p with ⟨x, y, f⟩
    apply Subtype.ext
    apply Prod.ext
    · change (f ≫ k.map x y) ≫ inclusion H (k.obj x) (k.obj y) =
        (f ≫ inclusion G x y) ≫ edgeMap k
      ext n t
      rfl
    · rfl)

def pairFst : pairs.{u} ⟶ DaggerGraphEvaluation.vertices where
  app _ := Prod.fst

def pairSnd : pairs.{u} ⟶ DaggerGraphEvaluation.vertices where
  app _ := Prod.snd

def pairsCone : BinaryFan DaggerGraphEvaluation.vertices.{u}
    DaggerGraphEvaluation.vertices := BinaryFan.mk pairFst pairSnd

def pairsLift {T : DaggerSimplicialGraph.{u} ⥤ Type u}
    (f g : T ⟶ DaggerGraphEvaluation.vertices) : T ⟶ pairs where
  app G t := (f.app G t, g.app G t)
  naturality {G H} k := by
    funext t
    exact Prod.ext (congrFun (f.naturality k) t) (congrFun (g.naturality k) t)

def pairsIsLimit : IsLimit pairsCone.{u} := BinaryFan.IsLimit.mk _ pairsLift
  (fun _ _ ↦ by ext G t; rfl)
  (fun _ _ ↦ by ext G t; rfl)
  (fun f g m h₁ h₂ ↦ by
    ext G t
    exact Prod.ext (congrArg (fun a ↦ a.app G t) h₁)
      (congrArg (fun a ↦ a.app G t) h₂))

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- A finite product of vertex evaluations preserves filtered colimits. -/
theorem pairs_isCardinalAccessible : pairs.{u}.IsCardinalAccessible Cardinal.aleph0.{u} := by
  letI := DaggerGraphEvaluation.vertices_preservesColimits.{u}
  letI : ∀ j, ((pair DaggerGraphEvaluation.vertices.{u}
      DaggerGraphEvaluation.vertices).obj j).IsCardinalAccessible Cardinal.aleph0.{u} := by
    rintro ⟨j⟩
    cases j <;> exact inferInstanceAs
      (DaggerGraphEvaluation.vertices.IsCardinalAccessible Cardinal.aleph0)
  exact Functor.isCardinalAccessible_of_isLimit pairsCone.{u} pairsIsLimit.{u}
    Cardinal.aleph0.{u}
    (hasCardinalLT_of_finite (Arrow (Discrete WalkingPair)) Cardinal.aleph0 le_rfl)

/-- The actual total-edge functor preserves colimits by its degreewise evaluations. -/
theorem edgeFunctor_preservesColimits : PreservesColimitsOfSize.{u, u} edgeFunctor.{u} :=
  preservesColimits_of_evaluation edgeFunctor (fun n ↦
    DaggerGraphEvaluation.edges_preservesColimits n)

/-- Presentable `K` gives accessibility of the literal fixed-endpoint mapping functor. -/
theorem sigmaFunctor_isCardinalAccessible (K : SSet.{u}) [IsFinitelyPresentable.{u} K] :
    (sigmaFunctor K).IsCardinalAccessible Cardinal.aleph0.{u} := by
  letI := pairs_isCardinalAccessible.{u}
  letI := edgeFunctor_preservesColimits.{u}
  letI : (edgeHoms K).IsCardinalAccessible Cardinal.aleph0.{u} :=
    inferInstanceAs ((edgeFunctor ⋙ coyoneda.obj (op K)).IsCardinalAccessible Cardinal.aleph0)
  letI : (constantHoms K).IsCardinalAccessible Cardinal.aleph0.{u} :=
    inferInstanceAs ((pairs ⋙ Functor.const SimplexCategoryᵒᵖ ⋙
      coyoneda.obj (op K)).IsCardinalAccessible Cardinal.aleph0)
  letI : (pullbackFunctor K).IsCardinalAccessible Cardinal.aleph0.{u} :=
    TypeFunctorPullback.isCardinalAccessible (endpointMap K) (constantMapNatural K)
  exact Functor.isCardinalAccessible_of_natIso (sigmaPullbackIso K).symm Cardinal.aleph0

/-- The source's finite simplicial sets satisfy the required presentability premise. -/
theorem sigmaFunctor_finite_isCardinalAccessible (K : SSet.{u}) [K.Finite] :
    (sigmaFunctor K).IsCardinalAccessible Cardinal.aleph0.{u} :=
  sigmaFunctor_isCardinalAccessible K

end DaggerModels.TwoObjectGraphPresentability
