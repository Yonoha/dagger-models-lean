import OriginalOrdinaryGraphValues
import DaggerModels.TypeFunctorPullback

/-!
# Endpoint-indexed maps in original ordinary simplicial graphs

A map from `K` into an individual Hom object is equivalent to a total-edge
map with a chosen pair of constant endpoints.  The chosen pair remains in the
fiber product even if `K` is empty or disconnected.
-/

open CategoryTheory Limits Opposite

universe u

namespace DaggerModels.OriginalOrdinaryGraphSigmaFunctor

open SimplicialGraph.TotalSpace

def pairs : SimplicialGraph.{u} ⥤ Type u where
  obj G := G.Obj × G.Obj
  map k p := (k.obj p.1, k.obj p.2)

def pairConstants : SimplicialGraph.{u} ⥤ SSet.{u} :=
  pairs ⋙ Functor.const SimplexCategoryᵒᵖ

def endpoints : edgeFunctor.{u} ⟶ pairConstants where
  app G := { app := fun _ e ↦ (e.1, e.2.1) }

def constantMap (K : SSet.{u}) {X : Type u} (x : X) :
    K ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X where
  app _ _ := x

def edgeHoms (K : SSet.{u}) : SimplicialGraph.{u} ⥤ Type u :=
  edgeFunctor ⋙ coyoneda.obj (op K)

def constantHoms (K : SSet.{u}) : SimplicialGraph.{u} ⥤ Type u :=
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

def pullbackFunctor (K : SSet.{u}) : SimplicialGraph.{u} ⥤ Type u :=
  TypeFunctorPullback.functor (endpointMap K) (constantMapNatural K)

/-- The literal disjoint union over both endpoint choices, including empty `K`. -/
def sigmaFunctor (K : SSet.{u}) : SimplicialGraph.{u} ⥤ Type u where
  obj G := Σ x : G.Obj, Σ y : G.Obj, (K ⟶ G.Hom x y)
  map k p := ⟨k.obj p.1, k.obj p.2.1, p.2.2 ≫ k.map p.1 p.2.1⟩
  map_id G := by
    funext p
    rcases p with ⟨x, y, f⟩
    change (⟨x, y, f ≫ 𝟙 (G.Hom x y)⟩ :
      Σ a : G.Obj, Σ b : G.Obj, (K ⟶ G.Hom a b)) = ⟨x, y, f⟩
    rw [Category.comp_id]
  map_comp k l := by
    funext p
    rcases p with ⟨x, y, f⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Sigma.ext rfl
    apply heq_of_eq
    exact (Category.assoc f (k.map x y) (l.map (k.obj x) (k.obj y))).symm

def inclusion (G : SimplicialGraph.{u}) (x y : G.Obj) :
    G.Hom x y ⟶ edges G where
  app _ e := ⟨x, y, e⟩

def fiberElement (K : SSet.{u}) (G : SimplicialGraph.{u}) (f : K ⟶ edges G)
    (x y : G.Obj) (h : f ≫ endpoints.app G = constantMap K (x, y))
    (n : SimplexCategoryᵒᵖ) (t : K.obj n) :
    {e : (edges G).obj n // e.1 = x ∧ e.2.1 = y} := by
  have ht := congrArg (fun a : K ⟶ pairConstants.obj G ↦ a.app n t) h
  change ((f.app n t).1, (f.app n t).2.1) = (x, y) at ht
  exact ⟨f.app n t, congrArg Prod.fst ht, congrArg Prod.snd ht⟩

/-- A total-edge map with constant endpoints factors through the exact hom fiber. -/
def fiberMap (K : SSet.{u}) (G : SimplicialGraph.{u}) (f : K ⟶ edges G)
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

def sigmaPullbackEquiv (K : SSet.{u}) (G : SimplicialGraph.{u}) :
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

end DaggerModels.OriginalOrdinaryGraphSigmaFunctor
