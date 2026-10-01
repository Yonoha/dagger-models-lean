import DaggerModels.TwoObjectDaggerCell

/-! Ordinary functors from the underlying free dagger cell can choose its two
edge maps independently. This is the free-word step in `bg.lem.reduction`. -/

open CategoryTheory MonoidalCategory

universe u

namespace DaggerModels.UnderlyingTwoObjectCell

noncomputable section
attribute [local instance] FreeSimplicialPaths.enrichedCategory

/-- An unrestricted assignment of objects and edges, without dagger compatibility. -/
abbrev EdgeData (G : DaggerSimplicialGraph.{u}) (C : SimplicialCat.{u, u}) :=
  Σ f : G.Obj → C.Obj, ∀ x y, G.Hom x y ⟶ (f x ⟶[SSet.{u}] f y)

/-- Restrict an ordinary enriched functor to the original singleton edges. -/
def restrict (G : DaggerSimplicialGraph.{u}) (C : SimplicialCat.{u, u})
    (F : (FreeSimplicialPaths.daggerCat G).toSimplicialCat ⟶ C) : EdgeData G C :=
  ⟨F.obj, fun x y ↦ FreeSimplicialPaths.inclusion G x y ≫ F.map x y⟩

/-- Freely composing edge assignments gives an ordinary enriched functor. -/
def extend (G : DaggerSimplicialGraph.{u}) (C : SimplicialCat.{u, u}) (p : EdgeData G C) :
    (FreeSimplicialPaths.daggerCat G).toSimplicialCat ⟶ C :=
  FreeSimplicialExtension.extend G p.1 p.2

/-- The underlying category is free on every directed edge, without imposing a dagger law. -/
def ordinaryHomEquiv (G : DaggerSimplicialGraph.{u}) (C : SimplicialCat.{u, u}) :
    ((FreeSimplicialPaths.daggerCat G).toSimplicialCat ⟶ C) ≃ EdgeData G C where
  toFun := restrict G C
  invFun := extend G C
  left_inv F := FreeSimplicialExtension.extend_restrict G F
  right_inv p := by
    rcases p with ⟨f, φ⟩
    apply congrArg (Sigma.mk f)
    funext x y
    exact FreeSimplicialExtension.inclusion_extend G f φ x y

open TwoObjectDaggerGraph

/-- The two edge maps are independent in an ordinary simplicial target. -/
abbrev TwoEdgeData (K : SSet.{u}) (C : SimplicialCat.{u, u}) :=
  Σ x : C.Obj, Σ y : C.Obj, ((K ⟶ (x ⟶[SSet.{u}] y)) × (K ⟶ (y ⟶[SSet.{u}] x)))

def readEdges (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (p : EdgeData (graph K) C) : TwoEdgeData K C :=
  ⟨p.1 left, p.1 right, p.2 left right, p.2 right left⟩

/-- Assign both orientations separately; diagonal source edge spaces are empty. -/
def fromEdges (K : SSet.{u}) (C : SimplicialCat.{u, u}) (p : TwoEdgeData K C) :
    EdgeData (graph K) C :=
  ⟨(fun a ↦ match a with | ⟨false⟩ => p.1 | ⟨true⟩ => p.2.1),
    fun a b ↦ match a, b with
      | ⟨false⟩, ⟨false⟩ => emptyMap _
      | ⟨false⟩, ⟨true⟩ => p.2.2.1
      | ⟨true⟩, ⟨false⟩ => p.2.2.2
      | ⟨true⟩, ⟨true⟩ => emptyMap _⟩

theorem fromEdges_readEdges (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (p : EdgeData (graph K) C) : fromEdges K C (readEdges K C p) = p := by
  apply Sigma.ext
  · funext a
    rcases a with ⟨a⟩
    cases a <;> rfl
  · apply Function.hfunext rfl
    intro a a' ha
    obtain rfl := eq_of_heq ha
    apply Function.hfunext rfl
    intro b b' hb
    obtain rfl := eq_of_heq hb
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    cases a <;> cases b <;> apply heq_of_eq
    · exact (emptyMap_unique (p.2 left left)).symm
    · rfl
    · rfl
    · exact (emptyMap_unique (p.2 right right)).symm

def edgeDataEquiv (K : SSet.{u}) (C : SimplicialCat.{u, u}) :
    EdgeData (graph K) C ≃ TwoEdgeData K C where
  toFun := readEdges K C
  invFun := fromEdges K C
  left_inv := fromEdges_readEdges K C
  right_inv p := by rcases p with ⟨x, y, f, g⟩; rfl

/-- The exact ordinary universal property of the underlying dagger cell. -/
def homEquiv (K : SSet.{u}) (C : SimplicialCat.{u, u}) :
    ((TwoObjectDaggerCell.cell K).toSimplicialCat ⟶ C) ≃ TwoEdgeData K C :=
  (ordinaryHomEquiv (graph K) C).trans (edgeDataEquiv K C)


/-- The reverse generating edge remains independent after ordinary forgetting. -/
def reverseGenerator (K : SSet.{u}) :
    K ⟶ (DaggerSimplicialCat.underlyingGraph (TwoObjectDaggerCell.cell K)).Hom right left :=
  FreeSimplicialPaths.inclusion (graph K) right left

/-- Classification restricts an ordinary functor to both actual singleton generators. -/
theorem homEquiv_apply (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (F : (TwoObjectDaggerCell.cell K).toSimplicialCat ⟶ C) :
    homEquiv K C F = ⟨F.obj left, F.obj right,
      TwoObjectDaggerCell.generator K ≫ F.map left right,
      reverseGenerator K ≫ F.map right left⟩ := rfl

theorem homEquiv_symm_obj_left (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (p : TwoEdgeData K C) : ((homEquiv K C).symm p).obj left = p.1 := rfl

theorem homEquiv_symm_obj_right (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (p : TwoEdgeData K C) : ((homEquiv K C).symm p).obj right = p.2.1 := rfl

theorem homEquiv_symm_generator (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (x y : C.Obj) (f : K ⟶ (x ⟶[SSet.{u}] y)) (g : K ⟶ (y ⟶[SSet.{u}] x)) :
    TwoObjectDaggerCell.generator K ≫ ((homEquiv K C).symm ⟨x, y, f, g⟩).map left right = f :=
  FreeSimplicialExtension.inclusion_extend (graph K)
    (fromEdges K C ⟨x, y, f, g⟩).1 (fromEdges K C ⟨x, y, f, g⟩).2 left right

theorem homEquiv_symm_reverseGenerator (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (x y : C.Obj) (f : K ⟶ (x ⟶[SSet.{u}] y)) (g : K ⟶ (y ⟶[SSet.{u}] x)) :
    reverseGenerator K ≫ ((homEquiv K C).symm ⟨x, y, f, g⟩).map right left = g :=
  FreeSimplicialExtension.inclusion_extend (graph K)
    (fromEdges K C ⟨x, y, f, g⟩).1 (fromEdges K C ⟨x, y, f, g⟩).2 right left

/-- Ordinary target functors act on the two edges independently. -/
theorem homEquiv_naturality_right (K : SSet.{u})
    {C D : SimplicialCat.{u, u}} (F : (TwoObjectDaggerCell.cell K).toSimplicialCat ⟶ C)
    (H : C ⟶ D) :
    homEquiv K D (F ≫ H) =
      ⟨H.obj (homEquiv K C F).1, H.obj (homEquiv K C F).2.1,
        (homEquiv K C F).2.2.1 ≫ H.map _ _,
        (homEquiv K C F).2.2.2 ≫ H.map _ _⟩ := rfl

end
end DaggerModels.UnderlyingTwoObjectCell
