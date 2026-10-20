import DaggerModels.OrdinaryTwoObjectCell
import DaggerModels.UnderlyingTwoObjectCell
import DaggerModels.SimplicialObjectAdjunctions
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
Part I `bg.lem.reduction`: the underlying free dagger cell is the pushout of its two
ordinary one-edge copies over the discrete two-object category. The second copy uses the
usual `A(K)` with its object labels swapped; this is the manuscript's `A(K)^{10}`.
No connectedness, nonemptiness, monicity, or distinctness of target endpoints is assumed.
-/

open CategoryTheory Limits MonoidalCategory

universe u

namespace DaggerModels.TwoObjectCellPushout

noncomputable section

open TwoObjectDaggerGraph (Vertex left right)

def base : SimplicialCat.{u, u} := SimplicialCat.discrete Vertex.{u}

def swap (a : Vertex.{u}) : Vertex.{u} := ⟨!a.down⟩

/-- The common apex is the actual ordinary forgetful image of the free dagger cell. -/
def apex (K : SSet.{u}) : SimplicialCat.{u, u} :=
  DaggerSimplicialCat.forget.obj (TwoObjectDaggerCell.cell K)

/-- The first span leg preserves both object labels. -/
def spanLeft (K : SSet.{u}) : base ⟶ OrdinaryTwoObjectCell.cell K :=
  SimplicialCat.discreteLift Vertex (OrdinaryTwoObjectCell.cell K) id

/-- The second span leg swaps labels, representing the reverse one-edge category. -/
def spanRight (K : SSet.{u}) : base ⟶ OrdinaryTwoObjectCell.cell K :=
  SimplicialCat.discreteLift Vertex (OrdinaryTwoObjectCell.cell K) swap

def inl (K : SSet.{u}) : OrdinaryTwoObjectCell.cell K ⟶ apex K :=
  OrdinaryTwoObjectCell.fromData K (apex K) left right (TwoObjectDaggerCell.generator K)

def inr (K : SSet.{u}) : OrdinaryTwoObjectCell.cell K ⟶ apex K :=
  OrdinaryTwoObjectCell.fromData K (apex K) right left
    (UnderlyingTwoObjectCell.reverseGenerator K)

theorem condition (K : SSet.{u}) : spanLeft K ≫ inl K = spanRight K ≫ inr K := by
  apply (SimplicialCat.discreteHomEquiv Vertex (apex K)).injective
  funext a
  rcases a with ⟨a⟩
  cases a <;> rfl

/-- The displayed pushout cocone, with the two singleton-edge inclusions as its legs. -/
def cocone (K : SSet.{u}) : PushoutCocone (spanLeft K) (spanRight K) :=
  PushoutCocone.mk (inl K) (inr K) (condition K)

variable {K : SSet.{u}} {C : SimplicialCat.{u, u}}
  (F H : OrdinaryTwoObjectCell.cell K ⟶ C)
  (h : spanLeft K ≫ F = spanRight K ≫ H)

include h in
theorem compatible_left : F.obj left = H.obj right :=
  congrArg (fun M : base ⟶ C ↦ M.obj left) h

include h in
theorem compatible_right : F.obj right = H.obj left :=
  congrArg (fun M : base ⟶ C ↦ M.obj right) h

/-- Transport only the endpoints of the independent reverse edge map. -/
def backward : K ⟶ (F.obj right ⟶[SSet.{u}] F.obj left) :=
  H.map left right ≫ eqToHom
    (congrArg₂ (fun x y : C.Obj ↦ (x ⟶[SSet.{u}] y))
      (compatible_right F H h).symm (compatible_left F H h).symm)

theorem backward_cast : backward F H h ≫ eqToHom
    (congrArg₂ (fun x y : C.Obj ↦ (x ⟶[SSet.{u}] y))
      (compatible_right F H h) (compatible_left F H h)) = H.map left right := by
  simp [backward]

/-- The two independent edge maps extend to the actual finite-word underlying category. -/
def desc : apex K ⟶ C :=
  (UnderlyingTwoObjectCell.homEquiv K C).symm
    ⟨F.obj left, F.obj right, F.map left right, backward F H h⟩

private theorem oneEdgeData_eq {x y x' y' : C.Obj}
    {f : K ⟶ (x ⟶[SSet.{u}] y)} {g : K ⟶ (x' ⟶[SSet.{u}] y')}
    (hx : x = x') (hy : y = y')
    (hf : f ≫ eqToHom (congrArg₂ (fun a b : C.Obj ↦ (a ⟶[SSet.{u}] b)) hx hy) = g) :
    (⟨x, y, f⟩ : Σ a : C.Obj, Σ b : C.Obj, (K ⟶ (a ⟶[SSet.{u}] b))) = ⟨x', y', g⟩ := by
  cases hx
  cases hy
  simp only [eqToHom_refl, Category.comp_id] at hf
  cases hf
  rfl

theorem inl_desc : inl K ≫ desc F H h = F := by
  apply (OrdinaryTwoObjectCell.homEquiv K C).injective
  change (⟨F.obj left, F.obj right, TwoObjectDaggerCell.generator K ≫
    (desc F H h).map left right⟩ :
      Σ x : C.Obj, Σ y : C.Obj, (K ⟶ (x ⟶[SSet.{u}] y))) =
    ⟨F.obj left, F.obj right, F.map left right⟩
  dsimp only [desc]
  rw [UnderlyingTwoObjectCell.homEquiv_symm_generator]

theorem inr_desc : inr K ≫ desc F H h = H := by
  apply (OrdinaryTwoObjectCell.homEquiv K C).injective
  change (⟨F.obj right, F.obj left, UnderlyingTwoObjectCell.reverseGenerator K ≫
    (desc F H h).map right left⟩ :
      Σ x : C.Obj, Σ y : C.Obj, (K ⟶ (x ⟶[SSet.{u}] y))) =
    ⟨H.obj left, H.obj right, H.map left right⟩
  apply oneEdgeData_eq (compatible_right F H h) (compatible_left F H h)
  dsimp only [desc]
  rw [UnderlyingTwoObjectCell.homEquiv_symm_reverseGenerator]
  exact backward_cast F H h

/-- Project the forward edge and its ordered endpoints from the unrestricted two-edge data. -/
def forwardData (p : UnderlyingTwoObjectCell.TwoEdgeData K C) :
    Σ x : C.Obj, Σ y : C.Obj, (K ⟶ (x ⟶[SSet.{u}] y)) :=
  ⟨p.1, p.2.1, p.2.2.1⟩

/-- Project the reverse edge with its reversed ordered endpoints. -/
def reverseData (p : UnderlyingTwoObjectCell.TwoEdgeData K C) :
    Σ x : C.Obj, Σ y : C.Obj, (K ⟶ (x ⟶[SSet.{u}] y)) :=
  ⟨p.2.1, p.1, p.2.2.2⟩

theorem twoEdgeData_ext (p q : UnderlyingTwoObjectCell.TwoEdgeData K C)
    (hf : forwardData p = forwardData q) (hg : reverseData p = reverseData q) : p = q := by
  rcases p with ⟨x, y, f, g⟩
  rcases q with ⟨x', y', f', g'⟩
  have hx : x = x' := congrArg Sigma.fst hf
  have hy : y = y' := congrArg Sigma.fst hg
  cases hx
  cases hy
  have hf' : f = f' := eq_of_heq (congr_arg_heq
    (fun p : Σ x : C.Obj, Σ y : C.Obj, (K ⟶ (x ⟶[SSet.{u}] y)) ↦ p.2.2) hf)
  have hg' : g = g' := eq_of_heq (congr_arg_heq
    (fun p : Σ x : C.Obj, Σ y : C.Obj, (K ⟶ (x ⟶[SSet.{u}] y)) ↦ p.2.2) hg)
  cases hf'
  cases hg'
  rfl

/-- Both ordinary copies together determine the entire unrestricted enriched functor. -/
theorem hom_ext {m n : apex K ⟶ C} (hl : inl K ≫ m = inl K ≫ n)
    (hr : inr K ≫ m = inr K ≫ n) : m = n := by
  apply (UnderlyingTwoObjectCell.homEquiv K C).injective
  apply twoEdgeData_ext
  · exact congrArg (OrdinaryTwoObjectCell.homEquiv K C) hl
  · exact congrArg (OrdinaryTwoObjectCell.homEquiv K C) hr

/-- The actual underlying free dagger cell has the complete ordinary pushout UP. -/
def isColimit (K : SSet.{u}) : IsColimit (cocone K) :=
  PushoutCocone.IsColimit.mk (condition K)
    (fun s ↦ desc s.inl s.inr s.condition)
    (fun s ↦ inl_desc s.inl s.inr s.condition)
    (fun s ↦ inr_desc s.inl s.inr s.condition)
    (by
      intro s m hl hr
      apply hom_ext
      · exact hl.trans (inl_desc s.inl s.inr s.condition).symm
      · exact hr.trans (inr_desc s.inl s.inr s.condition).symm)

/-- The decomposition from `bg.lem.reduction`, using a swap-labelled second ordinary copy. -/
theorem isPushout (K : SSet.{u}) : IsPushout (spanLeft K) (spanRight K) (inl K) (inr K) :=
  IsPushout.of_isColimit (isColimit K)

end
end DaggerModels.TwoObjectCellPushout
