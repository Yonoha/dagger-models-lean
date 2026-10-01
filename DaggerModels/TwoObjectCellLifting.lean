import DaggerModels.TwoObjectDaggerCell
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-! The local generator-lifting correspondence in Part I `bg.lem.I-inj`.
The actual two-object free dagger cell has the full Hom equivalence of
`bg.eq.A-univ`. Endpoint equalities are extracted before comparing dependent
hom maps. No condition on endpoints or on the simplicial sets is imposed.
This does not assert object surjectivity or a model-category characterization. -/

open CategoryTheory MonoidalCategory

universe u

namespace DaggerModels.TwoObjectCellLifting

noncomputable section

open TwoObjectDaggerCell

variable {K L : SSet.{u}} (i : K ⟶ L)
  {C D : DaggerSimplicialCat.{u, u}} (p : C ⟶ D)

/-- Lifting against the actual free cell gives lifting on each full hom space. -/
theorem hom_hasLiftingProperty (h : HasLiftingProperty (functor.map i) p)
    (x y : C.Obj) : HasLiftingProperty i (p.map x y) := by
  refine ⟨fun {f g} sq ↦ ?_⟩
  let F : cell K ⟶ C := (homEquiv K C).symm ⟨x, y, f⟩
  let G : cell L ⟶ D := (homEquiv L D).symm ⟨p.obj x, p.obj y, g⟩
  have hF : homEquiv K C F = ⟨x, y, f⟩ := (homEquiv K C).apply_symm_apply _
  have hG : homEquiv L D G = ⟨p.obj x, p.obj y, g⟩ :=
    (homEquiv L D).apply_symm_apply _
  have cellSq : CommSq F (functor.map i) p G := by
    constructor
    apply (homEquiv K D).injective
    rw [homEquiv_naturality_right, homEquiv_naturality_left, hF, hG]
    rw [sq.w]
  have : cellSq.HasLift := h.sq_hasLift cellSq
  rcases hH : homEquiv L C cellSq.lift with ⟨x', y', l⟩
  have hleft := congrArg (homEquiv K C) cellSq.fac_left
  rw [homEquiv_naturality_left, hH, hF] at hleft
  -- The cell map is the identity on vertices: these equalities transport l
  -- to the requested hom space C(x,y), including when x = y.
  have hx : x' = x := congrArg Sigma.fst hleft
  have hy : y' = y := congrArg (fun z ↦ z.2.1) hleft
  subst x'
  subst y'
  refine CommSq.HasLift.mk' { l := l, fac_left := ?_, fac_right := ?_ }
  · simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hleft
  · have hright := congrArg (homEquiv L D) cellSq.fac_right
    rw [homEquiv_naturality_right, hH, hG] at hright
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hright

/-- Local hom lifting solves every cell square, with arbitrary object maps. -/
theorem cell_hasLiftingProperty
    (h : ∀ x y : C.Obj, HasLiftingProperty i (p.map x y)) :
    HasLiftingProperty (functor.map i) p := by
  refine ⟨fun {F G} sq ↦ ?_⟩
  rcases hF : homEquiv K C F with ⟨x, y, f⟩
  rcases hG : homEquiv L D G with ⟨x', y', g⟩
  have hw := congrArg (homEquiv K D) sq.w
  rw [homEquiv_naturality_right, homEquiv_naturality_left, hF, hG] at hw
  -- The bottom endpoints need not be definitionally p(x), p(y).
  -- Square commutativity gives the equalities used for the dependent transport.
  have hx : p.obj x = x' := congrArg Sigma.fst hw
  have hy : p.obj y = y' := congrArg (fun z ↦ z.2.1) hw
  subst x'
  subst y'
  have homSq : CommSq f i (p.map x y) g := by
    constructor
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hw
  have : homSq.HasLift := (h x y).sq_hasLift homSq
  refine CommSq.HasLift.mk'
    { l := (homEquiv L C).symm ⟨x, y, homSq.lift⟩
      fac_left := ?_
      fac_right := ?_ }
  · apply (homEquiv K C).injective
    rw [homEquiv_naturality_left, Equiv.apply_symm_apply, hF]
    simp only [homSq.fac_left]
  · apply (homEquiv L D).injective
    rw [homEquiv_naturality_right, Equiv.apply_symm_apply, hG]
    simp only [homSq.fac_right]

/-- The actual cell map detects exactly the lifting properties of all hom maps. -/
theorem hasLiftingProperty_iff :
    HasLiftingProperty (TwoObjectDaggerCell.functor.map i) p ↔
      ∀ x y : C.Obj, HasLiftingProperty i (p.map x y) :=
  ⟨hom_hasLiftingProperty i p, cell_hasLiftingProperty i p⟩

end
end DaggerModels.TwoObjectCellLifting
