import NativeBisimplicialBoxUnion

/-! Glue actual compatible maps on the two original box subobjects. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBox
open DaggerNativeBisimplicialBoxUnion
universe u
namespace DaggerNativeBisimplicialBoxUnionDesc
noncomputable section

variable {K B : SSet.{u}} (H : K.Subcomplex) (A : B.Subcomplex)
variable {X : BiSSet.{u}} (a : box K (A : SSet.{u}) ⟶ X)
  (b : box (H : SSet.{u}) B ⟶ X)
  (hc : boxMap H.ι (𝟙 (A : SSet.{u})) ≫ a =
    boxMap (𝟙 (H : SSet.{u})) A.ι ≫ b)

theorem union_cover (h v : SimplexCategoryᵒᵖ) (p : ((boxUnion H A).obj h).obj v) :
    (∃ q, ((horizontalInclusion H A).app h).app v q = p) ∨
      (∃ q, ((verticalInclusion H A).app h).app v q = p) := by
  rcases p.property with hx | hy
  · exact Or.inl ⟨(⟨p.val.1, hx⟩, p.val.2), Subtype.ext rfl⟩
  · exact Or.inr ⟨(p.val.1, ⟨p.val.2, hy⟩), Subtype.ext rfl⟩

def unionValue (h v : SimplexCategoryᵒᵖ) (p : ((boxUnion H A).obj h).obj v) :
    (X.obj h).obj v := by
  classical
  exact if hx : p.val.1 ∈ H.obj h then (b.app h).app v (⟨p.val.1, hx⟩, p.val.2)
    else (a.app h).app v (p.val.1, ⟨p.val.2, p.property.resolve_left hx⟩)

theorem unionValue_horizontal (h v : SimplexCategoryᵒᵖ)
    (p : ((box (H : SSet.{u}) B).obj h).obj v) :
    unionValue H A a b h v (((horizontalInclusion H A).app h).app v p) =
      (b.app h).app v p := by
  classical
  unfold unionValue
  dsimp only [horizontalInclusion]
  rw [dif_pos p.1.property]
  exact congrArg ((b.app h).app v) (Prod.ext (Subtype.ext rfl) rfl)

include hc in
theorem unionValue_vertical (h v : SimplexCategoryᵒᵖ)
    (p : ((box K (A : SSet.{u})).obj h).obj v) :
    unionValue H A a b h v (((verticalInclusion H A).app h).app v p) =
      (a.app h).app v p := by
  classical
  by_cases hx : p.1 ∈ H.obj h
  · unfold unionValue
    dsimp only [verticalInclusion]
    rw [dif_pos hx]
    exact (congrFun (NatTrans.congr_app (NatTrans.congr_app hc h) v) (⟨p.1, hx⟩, p.2)).symm
  · unfold unionValue
    dsimp only [verticalInclusion]
    rw [dif_neg hx]
    exact congrArg ((a.app h).app v) (Prod.ext rfl (Subtype.ext rfl))

include hc in
def unionDesc : boxUnion H A ⟶ X where
  app h :=
    { app := unionValue H A a b h
      naturality := by
        intro v w β
        funext p
        rcases union_cover H A h v p with ⟨q, rfl⟩ | ⟨q, rfl⟩
        · change unionValue H A a b h w (((horizontalInclusion H A).app h).app w
              (q.1, B.map β q.2)) =
            (X.obj h).map β (unionValue H A a b h v
              (((horizontalInclusion H A).app h).app v q))
          rw [unionValue_horizontal, unionValue_horizontal]
          exact congrFun ((b.app h).naturality β) q
        · change unionValue H A a b h w (((verticalInclusion H A).app h).app w
              (q.1, (A : SSet.{u}).map β q.2)) =
            (X.obj h).map β (unionValue H A a b h v
              (((verticalInclusion H A).app h).app v q))
          rw [unionValue_vertical H A a b hc, unionValue_vertical H A a b hc]
          exact congrFun ((a.app h).naturality β) q }
  naturality h l α := by
    apply NatTrans.ext
    funext v p
    rcases union_cover H A h v p with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · change unionValue H A a b l v (((horizontalInclusion H A).app l).app v
          ((H : SSet.{u}).map α q.1, q.2)) =
        (X.map α).app v (unionValue H A a b h v
          (((horizontalInclusion H A).app h).app v q))
      rw [unionValue_horizontal, unionValue_horizontal]
      exact congrFun (NatTrans.congr_app (b.naturality α) v) q
    · change unionValue H A a b l v (((verticalInclusion H A).app l).app v
          (K.map α q.1, q.2)) =
        (X.map α).app v (unionValue H A a b h v
          (((verticalInclusion H A).app h).app v q))
      rw [unionValue_vertical H A a b hc, unionValue_vertical H A a b hc]
      exact congrFun (NatTrans.congr_app (a.naturality α) v) q

theorem horizontalInclusion_desc : horizontalInclusion H A ≫ unionDesc H A a b hc = b := by
  apply NatTrans.ext
  funext h
  apply NatTrans.ext
  funext v p
  exact unionValue_horizontal H A a b h v p

theorem verticalInclusion_desc : verticalInclusion H A ≫ unionDesc H A a b hc = a := by
  apply NatTrans.ext
  funext h
  apply NatTrans.ext
  funext v p
  exact unionValue_vertical H A a b hc h v p

end
end DaggerNativeBisimplicialBoxUnionDesc
