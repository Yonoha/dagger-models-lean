import OriginalSimplicialCategoryBarCoproductDegrees

/-!
# Assemble native simplicial homotopies on an entire native coproduct

Native evaluation preserves coproducts. Keep the actual coproduct index,
apply its full component cylinder and return through the target cofan
same-degree equivalence. No fibrancy assumption is used.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped MonoidalCategory
open DaggerOriginalSimplicialCategoryBarCoproductDegrees
universe u
namespace DaggerNativeSSetCoproductHomotopy
noncomputable section

/-- Native coproduct maps act on the actual component simplex with its actual index. -/
theorem coproductMap_apply {I : Type u} {X Y : I → SSet.{u}}
    (f : ∀ i, X i ⟶ Y i) (n : SimplexCategoryᵒᵖ) (i : I) (a : (X i).obj n) :
    (Limits.Sigma.map f).app n (coproductDegreeEquiv X n ⟨i, a⟩) =
      coproductDegreeEquiv Y n ⟨i, (f i).app n a⟩ :=
  congrFun (NatTrans.congr_app (Sigma.ι_map f i) n) a

/-- The entire cylinder degree retains the actual native component index. -/
def coproductCylinderDegree {I : Type u} {X Y : I → SSet.{u}} {f g : ∀ i, X i ⟶ Y i}
    (h : ∀ i, SSet.Homotopy (f i) (g i)) (n : SimplexCategoryᵒᵖ)
    (p : ((∐ X) ⊗ Δ[1]).obj n) : (∐ Y).obj n :=
  let a := (coproductDegreeEquiv X n).symm p.1
  coproductDegreeEquiv Y n ⟨a.1, (h a.1).h.app n (a.2, p.2)⟩

/-- Each actual component cylinder is retained by the whole coproduct cylinder. -/
theorem coproductCylinderDegree_apply {I : Type u} {X Y : I → SSet.{u}}
    {f g : ∀ i, X i ⟶ Y i} (h : ∀ i, SSet.Homotopy (f i) (g i))
    (n : SimplexCategoryᵒᵖ) (i : I) (a : (X i).obj n) (t : Δ[1].obj n) :
    coproductCylinderDegree h n (coproductDegreeEquiv X n ⟨i, a⟩, t) =
      coproductDegreeEquiv Y n ⟨i, (h i).h.app n (a, t)⟩ := by
  unfold coproductCylinderDegree
  rw [Equiv.symm_apply_apply]

/-- The entire native coproduct cylinder respects every original simplicial operator. -/
theorem coproductCylinderDegree_natural {I : Type u} {X Y : I → SSet.{u}}
    {f g : ∀ i, X i ⟶ Y i} (h : ∀ i, SSet.Homotopy (f i) (g i))
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) (p : ((∐ X) ⊗ Δ[1]).obj n) :
    coproductCylinderDegree h m (((∐ X) ⊗ Δ[1]).map i p) =
      (∐ Y).map i (coproductCylinderDegree h n p) := by
  rcases p with ⟨a, t⟩
  obtain ⟨⟨j, a⟩, rfl⟩ := (coproductDegreeEquiv X n).surjective a
  change coproductCylinderDegree h m
      ((∐ X).map i (coproductDegreeEquiv X n ⟨j, a⟩), Δ[1].map i t) =
    (∐ Y).map i (coproductCylinderDegree h n (coproductDegreeEquiv X n ⟨j, a⟩, t))
  rw [coproductDegreeEquiv_map, coproductCylinderDegree_apply,
    coproductCylinderDegree_apply, coproductDegreeEquiv_map]
  exact congrArg (fun b ↦ coproductDegreeEquiv Y m ⟨j, b⟩)
    (congrFun ((h j).h.naturality i) (a, t))

/-- The assembled native coproduct cylinder is an entire simplicial map. -/
def coproductCylinderMap {I : Type u} {X Y : I → SSet.{u}} {f g : ∀ i, X i ⟶ Y i}
    (h : ∀ i, SSet.Homotopy (f i) (g i)) : (∐ X) ⊗ Δ[1] ⟶ ∐ Y where
  app := coproductCylinderDegree h
  naturality _ _ i := by
    funext p
    exact coproductCylinderDegree_natural h i p

/-- The whole coproduct cylinder starts at the native coproduct of its original first maps. -/
theorem coproductCylinderMap_zero {I : Type u} {X Y : I → SSet.{u}}
    {f g : ∀ i, X i ⟶ Y i} (h : ∀ i, SSet.Homotopy (f i) (g i)) :
    SSet.ι₀ ≫ coproductCylinderMap h = Limits.Sigma.map f := by
  apply NatTrans.ext
  funext n a
  obtain ⟨⟨i, a⟩, rfl⟩ := (coproductDegreeEquiv X n).surjective a
  change coproductCylinderDegree h n
      (coproductDegreeEquiv X n ⟨i, a⟩, ((SSet.ι₀ (X := X i)).app n a).2) =
    (Limits.Sigma.map f).app n (coproductDegreeEquiv X n ⟨i, a⟩)
  rw [coproductCylinderDegree_apply, coproductMap_apply]
  exact congrArg (fun b ↦ coproductDegreeEquiv Y n ⟨i, b⟩)
    (congrFun (NatTrans.congr_app (h i).h₀ n) a)

/-- The whole coproduct cylinder ends at the native coproduct of its original second maps. -/
theorem coproductCylinderMap_one {I : Type u} {X Y : I → SSet.{u}}
    {f g : ∀ i, X i ⟶ Y i} (h : ∀ i, SSet.Homotopy (f i) (g i)) :
    SSet.ι₁ ≫ coproductCylinderMap h = Limits.Sigma.map g := by
  apply NatTrans.ext
  funext n a
  obtain ⟨⟨i, a⟩, rfl⟩ := (coproductDegreeEquiv X n).surjective a
  change coproductCylinderDegree h n
      (coproductDegreeEquiv X n ⟨i, a⟩, ((SSet.ι₁ (X := X i)).app n a).2) =
    (Limits.Sigma.map g).app n (coproductDegreeEquiv X n ⟨i, a⟩)
  rw [coproductCylinderDegree_apply, coproductMap_apply]
  exact congrArg (fun b ↦ coproductDegreeEquiv Y n ⟨i, b⟩)
    (congrFun (NatTrans.congr_app (h i).h₁ n) a)

/-- Native component homotopies give a homotopy of the entire native coproduct maps. -/
def coproductHomotopy {I : Type u} {X Y : I → SSet.{u}} {f g : ∀ i, X i ⟶ Y i}
    (h : ∀ i, SSet.Homotopy (f i) (g i)) :
    SSet.Homotopy (Limits.Sigma.map f) (Limits.Sigma.map g) :=
  SSet.Homotopy.mk (coproductCylinderMap h) (coproductCylinderMap_zero h)
    (coproductCylinderMap_one h)

end
end DaggerNativeSSetCoproductHomotopy
