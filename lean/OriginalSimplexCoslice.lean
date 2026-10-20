import OriginalOrdinalJoinLeft

/-!
# Actual standard-simplex coslices from the native ordinal sum

For a fixed simplex f in X[k], an n-simplex is an actual simplex of X[k+n+1]
whose restriction to the original left block is f. All simplex operators use
the native ordinal-sum functor. Restriction to the original right block gives
an actual simplicial projection to X. No horn-filling property is assumed.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft

universe u

namespace DaggerOriginalSimplexCoslice

/-- The presheaf of original simplices indexed by the native ordinal join with [k]. -/
def joinedPresheaf (k : SimplexCategory) (X : SSet.{u}) : SSet.{u} :=
  (ordinalJoinLeft k).op ⋙ X

/-- The original joined simplices with their left block fixed to the given simplex. -/
def prefixFiber (k : SimplexCategory) (X : SSet.{u}) (f : X.obj (op k)) :
    (joinedPresheaf k X).Subcomplex where
  obj n := {s | X.map (AugmentedSimplexCategory.inl' k n.unop).op s = f}
  map {a b} φ s hs := by
    change X.map (AugmentedSimplexCategory.inl' k b.unop).op
      (X.map ((ordinalJoinLeft k).map φ.unop).op s) = f
    have h := prefix_comp (k := k) φ.unop
    have hop : ((ordinalJoinLeft k).map φ.unop).op ≫
        (AugmentedSimplexCategory.inl' k b.unop).op =
        (AugmentedSimplexCategory.inl' k a.unop).op :=
      congrArg (fun g ↦ g.op) h
    calc
      _ = X.map (((ordinalJoinLeft k).map φ.unop).op ≫
          (AugmentedSimplexCategory.inl' k b.unop).op) s :=
        (congrFun (X.map_comp _ _) s).symm
      _ = X.map (AugmentedSimplexCategory.inl' k a.unop).op s := by rw [hop]
      _ = f := hs

/-- The actual standard-simplex coslice, retaining the original fixed simplex. -/
def simplexCoslice (k : SimplexCategory) (X : SSet.{u}) (f : X.obj (op k)) : SSet.{u} :=
  (prefixFiber k X f : SSet.{u})

/-- The coslice membership condition is exactly restriction along the native left inclusion. -/
theorem mem_prefixFiber_iff (k : SimplexCategory) (X : SSet.{u}) (f : X.obj (op k))
    (n : SimplexCategoryᵒᵖ) (s : (joinedPresheaf k X).obj n) :
    s ∈ (prefixFiber k X f).obj n ↔
      X.map (AugmentedSimplexCategory.inl' k n.unop).op s = f := Iff.rfl

/-- The literal right-block restriction of the original joined presheaf. -/
def suffixProjection (k : SimplexCategory) (X : SSet.{u}) : joinedPresheaf k X ⟶ X where
  app n s := X.map (AugmentedSimplexCategory.inr' k n.unop).op s
  naturality a b φ := by
    funext s
    change X.map (AugmentedSimplexCategory.inr' k b.unop).op
      (X.map ((ordinalJoinLeft k).map φ.unop).op s) =
      X.map φ (X.map (AugmentedSimplexCategory.inr' k a.unop).op s)
    have h := suffix_comp (k := k) φ.unop
    have hop : ((ordinalJoinLeft k).map φ.unop).op ≫
        (AugmentedSimplexCategory.inr' k b.unop).op =
        (AugmentedSimplexCategory.inr' k a.unop).op ≫ φ :=
      congrArg (fun g ↦ g.op) h
    calc
      _ = X.map (((ordinalJoinLeft k).map φ.unop).op ≫
          (AugmentedSimplexCategory.inr' k b.unop).op) s :=
        (congrFun (X.map_comp _ _) s).symm
      _ = X.map ((AugmentedSimplexCategory.inr' k a.unop).op ≫ φ) s := by rw [hop]
      _ = X.map φ (X.map (AugmentedSimplexCategory.inr' k a.unop).op s) :=
        congrFun (X.map_comp _ _) s

/-- The actual coslice projection is the original inclusion followed by right-block restriction. -/
def cosliceProjection (k : SimplexCategory) (X : SSet.{u}) (f : X.obj (op k)) :
    simplexCoslice k X f ⟶ X :=
  (prefixFiber k X f).ι ≫ suffixProjection k X

/-- The projection on every original coslice simplex is precisely its right-block face. -/
theorem cosliceProjection_app (k : SimplexCategory) (X : SSet.{u}) (f : X.obj (op k))
    (n : SimplexCategoryᵒᵖ) (s : (simplexCoslice k X f).obj n) :
    (cosliceProjection k X f).app n s =
      X.map (AugmentedSimplexCategory.inr' k n.unop).op s.val := rfl

end DaggerOriginalSimplexCoslice
