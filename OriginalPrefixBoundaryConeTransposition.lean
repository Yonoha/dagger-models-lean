import OriginalPrefixBoundaryConeNaturality
import OriginalJoinedBoundaryProjection

/-!
# The original remaining-boundary to vertex-join boundary transposition

Compose the exact cone unit with the actual target map. This gives a natural
map of the original mapping presheaves, commuting with original target maps
and with the exact whole-boundary overlap restriction. This file constructs
the forward map only; its inverse and bijectivity remain separate obligations.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornGeometry DaggerOriginalJoinedPrefixBoundaryFunctor
open DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalPrefixBoundarySuccessorShapes
open DaggerOriginalPrefixBoundarySuccessorIsomorphisms
open DaggerOriginalPrefixBoundaryConeUnit DaggerOriginalPrefixBoundaryConeNaturality
open DaggerOriginalRestPrefixBoundaryFunctor

universe u

namespace DaggerOriginalPrefixBoundaryConeTransposition

noncomputable section

/-- Every original joined suffix projection commutes with the actual target map. -/
theorem joinedSuffixProjection_naturality {X Y : SSet.{u}} (k : SimplexCategory)
    (p : X ⟶ Y) :
    Functor.whiskerLeft (ordinalJoinLeft k).op p ≫ suffixProjection k Y =
      suffixProjection k X ≫ p := by
  ext q s
  change Y.map (AugmentedSimplexCategory.inr' k q.unop).op
      (p.app (op ((ordinalJoinLeft k).obj q.unop)) s) =
    p.app q (X.map (AugmentedSimplexCategory.inr' k q.unop).op s)
  exact congrFun (p.naturality (AugmentedSimplexCategory.inr' k q.unop).op).symm s

/-- Transpose an actual map from the remaining original prefix boundary using the native unit. -/
def prefixConeTranspose {X : SSet.{u}} (k n : ℕ)
    (g : (restPrefixBoundary k n : SSet.{u}) ⟶ X) :
    (prefixBoundary k n : SSet.{u}) ⟶ joinedPresheaf ⦋0⦌ X :=
  prefixConeBoundaryUnit k n ≫ Functor.whiskerLeft (ordinalJoinLeft ⦋0⦌).op g

/-- The transposed suffix restriction is the exact original whole-overlap restriction. -/
theorem prefixConeTranspose_comp_suffix {X : SSet.{u}} (k n : ℕ)
    (g : (restPrefixBoundary k n : SSet.{u}) ⟶ X) :
    prefixConeTranspose k n g ≫ suffixProjection ⦋0⦌ X = boundaryToRest k n ≫ g := by
  rw [prefixConeTranspose, Category.assoc, joinedSuffixProjection_naturality,
    ← Category.assoc, prefixConeBoundaryUnit_comp_suffix]

/-- Transposition retains the exact image under every original target map. -/
theorem prefixConeTranspose_postcomp {X Y : SSet.{u}} (k n : ℕ)
    (g : (restPrefixBoundary k n : SSet.{u}) ⟶ X) (p : X ⟶ Y) :
    prefixConeTranspose k n (g ≫ p) =
      prefixConeTranspose k n g ≫ Functor.whiskerLeft (ordinalJoinLeft ⦋0⦌).op p := by
  ext q s
  rfl

/-- Transposition commutes with every original suffix operator on both boundary shapes. -/
theorem prefixConeTranspose_precomp {X : SSet.{u}} (k : ℕ)
    {m n : SimplexCategory} (β : m ⟶ n)
    (g : (restPrefixBoundary k n.len : SSet.{u}) ⟶ X) :
    prefixBoundaryMap k β ≫ prefixConeTranspose k n.len g =
      prefixConeTranspose k m.len (restPrefixBoundaryMap k β ≫ g) := by
  dsimp only [prefixConeTranspose]
  rw [← Category.assoc, prefixConeBoundaryUnit_naturality, Category.assoc]
  ext q s
  rfl

/-- The presheaf of actual maps from the remaining original successor prefix boundaries. -/
def restBoundaryJoinedPresheaf (k : ℕ) (X : SSet.{u}) : SSet.{u} :=
  (restPrefixBoundaryFunctor k).op ⋙ CategoryTheory.yoneda.obj X

/-- The native cone transpose is an actual map of the original boundary mapping presheaves. -/
def restBoundaryConeTransposition (k : ℕ) (X : SSet.{u}) :
    restBoundaryJoinedPresheaf k X ⟶ boundaryJoinedPresheaf k (joinedPresheaf ⦋0⦌ X) where
  app q g := prefixConeTranspose k q.unop.len g
  naturality a b β := by
    funext g
    change prefixConeTranspose k b.unop.len (restPrefixBoundaryMap k β.unop ≫ g) =
      prefixBoundaryMap k β.unop ≫ prefixConeTranspose k a.unop.len g
    exact (prefixConeTranspose_precomp k β.unop g).symm

/-- Every degree of the presheaf map is the same actual cone transpose. -/
theorem restBoundaryConeTransposition_app (k : ℕ) (X : SSet.{u})
    (q : SimplexCategoryᵒᵖ) (g : (restBoundaryJoinedPresheaf k X).obj q) :
    (restBoundaryConeTransposition k X).app q g = prefixConeTranspose k q.unop.len g := rfl

end

end DaggerOriginalPrefixBoundaryConeTransposition
