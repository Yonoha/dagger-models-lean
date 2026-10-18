import OrdinaryWordLength
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape

/-! The actual Nat filtration of the same original Q Hom, with full colimit and source data.
No successor pushout, anodyne, weak-equivalence or model-structure claim is made here. -/

open CategoryTheory Limits DaggerModels
open DaggerRelativeOneCellPresentation DaggerOrdinaryReducedWords DaggerOrdinaryWordBoundary
open DaggerOrdinaryCellNormalizer DaggerOrdinaryWordLength

universe u

namespace DaggerOrdinaryWordFiltration

noncomputable section

variable (C : SimplicialCat.{u, u}) (x y : C.Obj) {L : SSet.{u}}
variable (A : L.Subcomplex) (uA : (A : SSet.{u}) ⟶ (x ⟶[SSet] y)) (a b : C.Obj)

/-- The literal accepted stages and their canonical inclusion maps as a Nat diagram. -/
def filtration : ℕ ⥤ SSet.{u} where
  obj n := (stage C x y A uA n a b : SSet.{u})
  map φ := SSet.Subcomplex.homOfLE (stage_monotone C x y A uA a b (leOfHom φ))
  map_id n := by ext q z; rfl
  map_comp φ ψ := by ext q z; rfl

/-- All cocone legs are the literal inclusions into the same original Q Hom. -/
def inclusion : filtration C x y A uA a b ⟶
    (Functor.const ℕ).obj (SimplicialCat.HomQuotient.hom (relations C x y A.ι uA) a b) where
  app n := (stage C x y A uA n a b).ι
  naturality n m φ := by ext q z; rfl

def filtrationCocone : Cocone (filtration C x y A uA a b) :=
  Cocone.mk _ (inclusion C x y A uA a b)

@[simp] theorem successor_map (n : ℕ) :
    (filtration C x y A uA a b).map (homOfLE (Nat.le_succ n)) =
      SSet.Subcomplex.homOfLE (stage_monotone C x y A uA a b (Nat.le_succ n)) := rfl

@[simp] theorem order_successor_map (n : ℕ) :
    (filtration C x y A uA a b).map (homOfLE (Order.le_succ n)) =
      SSet.Subcomplex.homOfLE (stage_monotone C x y A uA a b (Nat.le_succ n)) := rfl

/-- Every original quotient simplex appears at its actual normalized length. -/
theorem simplex_appears (q : SimplexCategoryᵒᵖ)
    (z : SimplicialCat.HomQuotient.HomObj (relations C x y A.ι uA) q a b) :
    ∃ n, ∃ w : (stage C x y A uA n a b).obj q, w.val = z :=
  ⟨(normalize C x y A uA q a b z).1, ⟨z, Nat.le_refl _⟩, rfl⟩

theorem stage_exhaustive : (⨆ n, stage C x y A uA n a b) = ⊤ := by
  ext q z
  simp only [Subfunctor.iSup_obj, Subfunctor.top_obj, Set.mem_iUnion]
  refine iff_of_true ?_ (by trivial)
  exact ⟨(normalize C x y A uA q a b z).1, Nat.le_refl _⟩

/-- Full colimit universal property in SSet, recognized by the canonical evaluation theorem. -/
def filtrationIsColimit : IsColimit (filtrationCocone C x y A uA a b) := by
  apply evaluationJointlyReflectsColimits
  intro q
  apply Types.FilteredColimit.isColimitOf'
  · intro z
    exact ⟨(normalize C x y A uA q a b z).1, ⟨z, Nat.le_refl _⟩, rfl⟩
  · intro n z z' he
    exact ⟨n, 𝟙 n, Subtype.ext he⟩

/-- The full simplicial desc map for an arbitrary cocone over these actual stages. -/
def filtrationDesc (s : Cocone (filtration C x y A uA a b)) :
    SimplicialCat.HomQuotient.hom (relations C x y A.ι uA) a b ⟶ s.pt :=
  (filtrationIsColimit C x y A uA a b).desc s

@[reassoc] theorem filtrationDesc_fac (s : Cocone (filtration C x y A uA a b)) (n : ℕ) :
    (stage C x y A uA n a b).ι ≫ filtrationDesc C x y A uA a b s = s.ι.app n :=
  (filtrationIsColimit C x y A uA a b).fac s n

theorem filtrationDesc_unique (s : Cocone (filtration C x y A uA a b))
    (m : SimplicialCat.HomQuotient.hom (relations C x y A.ι uA) a b ⟶ s.pt)
    (hm : ∀ n, (stage C x y A uA n a b).ι ≫ m = s.ι.app n) :
    m = filtrationDesc C x y A uA a b s :=
  (filtrationIsColimit C x y A uA a b).uniq s m hm

/-- Exact desc value at the original simplex in the stage indexed by its normalized length. -/
theorem filtrationDesc_app (s : Cocone (filtration C x y A uA a b))
    (q : SimplexCategoryᵒᵖ)
    (z : SimplicialCat.HomQuotient.HomObj (relations C x y A.ι uA) q a b) :
    (filtrationDesc C x y A uA a b s).app q z =
      (s.ι.app (normalize C x y A uA q a b z).1).app q ⟨z, Nat.le_refl _⟩ :=
  congrFun (NatTrans.congr_app
    (filtrationDesc_fac C x y A uA a b s (normalize C x y A uA q a b z).1) q)
      ⟨z, Nat.le_refl _⟩

/-- All original F/incl/isoBot/fac data for the original old map, with actual colimit. -/
def transfiniteComposition :
    TransfiniteCompositionOfShape ℕ ((v C x y A.ι uA).map a b) where
  F := filtration C x y A uA a b
  isoBot := (stageZeroIso C x y A uA a b).symm
  incl := inclusion C x y A uA a b
  isColimit := filtrationIsColimit C x y A uA a b
  fac := stageZeroIso_hom_ι C x y A uA a b

end

end DaggerOrdinaryWordFiltration
