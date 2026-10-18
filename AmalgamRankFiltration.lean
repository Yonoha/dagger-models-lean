import AmalgamRank
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape

/-! All actual Nat tails of the SAME quotient Hom, with complete colimit and source data.
The NN tail may start at one; no claim about its zero-to-one weak equivalence is made. -/

open CategoryTheory Limits DaggerModels DaggerAmalgamPresentation

universe u

namespace DaggerAmalgamRankFiltration

noncomputable section

variable (C B : SimplicialCat.{u, u}) (c : C.Obj) (b : B.Obj)
variable (shift : Bool) (k : ℕ) (a z : Objects C B c b)

/-- Every tail has literal stage(k+n) objects and subcomplex inclusion transition maps. -/
def filtration : ℕ ⥤ SSet.{u} where
  obj n := (stage C B c b shift (k + n) a z : SSet.{u})
  map φ := SSet.Subcomplex.homOfLE
    (stage_monotone C B c b shift a z (Nat.add_le_add_left (leOfHom φ) k))
  map_id n := by ext q h; rfl
  map_comp φ ψ := by ext q h; rfl

/-- All original target cocone legs are literal inclusions in the SAME quotient Hom. -/
def inclusion : filtration C B c b shift k a z ⟶
    (Functor.const ℕ).obj (SimplicialCat.HomQuotient.hom (relations C B c b) a z) where
  app n := (stage C B c b shift (k + n) a z).ι
  naturality n m φ := by ext q h; rfl

def filtrationCocone : Cocone (filtration C B c b shift k a z) :=
  Cocone.mk _ (inclusion C B c b shift k a z)

@[simp] theorem successor_map (n : ℕ) :
    (filtration C B c b shift k a z).map (homOfLE (Nat.le_succ n)) =
      SSet.Subcomplex.homOfLE
        (stage_monotone C B c b shift a z (Nat.le_succ (k + n))) := rfl

@[simp] theorem order_successor_map (n : ℕ) :
    (filtration C B c b shift k a z).map (homOfLE (Order.le_succ n)) =
      SSet.Subcomplex.homOfLE
        (stage_monotone C B c b shift a z (Nat.le_succ (k + n))) := rfl

theorem rank_le_tail (q : SimplexCategoryᵒᵖ)
    (h : SimplicialCat.HomQuotient.HomObj (relations C B c b) q a z) :
    rankOf C B c b shift q h ≤ k + rankOf C B c b shift q h := by omega

/-- Every original simplex lies in every tail at its actual normalized rank index. -/
theorem simplex_appears (q : SimplexCategoryᵒᵖ)
    (h : SimplicialCat.HomQuotient.HomObj (relations C B c b) q a z) :
    ∃ n, ∃ w : (stage C B c b shift (k + n) a z).obj q, w.val = h :=
  ⟨rankOf C B c b shift q h, ⟨h, rank_le_tail C B c b shift k a z q h⟩, rfl⟩

theorem tail_exhaustive : (⨆ n, stage C B c b shift (k + n) a z) = ⊤ := by
  ext q h
  simp only [Subfunctor.iSup_obj, Subfunctor.top_obj, Set.mem_iUnion]
  exact iff_of_true ⟨rankOf C B c b shift q h, rank_le_tail C B c b shift k a z q h⟩
    (by trivial)

/-- The complete natural colimit UP is the canonical evaluation/filtered-Types criterion. -/
def filtrationIsColimit : IsColimit (filtrationCocone C B c b shift k a z) := by
  apply evaluationJointlyReflectsColimits
  intro q
  apply Types.FilteredColimit.isColimitOf'
  · intro h
    exact ⟨rankOf C B c b shift q h, ⟨h, rank_le_tail C B c b shift k a z q h⟩, rfl⟩
  · intro n h h' he
    exact ⟨n, 𝟙 n, Subtype.ext he⟩

/-- Desc to an arbitrary simplicial cocone, with no restricted target or object map. -/
def filtrationDesc (s : Cocone (filtration C B c b shift k a z)) :
    SimplicialCat.HomQuotient.hom (relations C B c b) a z ⟶ s.pt :=
  (filtrationIsColimit C B c b shift k a z).desc s

@[reassoc] theorem filtrationDesc_fac
    (s : Cocone (filtration C B c b shift k a z)) (n : ℕ) :
    (stage C B c b shift (k + n) a z).ι ≫ filtrationDesc C B c b shift k a z s = s.ι.app n :=
  (filtrationIsColimit C B c b shift k a z).fac s n

theorem filtrationDesc_unique (s : Cocone (filtration C B c b shift k a z))
    (m : SimplicialCat.HomQuotient.hom (relations C B c b) a z ⟶ s.pt)
    (hm : ∀ n, (stage C B c b shift (k + n) a z).ι ≫ m = s.ι.app n) :
    m = filtrationDesc C B c b shift k a z s :=
  (filtrationIsColimit C B c b shift k a z).uniq s m hm

/-- Exact original element formula, valid at ANY stage containing the element. -/
theorem filtrationDesc_app (s : Cocone (filtration C B c b shift k a z))
    (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (h : SimplicialCat.HomQuotient.HomObj (relations C B c b) q a z)
    (hh : rankOf C B c b shift q h ≤ k + n) :
    (filtrationDesc C B c b shift k a z s).app q h = (s.ι.app n).app q ⟨h, hh⟩ :=
  congrFun (NatTrans.congr_app (filtrationDesc_fac C B c b shift k a z s n) q) ⟨h, hh⟩

theorem filtrationDesc_rank_app (s : Cocone (filtration C B c b shift k a z))
    (q : SimplexCategoryᵒᵖ)
    (h : SimplicialCat.HomQuotient.HomObj (relations C B c b) q a z) :
    (filtrationDesc C B c b shift k a z s).app q h =
      (s.ι.app (rankOf C B c b shift q h)).app q
        ⟨h, rank_le_tail C B c b shift k a z q h⟩ :=
  filtrationDesc_app C B c b shift k a z s _ q h _

/-- The full original inclusion of stage k is this actual Nat transfinite composition. -/
def transfiniteComposition :
    TransfiniteCompositionOfShape ℕ (stage C B c b shift k a z).ι where
  F := filtration C B c b shift k a z
  isoBot := Iso.refl _
  incl := inclusion C B c b shift k a z
  isColimit := filtrationIsColimit C B c b shift k a z
  fac := by ext q h; rfl

end
end DaggerAmalgamRankFiltration
