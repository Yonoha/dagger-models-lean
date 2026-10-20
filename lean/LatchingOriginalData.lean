import LatchingIntersectionNaturality

/-!
Source-only derived D1 data. This contains no D2 union-W or diagonal-filtration proof.
The maps are the actual outer degeneracies and restrictions of the supplied eta.
-/

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerBisimplicialDiagonal

def latching (B : SimplicialObject SSet.{u}) :
    (n : ℕ) → (B.obj (op ⦋n⦌)).Subcomplex
  | 0 => ⊥
  | n + 1 => ⨆ i : Fin (n + 1), SSet.Subcomplex.range (B.σ i)

theorem sigma_isSplitMono (B : SimplicialObject SSet.{u}) {n : ℕ} (i : Fin (n + 1)) :
    IsSplitMono (B.σ i) :=
  IsSplitMono.mk' { retraction := B.δ i.castSucc, id := B.δ_comp_σ_self }

theorem latching_zero (B : SimplicialObject SSet.{u}) : latching B 0 = ⊥ := rfl

def latchingMap {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B') (n : ℕ) :
    (latching B n : SSet.{u}) ⟶ (latching B' n : SSet.{u}) :=
  SSet.Subcomplex.lift ((latching B n).ι ≫ eta.app (op ⦋n⦌)) (by
    rintro q x ⟨z, rfl⟩
    change (eta.app (op ⦋n⦌)).app q z.val ∈ (latching B' n).obj q
    cases n with
    | zero =>
        have hz := z.property
        change False at hz
        exact hz.elim
    | succ n =>
        have hz := z.property
        simp only [latching, Subfunctor.iSup_obj, Set.mem_iUnion,
          Subfunctor.range_obj] at hz ⊢
        obtain ⟨i, w, hw⟩ := hz
        refine ⟨i, (eta.app (op ⦋n⦌)).app q w, ?_⟩
        have h := congr_fun (congr_app (eta.naturality (SimplexCategory.σ i).op) q) w
        change (B'.σ i).app q ((eta.app (op ⦋n⦌)).app q w) =
          (eta.app (op ⦋n + 1⦌)).app q z.val
        rw [← hw]
        exact h.symm)

theorem latchingMap_app {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B') (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (x : (latching B n).obj q) :
    ((latchingMap eta n).app q x).val = (eta.app (op ⦋n⦌)).app q x.val := rfl

theorem latchingMap_ι {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B') (n : ℕ) :
    (latching B n).ι ≫ eta.app (op ⦋n⦌) = latchingMap eta n ≫ (latching B' n).ι :=
  (SSet.Subcomplex.lift_ι _ _).symm

theorem latchingMap_operator {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B') (n : ℕ)
    {q r : SimplexCategoryᵒᵖ} (beta : q ⟶ r) :
    (latching B n : SSet.{u}).map beta ≫ (latchingMap eta n).app r =
      (latchingMap eta n).app q ≫ (latching B' n : SSet.{u}).map beta :=
  (latchingMap eta n).naturality beta

end DaggerBisimplicialDiagonal
