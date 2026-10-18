import OriginalDiagonalStages
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! D3 source implementation only: literal Nat stages and their complete colimit UP. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerBisimplicialDiagonal

universe u
namespace DaggerOriginalDiagonalStages
noncomputable section

/-- The original Nat diagram consists only of canonical subcomplex inclusions. -/
def filtration (B : SimplicialObject SSet.{u}) : ℕ ⥤ SSet.{u} where
  obj r := (stage B r : SSet.{u})
  map phi := SSet.Subcomplex.homOfLE (stage_monotone B (leOfHom phi))
  map_id r := by ext q x; rfl
  map_comp phi psi := by ext q x; rfl

instance filtration_map_mono (B : SimplicialObject SSet.{u})
    {r s : ℕ} (phi : r ⟶ s) : Mono ((filtration B).map phi) := by
  change Mono (SSet.Subcomplex.homOfLE (stage_monotone B (leOfHom phi)))
  infer_instance

def inclusion (B : SimplicialObject SSet.{u}) :
    filtration B ⟶ (Functor.const ℕ).obj (DaggerBisimplicialDiagonal.diag B) where
  app r := (stage B r).ι
  naturality r s phi := by ext q x; rfl

def filtrationCocone (B : SimplicialObject SSet.{u}) : Cocone (filtration B) :=
  Cocone.mk (DaggerBisimplicialDiagonal.diag B) (inclusion B)

@[simp] theorem filtration_successor (B : SimplicialObject SSet.{u}) (r : ℕ) :
    (filtration B).map (homOfLE (Nat.le_succ r)) =
      SSet.Subcomplex.homOfLE (stage_le_succ B r) := rfl

/-- Each evaluation cocone is colimiting, including empty degrees at every universe. -/
def filtrationDegreeIsColimit (B : SimplicialObject SSet.{u}) (q : SimplexCategoryᵒᵖ) :
    IsColimit (((evaluation SimplexCategoryᵒᵖ (Type u)).obj q).mapCocone
      (filtrationCocone B)) := by
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    exact ⟨q.unop.len + 1, ⟨x, simplex_mem_stage B q x⟩, rfl⟩
  · intro r x y h
    exact ⟨r, 𝟙 r, Subtype.ext h⟩

/-- Existing evaluation reflection gives the full simplicial desc/fac/uniq. -/
def filtrationIsColimit (B : SimplicialObject SSet.{u}) :
    IsColimit (filtrationCocone B) :=
  evaluationJointlyReflectsColimits _ (filtrationDegreeIsColimit B)

/-- Full desc into an arbitrary supplied target cocone, not a vertex-only function. -/
def filtrationDesc (B : SimplicialObject SSet.{u}) (s : Cocone (filtration B)) :
    DaggerBisimplicialDiagonal.diag B ⟶ s.pt := (filtrationIsColimit B).desc s

@[reassoc] theorem filtrationDesc_fac (B : SimplicialObject SSet.{u})
    (s : Cocone (filtration B)) (r : ℕ) :
    (stage B r).ι ≫ filtrationDesc B s = s.ι.app r :=
  (filtrationIsColimit B).fac s r

theorem filtrationDesc_unique (B : SimplicialObject SSet.{u})
    (s : Cocone (filtration B)) (m : DaggerBisimplicialDiagonal.diag B ⟶ s.pt)
    (hm : ∀ r, (stage B r).ι ≫ m = s.ι.app r) : m = filtrationDesc B s :=
  (filtrationIsColimit B).uniq s m hm

theorem filtrationDesc_operator (B : SimplicialObject SSet.{u})
    (s : Cocone (filtration B)) {q q' : SimplexCategoryᵒᵖ} (beta : q ⟶ q') :
    (DaggerBisimplicialDiagonal.diag B).map beta ≫ (filtrationDesc B s).app q' =
      (filtrationDesc B s).app q ≫ s.pt.map beta := (filtrationDesc B s).naturality beta

/-- The desc evaluates at the exhaustive identity witness in degree q. -/
theorem filtrationDesc_app (B : SimplicialObject SSet.{u}) (s : Cocone (filtration B))
    (q : SimplexCategoryᵒᵖ) (x : (DaggerBisimplicialDiagonal.diag B).obj q) :
    (filtrationDesc B s).app q x =
      (s.ι.app (q.unop.len + 1)).app q ⟨x, simplex_mem_stage B q x⟩ :=
  congrFun (NatTrans.congr_app (filtrationDesc_fac B s (q.unop.len + 1)) q)
    ⟨x, simplex_mem_stage B q x⟩

def filtrationNatTrans {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B') :
    filtration B ⟶ filtration B' where
  app r := stageMap eta r
  naturality _ _ phi := stageMap_naturality eta (leOfHom phi)

theorem filtration_leg {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B') (r : ℕ) :
    (filtrationCocone B).ι.app r ≫ diagMap eta =
      (filtrationNatTrans eta).app r ≫ (filtrationCocone B').ι.app r :=
  (stageMap_ι eta r).symm

/-- Pull back a supplied target cocone along the literal stage natural transformation. -/
def comparisonCocone {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B')
    (s : Cocone (filtration B')) : Cocone (filtration B) :=
  Cocone.mk s.pt (filtrationNatTrans eta ≫ s.ι)

/-- The arbitrary-target final desc commutes with the SAME diagonal map. -/
theorem filtrationDesc_naturality {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B')
    (s : Cocone (filtration B')) :
    diagMap eta ≫ filtrationDesc B' s = filtrationDesc B (comparisonCocone eta s) := by
  apply filtrationDesc_unique B (comparisonCocone eta s)
  intro r
  rw [← Category.assoc, ← stageMap_ι eta r, Category.assoc, filtrationDesc_fac]
  rfl

end
end DaggerOriginalDiagonalStages
