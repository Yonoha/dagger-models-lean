import OriginalCompatibleFaceMaps
import OriginalInnerHornFaces
import RigidificationCofProperLaws

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.InnerHornProperMaps

noncomputable section

open BoundaryData PathFacets SimplicialThickening InnerHornFaces

variable {n : ℕ} {A : SC.{u}}
variable (k : interior n)
variable (D : CompatibleFaceData (n + 1) A (Admissible k))

/-- The full Hom of an interval admitted by the actual inner horn. -/
def forwardProperMap (i j : Fin (n + 2)) (hij : i ≤ j)
    (hp : ¬ (i = 0 ∧ j = Fin.last (n + 1))) :
    hom (ULift.up i) (ULift.up j) ⟶ (D.obj i ⟶[SSet.{u}] D.obj j) :=
  (intervalHomIso i j hij).inv ≫
    (D.canonicalF (Finset.Icc i j) (intervalNonempty i j hij)
      (interval_admissible k i j hp)).map
        (.mk (intervalLeft i j hij)) (.mk (intervalRight i j hij))

/-- Backward Hom maps have the original empty Path Hom as domain. -/
def properMap (i j : Fin (n + 2))
    (hp : ¬ (i = 0 ∧ j = Fin.last (n + 1))) :
    hom (ULift.up i) (ULift.up j) ⟶ (D.obj i ⟶[SSet.{u}] D.obj j) :=
  if hij : i ≤ j then forwardProperMap k D i j hij hp
  else emptyHomMap (show ULift.up j < ULift.up i from lt_of_not_ge hij) _

/-- Restrict a forward interval through any face actually admitted by the horn. -/
theorem forwardProperMap_restrict
    (i j : Fin (n + 2)) (hij : i ≤ j)
    (hp : ¬ (i = 0 ∧ j = Fin.last (n + 1)))
    (t : Finset (Fin (n + 2))) (ht : t.Nonempty) (hpt : Admissible k t)
    (hi : i ∈ t) (hj : j ∈ t) :
    homFromFace t i j hi hj ≫ forwardProperMap k D i j hij hp =
      D.faceMap t ht hpt i j hi hj := by
  let s := Finset.Icc i j
  let r := s ∩ t
  have his : i ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hij⟩
  have hjs : j ∈ s := Finset.mem_Icc.mpr ⟨hij, le_rfl⟩
  have hir : i ∈ r := Finset.mem_inter.mpr ⟨his, hi⟩
  have hjr : j ∈ r := Finset.mem_inter.mpr ⟨hjs, hj⟩
  have hr : r.Nonempty := ⟨i, hir⟩
  have hrs : r ⊆ s := Finset.inter_subset_left
  have hrt : r ⊆ t := Finset.inter_subset_right
  have hps : Admissible k s := interval_admissible k i j hp
  have hpr : Admissible k r := admissible_mono k hpt hrt
  let e := faceInclusionEmbedding.{u} hrt
  have hconv : ∀ x : ULift.{u} t, e (ULift.up ⟨i, hir⟩) ≤ x →
      x ≤ e (ULift.up ⟨j, hjr⟩) → x ∈ Set.range e := by
    intro x hix hxj
    exact ⟨⟨⟨x.down.val, Finset.mem_inter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hix, hxj⟩, x.down.property⟩⟩⟩, rfl⟩
  let ie := convexHomIso e (ULift.up ⟨i, hir⟩) (ULift.up ⟨j, hjr⟩) hconv
  apply (cancel_epi ie.hom).mp
  change (faceInclusionFunctor hrt).map (label r i hir) (label r j hjr) ≫ _ = _
  rw [← Category.assoc, homFromFace_comp]
  rw [← homFromFace_comp hrs i j hir hjr, Category.assoc]
  have hiso : homFromFace s i j his hjs ≫ forwardProperMap k D i j hij hp =
      D.faceMap s (intervalNonempty i j hij) hps i j his hjs := by
    change (intervalHomIso i j hij).hom ≫ ((intervalHomIso i j hij).inv ≫ _) = _
    simp only [Iso.hom_inv_id_assoc]
    rfl
  rw [hiso, D.faceMap_restrict]
  change D.faceMap r hr hpr i j hir hjr =
    (faceInclusionFunctor hrt).map (label r i hir) (label r j hjr) ≫
      D.faceMap t ht hpt i j (hrt hir) (hrt hjr)
  exact (D.faceMap_restrict r t hr ht hpr hpt hrt i j hir hjr).symm

/-- Full restriction to every admitted face, including backward intervals. -/
theorem properMap_restrict
    (i j : Fin (n + 2)) (hp : ¬ (i = 0 ∧ j = Fin.last (n + 1)))
    (t : Finset (Fin (n + 2))) (ht : t.Nonempty) (hpt : Admissible k t)
    (hi : i ∈ t) (hj : j ∈ t) :
    homFromFace t i j hi hj ≫ properMap k D i j hp =
      D.faceMap t ht hpt i j hi hj := by
  by_cases hij : i ≤ j
  · simpa only [properMap, dif_pos hij] using
      forwardProperMap_restrict k D i j hij hp t ht hpt hi hj
  · exact empty_hom_ext (J := ULift.{u} t)
      (i := ULift.up ⟨i, hi⟩) (j := ULift.up ⟨j, hj⟩)
      (show (ULift.up ⟨j, hj⟩ : ULift.{u} t) < ULift.up ⟨i, hi⟩
        from lt_of_not_ge hij) _ _

/-- The diagonal map is the enriched unit on its original Path Hom. -/
theorem properMap_id (i : Fin (n + 2)) :
    eId SSet.{u} (SimplicialThickening.mk (ULift.up i)) ≫
      properMap k D i i (diagonal_proper i) = eId SSet (D.obj i) := by
  let s := Finset.Icc i i
  have hi : i ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩
  have hs := intervalNonempty i i le_rfl
  have hp := interval_admissible k i i (diagonal_proper i)
  rw [← homFromFace_id s i hi, Category.assoc,
    properMap_restrict k D i i _ s hs hp hi hi]
  exact (D.canonicalF s hs hp).map_id (label s i hi)

/-- Composable intervals use one admitted interval face and its full Hom maps. -/
theorem properMap_comp_forward
    (i j l : Fin (n + 2)) (hij : i ≤ j) (hjl : j ≤ l)
    (hpil : ¬ (i = 0 ∧ l = Fin.last (n + 1)))
    (hpij : ¬ (i = 0 ∧ j = Fin.last (n + 1)))
    (hpjl : ¬ (j = 0 ∧ l = Fin.last (n + 1))) :
    compose (ULift.up i) (ULift.up j) (ULift.up l) ≫
      properMap k D i l hpil =
        (properMap k D i j hpij ⊗ₘ properMap k D j l hpjl) ≫
          eComp SSet (D.obj i) (D.obj j) (D.obj l) := by
  let s := Finset.Icc i l
  have hil := hij.trans hjl
  have hi : i ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hil⟩
  have hj : j ∈ s := Finset.mem_Icc.mpr ⟨hij, hjl⟩
  have hl : l ∈ s := Finset.mem_Icc.mpr ⟨hil, le_rfl⟩
  have hs := intervalNonempty i l hil
  have hp := interval_admissible k i l hpil
  let e := subsetEmbedding.{u} s
  have hconv₁ : ∀ x : vertices.{u} (n + 1),
      e (ULift.up ⟨i, hi⟩) ≤ x → x ≤ e (ULift.up ⟨j, hj⟩) → x ∈ Set.range e := by
    intro x hx hy
    exact ⟨⟨⟨x.down, Finset.mem_Icc.mpr ⟨hx, hy.trans hjl⟩⟩⟩, rfl⟩
  have hconv₂ : ∀ x : vertices.{u} (n + 1),
      e (ULift.up ⟨j, hj⟩) ≤ x → x ≤ e (ULift.up ⟨l, hl⟩) → x ∈ Set.range e := by
    intro x hx hy
    exact ⟨⟨⟨x.down, Finset.mem_Icc.mpr ⟨hij.trans hx, hy⟩⟩⟩, rfl⟩
  let e₁ := convexHomIso e (ULift.up ⟨i, hi⟩) (ULift.up ⟨j, hj⟩) hconv₁
  let e₂ := convexHomIso e (ULift.up ⟨j, hj⟩) (ULift.up ⟨l, hl⟩) hconv₂
  apply (cancel_epi (e₁.hom ⊗ₘ e₂.hom)).mp
  change (homFromFace s i j hi hj ⊗ₘ homFromFace s j l hj hl) ≫ _ =
    (homFromFace s i j hi hj ⊗ₘ homFromFace s j l hj hl) ≫
      (properMap k D i j hpij ⊗ₘ properMap k D j l hpjl) ≫ _
  rw [tensorHom_comp_tensorHom_assoc]
  rw [properMap_restrict k D i j hpij s hs hp hi hj,
    properMap_restrict k D j l hpjl s hs hp hj hl]
  have hc := (SimplicialThickening.functor e.toOrderHom).map_comp
    (label s i hi) (label s j hj) (label s l hl)
  have hc' : eComp SSet.{u} (label s i hi) (label s j hj) (label s l hl) ≫
      homFromFace s i l hi hl =
      (homFromFace s i j hi hj ⊗ₘ homFromFace s j l hj hl) ≫
        compose (ULift.up i) (ULift.up j) (ULift.up l) := hc
  change _ = (D.faceMap s hs hp i j hi hj ⊗ₘ D.faceMap s hs hp j l hj hl) ≫ _
  rw [← Category.assoc, ← hc', Category.assoc,
    properMap_restrict k D i l hpil s hs hp hi hl]
  exact (D.canonicalF s hs hp).map_comp
    (label s i hi) (label s j hj) (label s l hl)

end

end DaggerOrdinaryRigidificationCof.InnerHornProperMaps
