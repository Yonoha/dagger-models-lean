import RigidificationCofIntervalHoms

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.BoundaryData

noncomputable section

open PathFacets SimplicialThickening

variable {n : ℕ}

private theorem map_heq {X Y : Type u} [EnrichedCategory SSet.{u} X]
    [EnrichedCategory SSet.{u} Y] {F G : EnrichedFunctor SSet.{u} X Y}
    (h : F = G) (x y : X) : HEq (F.map x y) (G.map x y) := by
  cases h
  rfl

abbrev faceSource (s : Finset (Fin (n + 1))) : SC.{u} :=
  DaggerModels.SimplicialCat.of (SimplicialThickening (ULift.{u} s))

def label (s : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : i ∈ s) :
    (faceSource.{u} s).Obj := .mk (ULift.up ⟨i, hi⟩)

def faceInclusionFunctor {s t : Finset (Fin (n + 1))} (hst : s ⊆ t) :
    faceSource.{u} s ⟶ faceSource.{u} t :=
  SimplicialThickening.functor (faceInclusion hst).uliftMap

def homFromFace (s : Finset (Fin (n + 1))) (i j : Fin (n + 1))
    (hi : i ∈ s) (hj : j ∈ s) :
    (label s i hi ⟶[SSet.{u}] label s j hj) ⟶ hom (ULift.up i) (ULift.up j) :=
  imageHomMap (subsetEmbedding s) (ULift.up ⟨i, hi⟩) (ULift.up ⟨j, hj⟩)

theorem homFromFace_comp {s t : Finset (Fin (n + 1))} (hst : s ⊆ t)
    (i j : Fin (n + 1)) (hi : i ∈ s) (hj : j ∈ s) :
    (faceInclusionFunctor.{u} hst).map (label s i hi) (label s j hj) ≫
      homFromFace t i j (hst hi) (hst hj) = homFromFace s i j hi hj := by
  have h : EnrichedFunctor.comp SSet
      (SimplicialThickening.functor (faceInclusion hst).uliftMap)
      (SimplicialThickening.functor (subsetEmbedding.{u} t).toOrderHom) =
      SimplicialThickening.functor (subsetEmbedding.{u} s).toOrderHom := by
    rw [← SimplicialThickening.functor_comp]
    rfl
  exact eq_of_heq (map_heq h (label s i hi) (label s j hj))

def faceInclusionEmbedding {s t : Finset (Fin (n + 1))} (hst : s ⊆ t) :
    ULift.{u} s ↪o ULift.{u} t where
  toFun x := ⟨faceInclusion hst x.down⟩
  inj' _ _ h := ULift.ext _ _ (Subtype.ext (congrArg (fun x => x.down.val) h))
  map_rel_iff' := Iff.rfl

variable {A : SC.{u}}

def faceMap (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : s ≠ Finset.univ)
    (i j : Fin (n + 2)) (hi : i ∈ s) (hj : j ∈ s) :
    (label s i hi ⟶[SSet.{u}] label s j hj) ⟶ (vertex a i ⟶[SSet.{u}] vertex a j) :=
  (canonicalFaceFunctor a s hs hp).map (label s i hi) (label s j hj)

theorem faceMap_restrict (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (s t : Finset (Fin (n + 2))) (hs : s.Nonempty) (ht : t.Nonempty)
    (hps : s ≠ Finset.univ) (hpt : t ≠ Finset.univ) (hst : s ⊆ t)
    (i j : Fin (n + 2)) (hi : i ∈ s) (hj : j ∈ s) :
    (faceInclusionFunctor.{u} hst).map (label s i hi) (label s j hj) ≫
      faceMap a t ht hpt i j (hst hi) (hst hj) = faceMap a s hs hps i j hi hj := by
  have h := canonicalFaceFunctor_restrict a s t hs ht hps hpt hst
  exact eq_of_heq (map_heq h (label s i hi) (label s j hj))

/-- Strong proper-interval restriction to ANY applicable original proper face. -/
theorem forwardProperMap_restrict
    (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (i j : Fin (n + 2)) (hij : i ≤ j) (hp : ¬ (i = 0 ∧ j = Fin.last (n + 1)))
    (t : Finset (Fin (n + 2))) (ht : t.Nonempty) (hpt : t ≠ Finset.univ)
    (hi : i ∈ t) (hj : j ∈ t) :
    homFromFace t i j hi hj ≫ forwardProperMap a i j hij hp =
      faceMap a t ht hpt i j hi hj := by
  let s := Finset.Icc i j
  let r := s ∩ t
  have his : i ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hij⟩
  have hjs : j ∈ s := Finset.mem_Icc.mpr ⟨hij, le_rfl⟩
  have hir : i ∈ r := Finset.mem_inter.mpr ⟨his, hi⟩
  have hjr : j ∈ r := Finset.mem_inter.mpr ⟨hjs, hj⟩
  have hr : r.Nonempty := ⟨i, hir⟩
  have hrs : r ⊆ s := Finset.inter_subset_left
  have hrt : r ⊆ t := Finset.inter_subset_right
  have hpr : r ≠ Finset.univ := by
    intro h
    apply hpt
    apply Finset.eq_univ_of_forall
    intro x
    apply hrt
    rw [h]
    exact Finset.mem_univ _
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
  have hiso : homFromFace s i j his hjs ≫ forwardProperMap a i j hij hp =
      faceMap a s (intervalNonempty i j hij) (intervalProper i j hp) i j his hjs := by
    change (intervalHomIso i j hij).hom ≫ ((intervalHomIso i j hij).inv ≫ _) = _
    simp only [Iso.hom_inv_id_assoc]
    rfl
  rw [hiso, faceMap_restrict]
  change faceMap a r hr hpr i j hir hjr =
    (faceInclusionFunctor hrt).map (label r i hir) (label r j hjr) ≫
      faceMap a t ht hpt i j (hrt hir) (hrt hjr)
  exact (faceMap_restrict a r t hr ht hpr hpt hrt i j hir hjr).symm

end

end DaggerOrdinaryRigidificationCof.BoundaryData
