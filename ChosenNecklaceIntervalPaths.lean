import ChosenNecklaceIntervalMaps
import ChosenNecklaceEnrichedFunctor

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

variable (T : NecklaceCode) (a b : Fin (T.len + 1)) (hab : a ≤ b)

def intervalOrderMap : Vertices.{u} (intervalCode T a b hab) →o Vertices.{u} T :=
  (intervalEmbedding T a b hab).toOrderHom.uliftMap

theorem intervalOrderMap_injective : Function.Injective (intervalOrderMap.{u} T a b hab) := by
  intro v w h
  apply ULift.ext
  exact (intervalEmbedding T a b hab).injective (congrArg ULift.down h)

def intervalMapPath {v w : Vertices.{u} (intervalCode T a b hab)} (P : JointPath v w) :
    JointPath (intervalOrderMap T a b hab v) (intervalOrderMap T a b hab w) where
  I := intervalOrderMap T a b hab '' P.I
  left := Set.mem_image_of_mem _ P.left
  right := Set.mem_image_of_mem _ P.right
  left_le z hz := by
    obtain ⟨k, hk, rfl⟩ := hz
    exact (intervalOrderMap T a b hab).monotone (P.left_le k hk)
  le_right z hz := by
    obtain ⟨k, hk, rfl⟩ := hz
    exact (intervalOrderMap T a b hab).monotone (P.le_right k hk)
  joints k hk hl hr := by
    obtain ⟨l, he⟩ := intervalEmbedding_preimage T a b hab k
      ((intervalEmbedding_bounds T a b hab v.down).1.trans hl)
      (hr.trans (intervalEmbedding_bounds T a b hab w.down).2)
    have hj : l ∈ (intervalCode T a b hab).joints :=
      (intervalCode_joint T a b hab l).mpr (Or.inr (Or.inr (he.symm ▸ hk)))
    have hleft : v ≤ (ULift.up l : Vertices.{u} (intervalCode T a b hab)) :=
      (intervalEmbedding T a b hab).le_iff_le.mp (he.symm ▸ hl)
    have hright : (ULift.up l : Vertices.{u} (intervalCode T a b hab)) ≤ w :=
      (intervalEmbedding T a b hab).le_iff_le.mp (he.symm ▸ hr)
    exact ⟨ULift.up l, P.joints l hj hleft hright, ULift.ext _ _ he⟩

def intervalUnmapPath {v w : Vertices.{u} (intervalCode T a b hab)}
    (P : JointPath (intervalOrderMap T a b hab v) (intervalOrderMap T a b hab w)) :
    JointPath v w where
  I := intervalOrderMap T a b hab ⁻¹' P.I
  left := P.left
  right := P.right
  left_le k hk := (intervalEmbedding T a b hab).le_iff_le.mp (P.left_le _ hk)
  le_right k hk := (intervalEmbedding T a b hab).le_iff_le.mp (P.le_right _ hk)
  joints k hk hl hr := by
    rcases (intervalCode_joint T a b hab k).mp hk with he | he | hj
    · subst k
      have hv : v = ULift.up 0 := ULift.ext _ _ (le_antisymm hl (Fin.zero_le _))
      exact hv ▸ P.left
    · subst k
      have hw : w = ULift.up (Fin.last (b.val - a.val)) :=
        ULift.ext _ _ (le_antisymm (Fin.le_last _) hr)
      exact hw ▸ P.right
    · exact P.joints _ hj ((intervalOrderMap T a b hab).monotone hl)
        ((intervalOrderMap T a b hab).monotone hr)

def intervalMapPathFunctor (v w : Vertices.{u} (intervalCode T a b hab)) :
    JointPath v w ⥤ JointPath (intervalOrderMap T a b hab v) (intervalOrderMap T a b hab w) where
  obj := intervalMapPath T a b hab
  map h := ⟨⟨⟨Set.image_mono h.1.1.1⟩⟩⟩

def intervalUnmapPathFunctor (v w : Vertices.{u} (intervalCode T a b hab)) :
    JointPath (intervalOrderMap T a b hab v) (intervalOrderMap T a b hab w) ⥤ JointPath v w where
  obj := intervalUnmapPath T a b hab
  map h := ⟨⟨⟨Set.preimage_mono h.1.1.1⟩⟩⟩

theorem intervalUnmap_map {v w : Vertices.{u} (intervalCode T a b hab)} (P : JointPath v w) :
    intervalUnmapPath T a b hab (intervalMapPath T a b hab P) = P := by
  apply JointPath.ext
  exact Set.preimage_image_eq _ (intervalOrderMap_injective T a b hab)

theorem intervalMap_unmap {v w : Vertices.{u} (intervalCode T a b hab)}
    (P : JointPath (intervalOrderMap T a b hab v) (intervalOrderMap T a b hab w)) :
    intervalMapPath T a b hab (intervalUnmapPath T a b hab P) = P := by
  apply JointPath.ext
  ext z
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact hk
  · intro hz
    obtain ⟨k, he⟩ := intervalEmbedding_preimage T a b hab z.down
      ((intervalEmbedding_bounds T a b hab v.down).1.trans (P.left_le z hz))
      ((P.le_right z hz).trans (intervalEmbedding_bounds T a b hab w.down).2)
    have he' : intervalOrderMap T a b hab (ULift.up k) = z := ULift.ext _ _ he
    refine ⟨ULift.up k, ?_, he'⟩
    change intervalOrderMap T a b hab (ULift.up k) ∈ P.I
    rw [he']
    exact hz

/-- Full Hom iso for every pair of vertices of the cut necklace, in every degree. -/
def intervalHomIso (v w : Vertices.{u} (intervalCode T a b hab)) :
    nerve (JointPath v w) ≅
      nerve (JointPath (intervalOrderMap T a b hab v) (intervalOrderMap T a b hab w)) where
  hom := nerveMap (intervalMapPathFunctor T a b hab v w)
  inv := nerveMap (intervalUnmapPathFunctor T a b hab v w)
  hom_inv_id := by
    ext q F
    exact CategoryTheory.Functor.ext (fun i ↦ intervalUnmap_map T a b hab (F.obj i))
  inv_hom_id := by
    ext q F
    exact CategoryTheory.Functor.ext (fun i ↦ intervalMap_unmap T a b hab (F.obj i))

def intervalNC : NC.{u} (intervalCode T a b hab) ⟶ NC.{u} T where
  obj v := ⟨intervalOrderMap T a b hab v.as⟩
  map v w := (intervalHomIso T a b hab v.as w.as).hom
  map_id v := by
    ext q x
    exact CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext Set.image_singleton)
  map_comp v w z := by
    ext q x
    exact CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext (Set.image_union _ _ _))

theorem intervalHomIso_hom (v w : (NC.{u} (intervalCode T a b hab)).Obj) :
    (intervalHomIso T a b hab v.as w.as).hom = (intervalNC T a b hab).map v w := rfl

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
