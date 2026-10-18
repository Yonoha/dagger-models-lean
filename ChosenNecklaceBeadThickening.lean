import ChosenNecklaceEnrichedFunctor
import ChosenNecklaceSingleThickening
import ChosenNecklaceBeadCoordinates

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

variable {T : NecklaceCode} (b : T.Bead)

def beadOrderMap : ULift.{u} (Fin (b.length + 1)) →o Vertices.{u} T :=
  b.embedding.toOrderHom.uliftMap

theorem beadOrderMap_injective : Function.Injective (beadOrderMap.{u} b) := by
  intro a c h
  apply ULift.ext
  exact b.embedding.injective (congrArg ULift.down h)

theorem joint_in_bead (k : Fin (T.len + 1)) (hk : k ∈ T.joints)
    (hl : b.left ≤ k) (hr : k ≤ b.right) : k = b.left ∨ k = b.right := by
  by_cases hleft : k = b.left
  · exact Or.inl hleft
  by_cases hright : k = b.right
  · exact Or.inr hright
  exact (b.no_joint k hk (lt_of_le_of_ne hl (Ne.symm hleft))
    (lt_of_le_of_ne hr hright)).elim

def beadMapPath {a c : ULift.{u} (Fin (b.length + 1))}
    (P : SimplicialThickening.Path a c) :
    JointPath (beadOrderMap b a) (beadOrderMap b c) where
  I := beadOrderMap b '' P.I
  left := Set.mem_image_of_mem _ P.left
  right := Set.mem_image_of_mem _ P.right
  left_le v hv := by
    obtain ⟨w, hw, rfl⟩ := hv
    exact (beadOrderMap b).monotone (P.left_le w hw)
  le_right v hv := by
    obtain ⟨w, hw, rfl⟩ := hv
    exact (beadOrderMap b).monotone (P.le_right w hw)
  joints k hk hl hr := by
    change b.embedding a.down ≤ k at hl
    change k ≤ b.embedding c.down at hr
    have ha := Finset.mem_Icc.mp (Finset.orderEmbOfFin_mem b.interval b.card_interval a.down)
    have hc := Finset.mem_Icc.mp (Finset.orderEmbOfFin_mem b.interval b.card_interval c.down)
    rcases joint_in_bead b k hk (ha.1.trans hl) (hr.trans hc.2) with he | he
    · have h : beadOrderMap b a = ULift.up k :=
        ULift.ext _ _ (le_antisymm hl (he.symm ▸ ha.1))
      exact h ▸ Set.mem_image_of_mem (beadOrderMap b) P.left
    · have h : beadOrderMap b c = ULift.up k :=
        ULift.ext _ _ (le_antisymm (he.symm ▸ hc.2) hr)
      exact h ▸ Set.mem_image_of_mem (beadOrderMap b) P.right

def beadMapPathFunctor (a c : ULift.{u} (Fin (b.length + 1))) :
    SimplicialThickening.Path a c ⥤ JointPath (beadOrderMap b a) (beadOrderMap b c) where
  obj := beadMapPath b
  map h := ⟨⟨⟨Set.image_mono h.1.1.1⟩⟩⟩

def beadNC : DaggerChosenRigidificationNecklace.T.{u}.obj ⦋b.length⦌ ⟶ NC.{u} T where
  obj a := ⟨beadOrderMap b a.as⟩
  map a c := nerveMap (beadMapPathFunctor b a.as c.as)
  map_id a := by
    ext q x
    exact CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext Set.image_singleton)
  map_comp a c d := by
    ext q x
    exact CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext (Set.image_union _ _ _))

theorem beadNC_obj (a : SimplicialThickening (ULift.{u} (Fin (b.length + 1)))) :
    (beadNC b).obj a = ⟨ULift.up (b.embedding a.as.down)⟩ := rfl

theorem beadNC_map_I (a c : SimplicialThickening (ULift.{u} (Fin (b.length + 1))))
    (n : ℕ) (P : (a ⟶[SSet.{u}] c).obj (op ⦋n⦌)) (i : Fin (n + 1)) :
    ((((beadNC b).map a c).app _ P).obj i).I = beadOrderMap b '' (P.obj i).I := rfl

theorem exists_bead_preimage (v : Vertices.{u} T) (hv : v.down ∈ b.interval) :
    ∃ w, beadOrderMap b w = v := by
  have h : v.down ∈ Set.range b.embedding := by
    simpa only [Bead.embedding, Finset.range_orderEmbOfFin] using hv
  obtain ⟨w, hw⟩ := h
  exact ⟨ULift.up w, ULift.ext _ _ hw⟩

def beadUnmapPath {a c : ULift.{u} (Fin (b.length + 1))}
    (P : JointPath (beadOrderMap b a) (beadOrderMap b c)) :
    SimplicialThickening.Path a c where
  I := beadOrderMap b ⁻¹' P.I
  left := P.left
  right := P.right
  left_le v hv := by
    exact b.embedding.le_iff_le.mp (P.left_le (beadOrderMap b v) hv)
  le_right v hv := by
    exact b.embedding.le_iff_le.mp (P.le_right (beadOrderMap b v) hv)

def beadUnmapPathFunctor (a c : ULift.{u} (Fin (b.length + 1))) :
    JointPath (beadOrderMap b a) (beadOrderMap b c) ⥤ SimplicialThickening.Path a c where
  obj := beadUnmapPath b
  map h := ⟨⟨⟨Set.preimage_mono h.1.1.1⟩⟩⟩

theorem beadUnmap_map {a c : ULift.{u} (Fin (b.length + 1))}
    (P : SimplicialThickening.Path a c) : beadUnmapPath b (beadMapPath b P) = P := by
  apply SimplicialThickening.Path.ext
  exact Set.preimage_image_eq _ (beadOrderMap_injective b)

theorem beadMap_unmap {a c : ULift.{u} (Fin (b.length + 1))}
    (P : JointPath (beadOrderMap b a) (beadOrderMap b c)) :
    beadMapPath b (beadUnmapPath b P) = P := by
  apply JointPath.ext
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hv
    have ha := Finset.mem_Icc.mp (Finset.orderEmbOfFin_mem b.interval b.card_interval a.down)
    have hc := Finset.mem_Icc.mp (Finset.orderEmbOfFin_mem b.interval b.card_interval c.down)
    have hl : b.embedding a.down ≤ v.down := P.left_le v hv
    have hr : v.down ≤ b.embedding c.down := P.le_right v hv
    have hvi : v.down ∈ b.interval := Finset.mem_Icc.mpr
      ⟨ha.1.trans hl, hr.trans hc.2⟩
    obtain ⟨w, rfl⟩ := exists_bead_preimage b v hvi
    exact ⟨w, hv, rfl⟩

def beadHomIso (a c : ULift.{u} (Fin (b.length + 1))) :
    nerve (SimplicialThickening.Path a c) ≅
      nerve (JointPath (beadOrderMap b a) (beadOrderMap b c)) where
  hom := nerveMap (beadMapPathFunctor b a c)
  inv := nerveMap (beadUnmapPathFunctor b a c)
  hom_inv_id := by
    ext q F
    exact CategoryTheory.Functor.ext (fun i ↦ beadUnmap_map b (F.obj i))
  inv_hom_id := by
    ext q F
    exact CategoryTheory.Functor.ext (fun i ↦ beadMap_unmap b (F.obj i))

theorem beadHomIso_hom (a c : SimplicialThickening (ULift.{u} (Fin (b.length + 1)))) :
    (beadHomIso b a.as c.as).hom = (beadNC b).map a c := rfl

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
