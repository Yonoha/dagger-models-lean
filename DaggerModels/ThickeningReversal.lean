import DaggerModels.OrdinaryRigidification
import DaggerModels.SimplicialOpposite
import Mathlib.AlgebraicTopology.SimplicialSet.Op

/-!
# Reversal of the actual standard simplicial thickening

Lifted Fin reversal sends every original path subset to its image, reverses endpoints,
and preserves inclusion. Its nerve defines an enriched functor to the existing ordinary
opposite. The comparison is natural for every simplex operator and involutive with the
existing double-opposite functor. No nerve comparison or dagger adjunction is asserted.
-/

open CategoryTheory MonoidalCategory BraidedCategory Opposite

universe u

noncomputable section

namespace DaggerModels.OrdinaryRigidification.ThickeningReversal

/-- The exact lifted finite order used by the existing standard thickening. -/
abbrev Point (n : SimplexCategory) := ULift.{u} (Fin (n.len + 1))

/-- Reverse the finite coordinate while retaining its universe lift. -/
def reversePoint (n : SimplexCategory) (i : Point.{u} n) : Point.{u} n :=
  ULift.up i.down.rev

/-- Reversing a lifted coordinate twice returns the original coordinate. -/
@[simp]
theorem reversePoint_reversePoint (n : SimplexCategory) (i : Point.{u} n) :
    reversePoint n (reversePoint n i) = i := by
  cases i
  simp [reversePoint]

/-- Fin reversal reverses the order of the lifted points. -/
theorem reversePoint_antitone (n : SimplexCategory) : Antitone (reversePoint.{u} n) := by
  intro i j hij
  exact Fin.rev_le_rev.mpr hij

/-- Send an original path to its reverse image, with the endpoints swapped. -/
def reversePath (n : SimplexCategory) {i j : Point.{u} n}
    (p : SimplicialThickening.Path i j) :
    SimplicialThickening.Path (reversePoint n j) (reversePoint n i) where
  I := reversePoint n '' p.I
  left := Set.mem_image_of_mem _ p.right
  right := Set.mem_image_of_mem _ p.left
  left_le k hk := by
    obtain ⟨l, hl, rfl⟩ := hk
    exact reversePoint_antitone n (p.le_right l hl)
  le_right k hk := by
    obtain ⟨l, hl, rfl⟩ := hk
    exact reversePoint_antitone n (p.left_le l hl)

/-- Reversal is covariant on path categories: subset inclusions retain their direction. -/
def reversePathFunctor (n : SimplexCategory) (i j : Point.{u} n) :
    SimplicialThickening.Path i j ⥤
      SimplicialThickening.Path (reversePoint n j) (reversePoint n i) where
  obj := reversePath n
  map f := ⟨⟨⟨Set.image_mono f.1.1.1⟩⟩⟩

/-- Reuse the existing bundled thickening without changing its objects or enrichment. -/
abbrev standard (n : SimplexCategory) : SimplicialCat.{u, u} :=
  cosimplicialThickening.obj n

/-- Reverse an object of the original standard thickening. -/
def reverseObject (n : SimplexCategory) (i : (standard.{u} n).Obj) :
    (standard.{u} n).Obj := ⟨reversePoint n i.as⟩

/-- The actual thickening object returns after two reversals. -/
@[simp]
theorem reverseObject_reverseObject (n : SimplexCategory) (i : (standard.{u} n).Obj) :
    reverseObject n (reverseObject n i) = i := by
  cases i
  simp [reverseObject]

/-- The full enriched reversal, with the nerve of path reversal on every hom. -/
def reversal (n : SimplexCategory) : standard.{u} n ⟶ SimplicialCat.opposite (standard n) where
  obj i := op (reverseObject n i)
  map i j := nerveMap (reversePathFunctor n i.as j.as)
  map_id i := by
    have : Quiver.IsThin
        (SimplicialThickening.Path (reversePoint n i.as) (reversePoint n i.as)) :=
      fun _ _ ↦ ⟨by
        intro f g
        cases f
        cases g
        congr 1
        apply ULift.ext
        apply Subsingleton.elim⟩
    ext d x
    dsimp [eId, nerveMap]
    apply CategoryTheory.nerve.ext_of_isThin
    funext a
    apply SimplicialThickening.Path.ext
    change reversePoint n '' {i.as} = {reversePoint n i.as}
    exact Set.image_singleton
  map_comp i j k := by
    have : Quiver.IsThin
        (SimplicialThickening.Path (reversePoint n k.as) (reversePoint n i.as)) :=
      fun _ _ ↦ ⟨by
        intro f g
        cases f
        cases g
        congr 1
        apply ULift.ext
        apply Subsingleton.elim⟩
    ext d p
    dsimp [eComp, nerveMap]
    apply CategoryTheory.nerve.ext_of_isThin
    funext a
    apply SimplicialThickening.Path.ext
    change reversePoint n '' ((p.1.obj a).I ∪ (p.2.obj a).I) =
      (reversePoint n '' (p.2.obj a).I) ∪ (reversePoint n '' (p.1.obj a).I)
    rw [Set.image_union, Set.union_comm]

/-- Reverse again and remove the actual double-opposite object wrappers. -/
def reversalInv (n : SimplexCategory) : SimplicialCat.opposite (standard.{u} n) ⟶ standard n :=
  SimplicialCat.oppositeFunctor.map (reversal n) ≫
    SimplicialCat.doubleOppositeHom (standard n)

/-- Reversal twice is identity with the existing full double-opposite hom. -/
theorem reversal_involutive (n : SimplexCategory) :
    reversal.{u} n ≫ SimplicialCat.oppositeFunctor.map (reversal n) ≫
      SimplicialCat.doubleOppositeHom (standard n) = 𝟙 (standard n) := by
  let f : Point.{u} n →o Point.{u} n :=
    ⟨fun i ↦ reversePoint n (reversePoint n i),
      fun _ _ h ↦ reversePoint_antitone n (reversePoint_antitone n h)⟩
  have hf : f = OrderHom.id := by
    apply OrderHom.ext
    funext i
    exact reversePoint_reversePoint n i
  have h : reversal n ≫ SimplicialCat.oppositeFunctor.map (reversal n) ≫
      SimplicialCat.doubleOppositeHom (standard n) = SimplicialThickening.functor f := by
    apply EnrichedFunctor.ext SSet
    case h_obj =>
      intro i
      rfl
    case h_map =>
      intro i j
      dsimp [reversal, SimplicialCat.oppositeFunctor, SimplicialCat.oppositeMap,
        SimplicialCat.doubleOppositeHom, reverseObject, EnrichedFunctor.comp]
      simp only [Category.comp_id]
      ext d p
      have : Quiver.IsThin (SimplicialThickening.Path (f i.as) (f j.as)) :=
        fun _ _ ↦ ⟨by
          intro a b
          cases a
          cases b
          congr 1
          apply ULift.ext
          apply Subsingleton.elim⟩
      apply CategoryTheory.nerve.ext_of_isThin
      funext a
      apply SimplicialThickening.Path.ext
      exact Set.image_image _ _ _
  rw [h, hf, SimplicialThickening.functor_id]
  rfl

/-- The concrete inverse is a right inverse to the enriched reversal. -/
theorem reversal_hom_inv_id (n : SimplexCategory) :
    reversal.{u} n ≫ reversalInv n = 𝟙 (standard n) :=
  reversal_involutive n

/-- The same concrete inverse is also a left inverse. -/
theorem reversal_inv_hom_id (n : SimplexCategory) :
    reversalInv.{u} n ≫ reversal n = 𝟙 (SimplicialCat.opposite (standard n)) := by
  have : IsSplitMono (reversal.{u} n) :=
    IsSplitMono.mk' ⟨reversalInv n, reversal_hom_inv_id n⟩
  have : IsSplitMono (SimplicialCat.oppositeFunctor.map (reversal.{u} n)) :=
    IsSplitMono.mk' ⟨SimplicialCat.oppositeFunctor.map (reversalInv n), by
      rw [← CategoryTheory.Functor.map_comp, reversal_hom_inv_id,
        CategoryTheory.Functor.map_id]⟩
  have : Mono (SimplicialCat.doubleOppositeHom (standard.{u} n)) := by
    change Mono (SimplicialCat.doubleOppositeIso (standard.{u} n)).hom
    infer_instance
  have : Mono (reversalInv.{u} n) := by
    unfold reversalInv
    infer_instance
  apply (cancel_mono (reversalInv n)).1
  simp only [Category.assoc, reversal_hom_inv_id, Category.comp_id, Category.id_comp]

/-- The actual standard thickening is isomorphic to its ordinary enriched opposite. -/
def reversalIso (n : SimplexCategory) :
    standard.{u} n ≅ SimplicialCat.opposite (standard n) where
  hom := reversal n
  inv := reversalInv n
  hom_inv_id := reversal_hom_inv_id n
  inv_hom_id := reversal_inv_hom_id n

private def antiImagePath {n m : SimplexCategory} (r : Point.{u} n → Point.{u} m)
    (hr : Antitone r) {i j : Point n} (p : SimplicialThickening.Path i j) :
    SimplicialThickening.Path (r j) (r i) where
  I := r '' p.I
  left := Set.mem_image_of_mem _ p.right
  right := Set.mem_image_of_mem _ p.left
  left_le k hk := by
    obtain ⟨l, hl, rfl⟩ := hk
    exact hr (p.le_right l hl)
  le_right k hk := by
    obtain ⟨l, hl, rfl⟩ := hk
    exact hr (p.left_le l hl)

private def antiImagePathFunctor {n m : SimplexCategory} (r : Point.{u} n → Point.{u} m)
    (hr : Antitone r) (i j : Point n) :
    SimplicialThickening.Path i j ⥤ SimplicialThickening.Path (r j) (r i) where
  obj := antiImagePath r hr
  map f := ⟨⟨⟨Set.image_mono f.1.1.1⟩⟩⟩

private theorem pathThin {n : SimplexCategory} (i j : Point.{u} n) :
    Quiver.IsThin (SimplicialThickening.Path i j) :=
  fun _ _ ↦ ⟨by
    intro a b
    cases a
    cases b
    congr 1
    apply ULift.ext
    apply Subsingleton.elim⟩

private def antiImageFunctor {n m : SimplexCategory} (r : Point.{u} n → Point.{u} m)
    (hr : Antitone r) : standard n ⟶ SimplicialCat.opposite (standard m) where
  obj i := op (SimplicialThickening.mk (r i.as))
  map i j := nerveMap (antiImagePathFunctor r hr i.as j.as)
  map_id i := by
    have := pathThin (r i.as) (r i.as)
    ext d x
    dsimp [eId, nerveMap]
    apply CategoryTheory.nerve.ext_of_isThin
    funext a
    apply SimplicialThickening.Path.ext
    change r '' {i.as} = {r i.as}
    exact Set.image_singleton
  map_comp i j k := by
    have := pathThin (r k.as) (r i.as)
    ext d p
    dsimp [eComp, nerveMap]
    apply CategoryTheory.nerve.ext_of_isThin
    funext a
    apply SimplicialThickening.Path.ext
    change r '' ((p.1.obj a).I ∪ (p.2.obj a).I) =
      (r '' (p.2.obj a).I) ∪ (r '' (p.1.obj a).I)
    rw [Set.image_union, Set.union_comm]

private theorem reversal_eq_antiImageFunctor (n : SimplexCategory) :
    reversal.{u} n = antiImageFunctor (reversePoint n) (reversePoint_antitone n) := rfl

private theorem antiImageFunctor_congr {n m : SimplexCategory}
    {r s : Point.{u} n → Point.{u} m} (h : r = s) (hr : Antitone r) (hs : Antitone s) :
    antiImageFunctor r hr = antiImageFunctor s hs := by
  cases h
  rfl

private theorem antiImageFunctor_precomp {n m k : SimplexCategory}
    (f : Point.{u} n →o Point.{u} m) (r : Point m → Point k) (hr : Antitone r) :
    (SimplicialThickening.functor f : standard n ⟶ standard m) ≫ antiImageFunctor r hr =
      antiImageFunctor (fun i ↦ r (f i)) (fun _ _ h ↦ hr (f.monotone h)) := by
  apply EnrichedFunctor.ext SSet
  case h_obj => intro i; rfl
  case h_map =>
    intro i j
    dsimp [antiImageFunctor, EnrichedFunctor.comp]
    ext d p
    have := pathThin (r (f j.as)) (r (f i.as))
    apply CategoryTheory.nerve.ext_of_isThin
    funext a
    apply SimplicialThickening.Path.ext
    exact Set.image_image _ _ _

private theorem antiImageFunctor_postcomp {n m k : SimplexCategory}
    (r : Point.{u} n → Point.{u} m) (hr : Antitone r) (f : Point m →o Point k) :
    antiImageFunctor r hr ≫ SimplicialCat.oppositeFunctor.map
        (SimplicialThickening.functor f : standard m ⟶ standard k) =
      antiImageFunctor (fun i ↦ f (r i)) (fun _ _ h ↦ f.monotone (hr h)) := by
  apply EnrichedFunctor.ext SSet
  case h_obj => intro i; rfl
  case h_map =>
    intro i j
    dsimp [antiImageFunctor, SimplicialCat.oppositeFunctor,
      SimplicialCat.oppositeMap, EnrichedFunctor.comp]
    ext d p
    have := pathThin (f (r j.as)) (f (r i.as))
    apply CategoryTheory.nerve.ext_of_isThin
    funext a
    apply SimplicialThickening.Path.ext
    exact Set.image_image _ _ _

/-- Naturality retains every simplex operator, conjugated by Fin reversal. -/
theorem reversal_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    cosimplicialThickening.{u}.map (SimplexCategory.rev.map f) ≫ reversal m =
      reversal n ≫ SimplicialCat.oppositeFunctor.map (cosimplicialThickening.map f) := by
  rw [reversal_eq_antiImageFunctor, reversal_eq_antiImageFunctor]
  change (SimplicialThickening.functor (SimplexCategory.rev.map f).toOrderHom.uliftMap :
      standard n ⟶ standard m) ≫ antiImageFunctor _ _ =
    antiImageFunctor _ _ ≫ SimplicialCat.oppositeFunctor.map
      (SimplicialThickening.functor f.toOrderHom.uliftMap : standard n ⟶ standard m)
  rw [antiImageFunctor_precomp, antiImageFunctor_postcomp]
  have h : (fun i : Point.{u} n ↦
      reversePoint m ((SimplexCategory.rev.map f).toOrderHom.uliftMap i)) =
      (fun i ↦ f.toOrderHom.uliftMap (reversePoint n i)) := by
    funext i
    apply ULift.ext
    simp [reversePoint, SimplexCategory.rev_map_apply]
  exact antiImageFunctor_congr h _ _

/-- The reversal comparison is a full natural isomorphism of cosimplicial enrichments. -/
def cosimplicialReversalIso :
    SimplexCategory.rev ⋙ cosimplicialThickening.{u} ≅
      cosimplicialThickening ⋙ SimplicialCat.oppositeFunctor :=
  NatIso.ofComponents reversalIso (by
    intro n m f
    exact reversal_naturality f)

end DaggerModels.OrdinaryRigidification.ThickeningReversal
