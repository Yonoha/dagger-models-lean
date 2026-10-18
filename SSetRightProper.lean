import TopCatModelCategory.ModelCategorySSet
import TopCatModelCategory.SSet.Loop
import TopCatModelCategory.SSet.MinimalFibrationsLemmas
import TopCatModelCategory.TopCat.ToTopExact
import TopCatModelCategory.SSet.ToTopFibration

/-! Right properness for the original geometric weak equivalences of arbitrary simplicial sets.
The chosen lifts retain the full stationary cylinder homotopy and the original pullback maps. -/

open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory MonoidalClosed
open CartesianMonoidalCategory Simplicial SSet.modelCategoryQuillen

universe u

namespace DaggerSSetRightProper

noncomputable section

private theorem path_evaluation {A B : SSet.{u}} (L : A ⟶ B.path) (k : Δ[0] ⟶ Δ[1]) :
    (SSet.stdSimplex.leftUnitor A).inv ≫ k ▷ A ≫ uncurry L =
      L ≫ (MonoidalClosed.pre k).app B ≫ SSet.stdSimplex.ihom₀.hom.app B := by
  rw [← cancel_mono (SSet.stdSimplex.ihom₀.inv.app B)]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [SSet.stdSimplex.ihom₀_inv_app]
  change ((SSet.stdSimplex.leftUnitor A).inv ≫ k ▷ A ≫ uncurry L) ≫
    curry (SSet.stdSimplex.leftUnitor B).hom = L ≫ (MonoidalClosed.pre k).app B
  rw [← curry_natural_left]
  conv_rhs => rw [← curry_uncurry L, ← curry_whiskerRight_comp]
  congr 1
  change Δ[0] ◁ ((SSet.stdSimplex.leftUnitor A).inv ≫ k ▷ A ≫ uncurry L) ≫
    snd _ _ = k ▷ A ≫ uncurry L
  rw [whiskerLeft_snd, SSet.stdSimplex.snd_leftUnitor_inv_assoc]

private theorem path_endpoint₀ {A B : SSet.{u}} (L : A ⟶ B.path) :
    SSet.ι₀ ≫ (β_ A Δ[1]).hom ≫ uncurry L = L ≫ B.pathEv₀ := by
  rw [← SSet.stdSimplex.leftUnitor_inv_map_δ_one_assoc, path_evaluation]
  dsimp only [SSet.pathEv₀, SSet.ihomEv, NatTrans.comp_app]
  rw [SSet.stdSimplex.δ_one]
  rfl

private theorem path_endpoint₁ {A B : SSet.{u}} (L : A ⟶ B.path) :
    SSet.ι₁ ≫ (β_ A Δ[1]).hom ≫ uncurry L = L ≫ B.pathEv₁ := by
  rw [← SSet.stdSimplex.leftUnitor_inv_map_δ_zero_assoc, path_evaluation]
  dsimp only [SSet.pathEv₁, SSet.ihomEv, NatTrans.comp_app]
  rw [SSet.stdSimplex.δ_zero]
  rfl

private theorem pathConst_endpoints (B : SSet.{u}) :
    B.pathConst ≫ B.pathEv₀₁ = lift (𝟙 B) (𝟙 B) := by
  ext : 1
  · rw [Category.assoc, SSet.pathEv₀₁_fst, lift_fst, ← path_endpoint₀]
    dsimp only [SSet.pathConst]
    rw [uncurry_curry]
    rfl
  · rw [Category.assoc, SSet.pathEv₀₁_snd, lift_snd, ← path_endpoint₁]
    dsimp only [SSet.pathConst]
    rw [uncurry_curry]
    rfl

section DeformationRetract

variable {A B : SSet.{u}} (j : A ⟶ B) [Cofibration j] [WeakEquivalence j]
  [IsFibrant A] [IsFibrant B]

/-- The first actual CM4a square, with the original inclusion j. -/
def retractionSquare : CommSq (𝟙 A) j (terminal.from A) (terminal.from B) :=
  ⟨terminalIsTerminal.hom_ext _ _⟩

def retraction : B ⟶ A := (retractionSquare j).lift

omit [IsFibrant B] in
@[reassoc (attr := simp)]
theorem retraction_fac : j ≫ retraction j = 𝟙 A := (retractionSquare j).fac_left

/-- The second actual CM4a square fixes both endpoints and every simplex on j. -/
def stationarySquare : CommSq (j ≫ B.pathConst) j B.pathEv₀₁
    (lift (retraction j ≫ j) (𝟙 B)) where
  w := by
    rw [Category.assoc, pathConst_endpoints]
    simp only [comp_lift, Category.comp_id, ← Category.assoc, retraction_fac,
      Category.id_comp]

def pathLift : B ⟶ B.path := (stationarySquare j).lift

@[reassoc (attr := simp)]
theorem pathLift_fac_left : j ≫ pathLift j = j ≫ B.pathConst :=
  (stationarySquare j).fac_left

@[reassoc (attr := simp)]
theorem pathLift_fac_right : pathLift j ≫ B.pathEv₀₁ = lift (retraction j ≫ j) (𝟙 B) :=
  (stationarySquare j).fac_right

def deformationHom : B ⊗ Δ[1] ⟶ B := (β_ B Δ[1]).hom ≫ uncurry (pathLift j)

@[reassoc (attr := simp)]
theorem deformationHom_endpoint₀ : SSet.ι₀ ≫ deformationHom j = retraction j ≫ j := by
  rw [deformationHom, path_endpoint₀]
  have h := congrArg (fun f ↦ f ≫ fst B B) (pathLift_fac_right j)
  simpa only [Category.assoc, SSet.pathEv₀₁_fst, lift_fst] using h

@[reassoc (attr := simp)]
theorem deformationHom_endpoint₁ : SSet.ι₁ ≫ deformationHom j = 𝟙 B := by
  rw [deformationHom, path_endpoint₁]
  have h := congrArg (fun f ↦ f ≫ snd B B) (pathLift_fac_right j)
  simpa only [Category.assoc, SSet.pathEv₀₁_snd, lift_snd] using h

@[reassoc (attr := simp)]
theorem deformationHom_stationary : j ▷ Δ[1] ≫ deformationHom j = fst A Δ[1] ≫ j := by
  rw [deformationHom, BraidedCategory.braiding_naturality_left_assoc,
    ← uncurry_natural_left, pathLift_fac_left, uncurry_natural_left]
  dsimp only [SSet.pathConst]
  rw [uncurry_curry, whiskerLeft_snd]
  rfl

/-- This original strong deformation retract has inclusion literally j. -/
def deformationRetract : SSet.DeformationRetract A B where
  i := j
  r := retraction j
  retract := retraction_fac j
  h := deformationHom j
  hi := deformationHom_stationary j
  h₀ := deformationHom_endpoint₀ j
  h₁ := deformationHom_endpoint₁ j

end DeformationRetract

section PullbackDeformation

variable {E' E A B : SSet.{u}} (p : E ⟶ B) [Fibration p]
  (j : A ⟶ B) [Cofibration j] [WeakEquivalence j] [IsFibrant A] [IsFibrant B]
  {i : E' ⟶ E} {l : E' ⟶ A} (sq : IsPullback i l p j)

/-- All data returned by the existing full relative homotopy lift, on the original square. -/
structure PullbackDeformationData (sq : IsPullback i l p j) where
  r : E ⟶ E'
  retract : i ≫ r = 𝟙 E'
  homotopy : SSet.Homotopy (r ≫ i) (𝟙 E)
  projection : homotopy.h ≫ p = p ▷ Δ[1] ≫ deformationHom j
  stationary : i ▷ Δ[1] ≫ homotopy.h = fst E' Δ[1] ≫ i
  retraction_projection : r ≫ l = p ≫ retraction j

def pullbackDeformationData : PullbackDeformationData p j sq :=
  Classical.choice (show Nonempty (PullbackDeformationData p j sq) from by
    obtain ⟨r, hr, h, hproj, hstat, hrproj⟩ :=
      SSet.exists_retraction_of_homotopy_of_fibration' p j (retraction j)
        (retraction_fac j) (deformationRetract j).homotopy (deformationHom_stationary j) sq
    exact ⟨{ r := r
             retract := hr
             homotopy := h
             projection := hproj
             stationary := hstat
             retraction_projection := hrproj }⟩)

def pullbackDeformationRetract : SSet.DeformationRetract E' E where
  i := i
  r := (pullbackDeformationData p j sq).r
  retract := (pullbackDeformationData p j sq).retract
  h := (pullbackDeformationData p j sq).homotopy.h
  hi := (pullbackDeformationData p j sq).stationary
  h₀ := (pullbackDeformationData p j sq).homotopy.h₀
  h₁ := (pullbackDeformationData p j sq).homotopy.h₁

include p j sq in
theorem weakEquivalence_of_trivialCofibration_pullback : WeakEquivalence i := by
  letI : IsFibrant E := isFibrant_of_fibration p
  letI : Fibration l := (HomotopicalAlgebra.fibration_iff l).2
    (MorphismProperty.of_isPullback (P := fibrations SSet) sq
      ((HomotopicalAlgebra.fibration_iff p).1 inferInstance))
  letI : IsFibrant E' := isFibrant_of_fibration l
  exact (SSet.weakEquivalence_iff_kanComplexW i).2
    (SSet.KanComplex.W.homotopyEquivHom
      (SSet.HomotopyEquiv.ofDeformationRetract (pullbackDeformationRetract p j sq)))

end PullbackDeformation

abbrev fibrantReplacement : SSet.{u} ⥤ SSet.{u} := SSet.toTop ⋙ TopCat.toSSet

theorem weakEquivalence_fibrantReplacement_map_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    WeakEquivalence (fibrantReplacement.map f) ↔ WeakEquivalence f :=
  (TopCat.weakEquivalence_toSSet_map_iff (SSet.toTop.map f)).trans
    (SSet.modelCategoryQuillen.weakEquivalence_iff f).symm

/-- The original arbitrary pullback top map is a geometric weak equivalence. -/
theorem weakEquivalence_of_isPullback {E' E B' B : SSet.{u}}
    {t : E' ⟶ E} {l : E' ⟶ B'} {r : E ⟶ B} {b : B' ⟶ B}
    [Fibration r] [WeakEquivalence b] (sq : IsPullback t l r b) : WeakEquivalence t := by
  let R := fibrantReplacement.{u}
  letI : WeakEquivalence (R.map b) := (weakEquivalence_fibrantReplacement_map_iff b).2
    inferInstance
  letI : Fibration (R.map r) := by dsimp [R, fibrantReplacement]; infer_instance
  let data := MorphismProperty.factorizationData
    (trivialCofibrations SSet.{u}) (fibrations SSet) (R.map b)
  letI : Cofibration data.i := (mem_trivialCofibrations_iff data.i).1 data.hi |>.1
  letI : WeakEquivalence data.i := (mem_trivialCofibrations_iff data.i).1 data.hi |>.2
  letI : Fibration data.p := (HomotopicalAlgebra.fibration_iff data.p).2 data.hp
  letI : WeakEquivalence data.p := weakEquivalence_of_precomp_of_fac data.fac
  letI : IsFibrant data.Z := isFibrant_of_fibration data.p
  let a := pullback.fst (R.map r) data.p
  let p := pullback.snd (R.map r) data.p
  have rightSq : IsPullback a p (R.map r) data.p := IsPullback.of_hasPullback _ _
  letI : Fibration p := by dsimp [p]; infer_instance
  letI : WeakEquivalence a :=
    SSet.modelCategoryQuillen.weakEquivalence_of_fibration_of_isPullback rightSq.flip
  let h := rightSq.lift (R.map t) (R.map l ≫ data.i) (by
    rw [Category.assoc, data.fac]
    exact (sq.map R).w)
  have ha : h ≫ a = R.map t := rightSq.lift_fst _ _ _
  have hp : h ≫ p = R.map l ≫ data.i := rightSq.lift_snd _ _ _
  have outer : IsPullback (h ≫ a) (R.map l) (R.map r) (data.i ≫ data.p) := by
    simpa only [ha, data.fac] using sq.map R
  have leftSq : IsPullback h (R.map l) p data.i := outer.of_right hp rightSq
  letI : WeakEquivalence h := weakEquivalence_of_trivialCofibration_pullback p data.i leftSq
  have ht : WeakEquivalence (h ≫ a) := inferInstance
  rw [ha] at ht
  exact (weakEquivalence_fibrantReplacement_map_iff t).1 ht

end

end DaggerSSetRightProper
