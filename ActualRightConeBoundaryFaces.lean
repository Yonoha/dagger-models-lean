import NativeBoundaryCofaceDescent
import NativeRightConeCofaceGeometry

/-! The literal boundary maps for right-cone mapping spaces, including their collapsed face. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
open DaggerActualGeneralRightConeMapping DaggerNativeRightConeSimplexPresentation
open DaggerNativeRightConeCofaceGeometry
universe u
namespace DaggerActualRightConeBoundaryFaces
noncomputable section

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))

def raw {n : ℕ} (g : (Δ[n] : SSet.{u}) ⟶ rightMapping X a b) :
    (Δ[n + 1] : SSet.{u}) ⟶ X :=
  (SSet.yonedaEquiv (g ≫ forward X a b)).val

theorem raw_first {n : ℕ} (g : (Δ[n] : SSet.{u}) ⟶ rightMapping X a b) :
    face n ≫ raw X a b g = SSet.const a :=
  (SSet.yonedaEquiv (g ≫ forward X a b)).property.1

theorem raw_last {n : ℕ} (g : (Δ[n] : SSet.{u}) ⟶ rightMapping X a b) :
    lastVertex n ≫ raw X a b g = SSet.const b :=
  (SSet.yonedaEquiv (g ≫ forward X a b)).property.2

theorem raw_operator {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (g : (Δ[n] : SSet.{u}) ⟶ rightMapping X a b) :
    raw X a b (SSet.stdSimplex.map α ≫ g) = joinMap α ≫ raw X a b g := by
  unfold raw
  rw [Category.assoc, SSet.yonedaEquiv_map_comp]
  rfl

theorem raw_postcomp {Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ}
    (g : (Δ[n] : SSet.{u}) ⟶ rightMapping X a b) :
    raw Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b)
        (g ≫ DaggerActualGeneralRightConeMapping.map f a b) = raw X a b g ≫ f := by
  unfold raw
  simp only [SSet.yonedaEquiv_comp]
  exact (Category.assoc _ _ _).symm

theorem raw_injective {n : ℕ} {g h : (Δ[n] : SSet.{u}) ⟶ rightMapping X a b}
    (he : raw X a b g = raw X a b h) : g = h := by
  apply (cancel_mono (presentationIso X a b).hom).mp
  apply SSet.yonedaEquiv.injective
  apply Subtype.ext
  exact he

def ofRaw {n : ℕ} (μ : (Δ[n + 1] : SSet.{u}) ⟶ X)
    (hfirst : face n ≫ μ = SSet.const a) (hlast : lastVertex n ≫ μ = SSet.const b) :
    (Δ[n] : SSet.{u}) ⟶ rightMapping X a b :=
  SSet.yonedaEquiv.symm ((backward X a b).app (op ⦋n⦌) ⟨μ, hfirst, hlast⟩)

theorem raw_ofRaw {n : ℕ} (μ : (Δ[n + 1] : SSet.{u}) ⟶ X)
    (hfirst : face n ≫ μ = SSet.const a) (hlast : lastVertex n ≫ μ = SSet.const b) :
    raw X a b (ofRaw X a b μ hfirst hlast) = μ := by
  unfold raw ofRaw
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact simplex_coneOfSimplex X a b (op ⦋n⦌) ⟨μ, hfirst, hlast⟩

theorem lastVertex_zero : lastVertex.{u} 0 = SSet.stdSimplex.δ (0 : Fin 2) := by
  rw [lastVertex_eq_inr]
  apply congrArg SSet.stdSimplex.map
  ext j : 3
  apply Fin.ext
  fin_cases j
  rfl

theorem raw_boundary_compat {n : ℕ}
    (φ : (SSet.boundary (n + 2) : SSet.{u}) ⟶ rightMapping X a b)
    (i j : Fin (n + 2)) (hij : i ≤ j) :
    SSet.stdSimplex.δ i.castSucc ≫ raw X a b (SSet.boundary.ι j.succ ≫ φ) =
      SSet.stdSimplex.δ j.castSucc ≫ raw X a b (SSet.boundary.ι i.castSucc ≫ φ) := by
  have hw : SSet.stdSimplex.δ i ≫ SSet.boundary.ι j.succ =
      SSet.stdSimplex.δ j ≫ SSet.boundary.ι i.castSucc := by
    apply (cancel_mono (SSet.boundary (n + 2)).ι).mp
    rw [Category.assoc, SSet.boundary.ι_ι, Category.assoc, SSet.boundary.ι_ι]
    exact (SSet.stdSimplex.map_comp _ _).symm.trans
      ((congrArg SSet.stdSimplex.map (SimplexCategory.δ_comp_δ hij)).trans
        (SSet.stdSimplex.map_comp _ _))
  have hv := congrArg (fun g ↦ raw X a b (g ≫ φ)) hw
  simp only [Category.assoc] at hv
  change raw X a b (SSet.stdSimplex.map (SimplexCategory.δ i) ≫
      (SSet.boundary.ι j.succ ≫ φ)) =
    raw X a b (SSet.stdSimplex.map (SimplexCategory.δ j) ≫
      (SSet.boundary.ι i.castSucc ≫ φ)) at hv
  rw [raw_operator, raw_operator, joinMap_coface, joinMap_coface] at hv
  exact hv

def faces {n : ℕ} (φ : (SSet.boundary (n + 1) : SSet.{u}) ⟶ rightMapping X a b)
    (i : Fin (n + 3)) : (Δ[n + 1] : SSet.{u}) ⟶ X :=
  Fin.lastCases (SSet.const a) (fun j ↦ raw X a b (SSet.boundary.ι j ≫ φ)) i

theorem faces_castSucc {n : ℕ}
    (φ : (SSet.boundary (n + 1) : SSet.{u}) ⟶ rightMapping X a b) (i : Fin (n + 2)) :
    faces X a b φ i.castSucc = raw X a b (SSet.boundary.ι i ≫ φ) := by
  simp only [faces, Fin.lastCases_castSucc]

theorem faces_last {n : ℕ}
    (φ : (SSet.boundary (n + 1) : SSet.{u}) ⟶ rightMapping X a b) :
    faces X a b φ (Fin.last (n + 2)) = SSet.const a := by
  simp only [faces, Fin.lastCases_last]

theorem faces_compatible {n : ℕ}
    (φ : (SSet.boundary (n + 1) : SSet.{u}) ⟶ rightMapping X a b)
    (i j : Fin (n + 2)) (hij : i ≤ j) :
    SSet.stdSimplex.δ i ≫ faces X a b φ j.succ =
      SSet.stdSimplex.δ j ≫ faces X a b φ i.castSucc := by
  by_cases hj : j = Fin.last (n + 1)
  · subst j
    rw [show (Fin.last (n + 1)).succ = Fin.last (n + 2) from rfl,
      faces_last, faces_castSucc, SSet.comp_const]
    exact (raw_first X a b _).symm
  · obtain ⟨j', rfl⟩ : ∃ j' : Fin (n + 1), j'.castSucc = j := by
      refine ⟨⟨j.val, ?_⟩, Fin.ext rfl⟩
      have ht : j.val < n + 2 := j.isLt
      have hn : j.val ≠ n + 1 := fun h ↦ hj (Fin.ext h)
      omega
    obtain ⟨i', rfl⟩ : ∃ i' : Fin (n + 1), i'.castSucc = i := by
      refine ⟨⟨i.val, ?_⟩, Fin.ext rfl⟩
      have ht := j'.isLt
      change i.val ≤ j'.val at hij
      omega
    rw [show j'.castSucc.succ = j'.succ.castSucc from Fin.ext rfl,
      faces_castSucc, faces_castSucc]
    cases n with
    | zero =>
      have hi : i' = 0 := by apply Fin.ext; have ht : i'.val < 1 := i'.isLt; omega
      have hj : j' = 0 := by apply Fin.ext; have ht : j'.val < 1 := j'.isLt; omega
      subst i'
      subst j'
      change SSet.stdSimplex.δ (0 : Fin 2) ≫ _ = SSet.stdSimplex.δ (0 : Fin 2) ≫ _
      rw [← lastVertex_zero, raw_last, raw_last]
    | succ n =>
      exact raw_boundary_compat X a b φ i' j' hij

def boundaryMap {n : ℕ}
    (φ : (SSet.boundary (n + 1) : SSet.{u}) ⟶ rightMapping X a b) :
    (SSet.boundary (n + 2) : SSet.{u}) ⟶ X :=
  DaggerNativeBoundaryCofaceDescent.desc (faces X a b φ)
    (DaggerNativeBoundaryCofaceDescent.intersection_compatibility (faces X a b φ)
      (faces_compatible X a b φ))

theorem boundaryMap_face {n : ℕ}
    (φ : (SSet.boundary (n + 1) : SSet.{u}) ⟶ rightMapping X a b) (i : Fin (n + 2)) :
    SSet.boundary.ι i.castSucc ≫ boundaryMap X a b φ =
      raw X a b (SSet.boundary.ι i ≫ φ) := by
  rw [boundaryMap, DaggerNativeBoundaryCofaceDescent.desc_face, faces_castSucc]

theorem boundaryMap_collapsed {n : ℕ}
    (φ : (SSet.boundary (n + 1) : SSet.{u}) ⟶ rightMapping X a b) :
    SSet.boundary.ι (Fin.last (n + 2)) ≫ boundaryMap X a b φ = SSet.const a := by
  rw [boundaryMap, DaggerNativeBoundaryCofaceDescent.desc_face, faces_last]

end
end DaggerActualRightConeBoundaryFaces
