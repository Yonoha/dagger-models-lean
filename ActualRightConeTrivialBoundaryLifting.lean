import ActualRightConeBoundaryFaces
import NativeBoundaryJoyalMappingWeak

/-! All-monomorphism right lifting gives actual Kan trivial fibrations on right mapping spaces. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
open DaggerActualGeneralRightConeMapping DaggerActualRightConeBoundaryFaces
open DaggerNativeRightConeCofaceGeometry
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualRightConeTrivialBoundaryLifting
noncomputable section

variable {X Y : SSet.{u}} (p : X ⟶ Y) (a b : X.obj (op ⦋0⦌))

private abbrev R := rightMapping X a b
private abbrev S := rightMapping Y (p.app (op ⦋0⦌) a) (p.app (op ⦋0⦌) b)

theorem boundaryMap_square {n : ℕ}
    (φ : (SSet.boundary (n + 1) : SSet.{u}) ⟶ R a b)
    (τ : (Δ[n + 1] : SSet.{u}) ⟶ S p a b)
    (w : φ ≫ DaggerActualGeneralRightConeMapping.map p a b = (SSet.boundary (n + 1)).ι ≫ τ) :
    boundaryMap X a b φ ≫ p = (SSet.boundary (n + 2)).ι ≫
      raw Y (p.app (op ⦋0⦌) a) (p.app (op ⦋0⦌) b) τ := by
  apply SSet.boundary.hom_ext
  intro i
  induction i using Fin.lastCases with
  | last =>
      simp only [← Category.assoc, boundaryMap_collapsed, SSet.boundary.ι_ι]
      rw [SSet.const_comp]
      exact (raw_first Y _ _ τ).symm
  | cast i =>
      simp only [← Category.assoc, boundaryMap_face, SSet.boundary.ι_ι]
      calc
        raw X a b (SSet.boundary.ι i ≫ φ) ≫ p =
            raw Y _ _ ((SSet.boundary.ι i ≫ φ) ≫
              DaggerActualGeneralRightConeMapping.map p a b) :=
          (raw_postcomp X a b p _).symm
        _ = raw Y _ _ (SSet.stdSimplex.δ i ≫ τ) := by
          rw [Category.assoc, w, ← Category.assoc, SSet.boundary.ι_ι]
        _ = SSet.stdSimplex.δ i.castSucc ≫ raw Y _ _ τ := by
          change raw Y _ _ (SSet.stdSimplex.map (SimplexCategory.δ i) ≫ τ) = _
          rw [raw_operator, joinMap_coface]

theorem positive_lift
    (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p) (n : ℕ)
    (φ : (SSet.boundary (n + 1) : SSet.{u}) ⟶ R a b)
    (τ : (Δ[n + 1] : SSet.{u}) ⟶ S p a b)
    (w : φ ≫ DaggerActualGeneralRightConeMapping.map p a b = (SSet.boundary (n + 1)).ι ≫ τ) :
    ∃ r : (Δ[n + 1] : SSet.{u}) ⟶ R a b,
      (SSet.boundary (n + 1)).ι ≫ r = φ ∧
        r ≫ DaggerActualGeneralRightConeMapping.map p a b = τ := by
  have : HasLiftingProperty (SSet.boundary (n + 2)).ι p :=
    hp _ (show Mono (SSet.boundary (n + 2)).ι from inferInstance)
  let sq : CommSq (boundaryMap X a b φ) (SSet.boundary (n + 2)).ι p
      (raw Y _ _ τ) := ⟨boundaryMap_square p a b φ τ w⟩
  let μ := sq.lift
  have hface (i : Fin (n + 2)) :
      SSet.stdSimplex.δ i.castSucc ≫ μ = raw X a b (SSet.boundary.ι i ≫ φ) := by
    rw [← SSet.boundary.ι_ι, Category.assoc]
    change SSet.boundary.ι i.castSucc ≫ ((SSet.boundary (n + 2)).ι ≫ sq.lift) = _
    rw [sq.fac_left, boundaryMap_face]
  have hfirst : face (n + 1) ≫ μ = SSet.const a := by
    change SSet.stdSimplex.δ (Fin.last (n + 2)) ≫ μ = _
    rw [← SSet.boundary.ι_ι, Category.assoc]
    change SSet.boundary.ι (Fin.last (n + 2)) ≫
      ((SSet.boundary (n + 2)).ι ≫ sq.lift) = _
    rw [sq.fac_left, boundaryMap_collapsed]
  have hlast : lastVertex (n + 1) ≫ μ = SSet.const b := by
    have ht := lastVertex_naturality (SimplexCategory.δ (0 : Fin (n + 2)))
    rw [joinMap_coface] at ht
    simp only [SimplexCategory.len_mk] at ht
    rw [← ht, Category.assoc, hface, raw_last]
  let r := ofRaw X a b μ hfirst hlast
  refine ⟨r, ?_, ?_⟩
  · apply SSet.boundary.hom_ext
    intro i
    rw [← Category.assoc, SSet.boundary.ι_ι]
    apply raw_injective X a b
    change raw X a b (SSet.stdSimplex.map (SimplexCategory.δ i) ≫ r) = _
    rw [raw_operator, joinMap_coface]
    change SSet.stdSimplex.δ i.castSucc ≫
      raw X a b (ofRaw X a b μ hfirst hlast) = _
    rw [raw_ofRaw]
    exact hface i
  · apply raw_injective Y (p.app (op ⦋0⦌) a) (p.app (op ⦋0⦌) b)
    rw [raw_postcomp]
    change raw X a b (ofRaw X a b μ hfirst hlast) ≫ p = _
    rw [raw_ofRaw]
    exact sq.fac_right

private theorem zero_face_agreement (i j : Fin 2) (hij : i < j)
    (fi fj : (Δ[0] : SSet.{u}) ⟶ X) :
    SSet.Subcomplex.homOfLE inf_le_left ≫
        ((SSet.stdSimplex.faceSingletonComplIso i).inv ≫ fi) =
      SSet.Subcomplex.homOfLE inf_le_right ≫
        ((SSet.stdSimplex.faceSingletonComplIso j).inv ≫ fj) := by
  apply NatTrans.ext
  funext q z
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h d =>
      have hi := z.property.1
      have hj := z.property.2
      rw [SSet.stdSimplex.mem_face_iff] at hi hj
      simp only [Finset.mem_compl, Finset.mem_singleton] at hi hj
      have hi0 := hi 0
      have hj0 := hj 0
      have hi' : (SSet.stdSimplex.asOrderHom z.val 0).val ≠ i.val :=
        fun h ↦ hi0 (Fin.ext h)
      have hj' : (SSet.stdSimplex.asOrderHom z.val 0).val ≠ j.val :=
        fun h ↦ hj0 (Fin.ext h)
      have ht := (SSet.stdSimplex.asOrderHom z.val 0).isLt
      have hit := i.isLt
      have hjt := j.isLt
      change i.val < j.val at hij
      exact False.elim (by omega)

private def zeroFaces (i : Fin 2) : (Δ[0] : SSet.{u}) ⟶ X :=
  Fin.lastCases (SSet.const a) (fun _ ↦ SSet.const b) i

private def zeroBoundary : (SSet.boundary 1 : SSet.{u}) ⟶ X :=
  DaggerNativeBoundaryCofaceDescent.desc (zeroFaces a b)
    (fun i j hij ↦ zero_face_agreement i j hij _ _)

private theorem zeroBoundary_face0 :
    SSet.boundary.ι (0 : Fin 2) ≫ zeroBoundary a b = SSet.const b := by
  rw [zeroBoundary, DaggerNativeBoundaryCofaceDescent.desc_face]
  rfl

private theorem zeroBoundary_face1 :
    SSet.boundary.ι (1 : Fin 2) ≫ zeroBoundary a b = SSet.const a := by
  rw [zeroBoundary, DaggerNativeBoundaryCofaceDescent.desc_face]
  rfl

theorem zero_lift (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p)
    (φ : (SSet.boundary 0 : SSet.{u}) ⟶ R a b)
    (τ : (Δ[0] : SSet.{u}) ⟶ S p a b) :
    ∃ r : (Δ[0] : SSet.{u}) ⟶ R a b,
      (SSet.boundary 0).ι ≫ r = φ ∧
        r ≫ DaggerActualGeneralRightConeMapping.map p a b = τ := by
  have hw : zeroBoundary a b ≫ p = (SSet.boundary 1).ι ≫ raw Y _ _ τ := by
    apply SSet.boundary.hom_ext
    intro i
    fin_cases i
    · simp only [← Category.assoc, SSet.boundary.ι_ι]
      change (SSet.boundary.ι (0 : Fin 2) ≫ zeroBoundary a b) ≫ p =
        SSet.stdSimplex.δ (0 : Fin 2) ≫ raw Y _ _ τ
      rw [zeroBoundary_face0 a b, SSet.const_comp, ← lastVertex_zero, raw_last]
    · simp only [← Category.assoc, SSet.boundary.ι_ι]
      change (SSet.boundary.ι (1 : Fin 2) ≫ zeroBoundary a b) ≫ p =
        SSet.stdSimplex.δ (1 : Fin 2) ≫ raw Y _ _ τ
      rw [zeroBoundary_face1 a b, SSet.const_comp]
      exact (raw_first Y _ _ τ).symm
  have : HasLiftingProperty (SSet.boundary 1).ι p :=
    hp _ (show Mono (SSet.boundary 1).ι from inferInstance)
  let sq : CommSq (zeroBoundary a b) (SSet.boundary 1).ι p (raw Y _ _ τ) := ⟨hw⟩
  let μ := sq.lift
  have hfirst : face 0 ≫ μ = SSet.const a := by
    change SSet.stdSimplex.δ (1 : Fin 2) ≫ μ = _
    rw [← SSet.boundary.ι_ι, Category.assoc]
    change SSet.boundary.ι (1 : Fin 2) ≫ ((SSet.boundary 1).ι ≫ sq.lift) = _
    rw [sq.fac_left, zeroBoundary_face1]
  have hlast : lastVertex 0 ≫ μ = SSet.const b := by
    rw [lastVertex_zero, ← SSet.boundary.ι_ι, Category.assoc]
    change SSet.boundary.ι (0 : Fin 2) ≫ ((SSet.boundary 1).ι ≫ sq.lift) = _
    rw [sq.fac_left, zeroBoundary_face0]
  let r := ofRaw X a b μ hfirst hlast
  refine ⟨r, ?_, ?_⟩
  · apply NatTrans.ext
    funext q z
    have hz : ¬ Function.Surjective (SSet.stdSimplex.asOrderHom z.val) := z.property
    exact False.elim (hz (fun i ↦ ⟨0, by apply Fin.ext; have ht := i.isLt; omega⟩))
  · apply raw_injective Y (p.app (op ⦋0⦌) a) (p.app (op ⦋0⦌) b)
    rw [raw_postcomp]
    change raw X a b (ofRaw X a b μ hfirst hlast) ≫ p = _
    rw [raw_ofRaw]
    exact sq.fac_right

theorem boundary_lifting (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p) (n : ℕ) :
    HasLiftingProperty (SSet.boundary n).ι (DaggerActualGeneralRightConeMapping.map p a b) := by
  constructor
  intro φ τ sq
  cases n with
  | zero =>
      obtain ⟨r, hleft, hright⟩ := zero_lift p a b hp φ τ
      exact ⟨r, hleft, hright⟩
  | succ n =>
      obtain ⟨r, hleft, hright⟩ := positive_lift p a b hp n φ τ sq.w
      exact ⟨r, hleft, hright⟩

theorem map_trivial_fibration (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p) :
    trivialFibrations SSet.{u} (DaggerActualGeneralRightConeMapping.map p a b) :=
  (DaggerNativeBoundaryJoyalMappingWeak.boundary_rlp_iff_trivialFibration _).mp
    (boundary_lifting p a b hp)

end
end DaggerActualRightConeTrivialBoundaryLifting
