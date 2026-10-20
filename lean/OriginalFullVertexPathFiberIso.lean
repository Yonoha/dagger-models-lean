import OriginalFullVertexPathFiber

/-!
# Fixed-endpoint path fibers in a full vertex subcomplex

The actual path fiber formed from the retained simplicial internal hom is
unchanged when both endpoints lie in a full vertex subcomplex. The inverse
uses unique factorization of the uncurried path cylinder.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial MonoidalCategory
  MonoidalClosed CartesianMonoidalCategory
open DaggerOriginalFullVertexSubcomplex

universe u

namespace DaggerOriginalFullVertexSubcomplex

noncomputable section

private theorem subvertex_mem {X : SSet.{u}}
    (V : Set (X.obj (op ⦋0⦌)))
    (a : (fullVertexSubcomplex X V : SSet).obj (op ⦋0⦌)) : a.val ∈ V := by
  have h := a.property (𝟙 ⦋0⦌)
  simpa only [op_id, FunctorToTypes.map_id_apply] using h

private theorem pathEv_zero_natural {A X : SSet.{u}} (i : A ⟶ X) :
    ((ihom Δ[1]).map i) ≫ X.pathEv₀ = A.pathEv₀ ≫ i := by
  exact ((Δ[1].ihomEv (SSet.stdSimplex.obj₀Equiv.symm 0)).naturality i)

private theorem pathEv_one_natural {A X : SSet.{u}} (i : A ⟶ X) :
    ((ihom Δ[1]).map i) ≫ X.pathEv₁ = A.pathEv₁ ≫ i := by
  exact ((Δ[1].ihomEv (SSet.stdSimplex.obj₀Equiv.symm 1)).naturality i)

private theorem path_map_mono {A X : SSet.{u}} (i : A ⟶ X) [Mono i] :
    Mono ((ihom Δ[1]).map i) := by
  constructor
  intro Z f g h
  apply uncurry_injective
  have hh := congrArg (fun q : Z ⟶ X.path => uncurry q) h
  dsimp only at hh
  rw [uncurry_natural_right, uncurry_natural_right] at hh
  exact (cancel_mono i).mp hh

/-- The inverse comparison, together with its defining equality after
inclusion in the ambient path object. -/
private def strictPathFiberInverseData {X : SSet.{u}}
    (V : Set (X.obj (op ⦋0⦌)))
    (a b : (fullVertexSubcomplex X V : SSet).obj (op ⦋0⦌)) :
    let A := fullVertexSubcomplex X V
    let PX := strictPathFiber X a.val b.val
    let PA := strictPathFiber (A : SSet) a b
    {g : (PX : SSet) ⟶ (PA : SSet) //
      g ≫ PA.ι ≫ ((ihom Δ[1]).map A.ι) = PX.ι} := by
  let A := fullVertexSubcomplex X V
  let PX := strictPathFiber X a.val b.val
  let PA := strictPathFiber (A : SSet) a b
  let i := A.ι
  let q := PX.ι
  have hpair : q ≫ X.pathEv₀₁ = SSet.const (X := (PX : SSet))
      ((a.val, b.val) : (X ⊗ X : SSet.{u}) _⦋0⦌) :=
    SSet.Subcomplex.fiber_ι_comp X.pathEv₀₁
      ((a.val, b.val) : (X ⊗ X : SSet.{u}) _⦋0⦌)
  have hp₀ : q ≫ X.pathEv₀ = SSet.const a.val := by
    have h := congrArg (fun f : (PX : SSet) ⟶ X ⊗ X => f ≫ fst X X) hpair
    simpa only [Category.assoc, SSet.pathEv₀₁_fst, SSet.const_comp] using h
  have hp₁ : q ≫ X.pathEv₁ = SSet.const b.val := by
    have h := congrArg (fun f : (PX : SSet) ⟶ X ⊗ X => f ≫ snd X X) hpair
    simpa only [Category.assoc, SSet.pathEv₀₁_snd, SSet.const_comp] using h
  have h₀ (z : (PX : SSet).obj (op ⦋0⦌)) :
      (uncurry q).app (op ⦋0⦌)
        ⟨SSet.stdSimplex.obj₀Equiv.symm 0, z⟩ = a.val := by
    rw [uncurry_path_endpoint_zero]
    have h := congrArg (fun f : (PX : SSet) ⟶ X => f.app (op ⦋0⦌) z) hp₀
    simpa [SSet.const] using h
  have h₁ (z : (PX : SSet).obj (op ⦋0⦌)) :
      (uncurry q).app (op ⦋0⦌)
        ⟨SSet.stdSimplex.obj₀Equiv.symm 1, z⟩ = b.val := by
    rw [uncurry_path_endpoint_one]
    have h := congrArg (fun f : (PX : SSet) ⟶ X => f.app (op ⦋0⦌) z) hp₁
    simpa [SSet.const] using h
  let fA := strictEndpointCylinderLift V a.val b.val
    (subvertex_mem V a) (subvertex_mem V b) (uncurry q) h₀ h₁
  let qA : (PX : SSet) ⟶ (A : SSet).path := curry fA
  have hpost : qA ≫ ((ihom Δ[1]).map i) = q := by
    calc
      qA ≫ ((ihom Δ[1]).map i) = curry (fA ≫ i) :=
        (curry_natural_right fA i).symm
      _ = curry (uncurry q) := by
        rw [strictEndpointCylinderLift_ι]
      _ = q := curry_uncurry q
  have hp₀A : qA ≫ (A : SSet).pathEv₀ = SSet.const a := by
    apply (cancel_mono i).mp
    calc
      (qA ≫ (A : SSet).pathEv₀) ≫ i =
          qA ≫ ((ihom Δ[1]).map i) ≫ X.pathEv₀ := by
        rw [Category.assoc, ← pathEv_zero_natural i, ← Category.assoc]
      _ = q ≫ X.pathEv₀ := by rw [← Category.assoc, hpost]
      _ = SSet.const a.val := hp₀
      _ = SSet.const a ≫ i := by rw [SSet.const_comp]; rfl
  have hp₁A : qA ≫ (A : SSet).pathEv₁ = SSet.const b := by
    apply (cancel_mono i).mp
    calc
      (qA ≫ (A : SSet).pathEv₁) ≫ i =
          qA ≫ ((ihom Δ[1]).map i) ≫ X.pathEv₁ := by
        rw [Category.assoc, ← pathEv_one_natural i, ← Category.assoc]
      _ = q ≫ X.pathEv₁ := by rw [← Category.assoc, hpost]
      _ = SSet.const b.val := hp₁
      _ = SSet.const b ≫ i := by rw [SSet.const_comp]; rfl
  have hpairA : qA ≫ (A : SSet).pathEv₀₁ = SSet.const (X := (PX : SSet))
      ((a, b) : ((A : SSet) ⊗ (A : SSet) : SSet.{u}) _⦋0⦌) := by
    ext : 1
    · simpa only [Category.assoc, SSet.pathEv₀₁_fst,
        SSet.const_comp] using hp₀A
    · simpa only [Category.assoc, SSet.pathEv₀₁_snd,
        SSet.const_comp] using hp₁A
  let g : (PX : SSet) ⟶ (PA : SSet) :=
    SSet.Subcomplex.lift qA
      ((SSet.Subcomplex.range_le_fiber_iff (A : SSet).pathEv₀₁ ⟨a, b⟩ qA).2 hpairA)
  refine ⟨g, ?_⟩
  calc
    g ≫ PA.ι ≫ ((ihom Δ[1]).map A.ι) =
        qA ≫ ((ihom Δ[1]).map i) := by
      dsimp only [g]
      rw [← Category.assoc, SSet.Subcomplex.lift_ι]
    _ = q := hpost

/-- The exact strict-endpoint path-fiber comparison is an isomorphism of
simplicial sets for arbitrary selected vertices. -/
def strictPathFiberIso {X : SSet.{u}}
    (V : Set (X.obj (op ⦋0⦌)))
    (a b : (fullVertexSubcomplex X V : SSet).obj (op ⦋0⦌)) :
    (strictPathFiber (fullVertexSubcomplex X V : SSet) a b : SSet) ≅
      (strictPathFiber X a.val b.val : SSet) := by
  let A := fullVertexSubcomplex X V
  let PA := strictPathFiber (A : SSet) a b
  let PX := strictPathFiber X a.val b.val
  let i := A.ι
  let forward := strictPathFiberMap i a b
  let back := (strictPathFiberInverseData V a b).val
  have hforward : forward ≫ PX.ι = PA.ι ≫ ((ihom Δ[1]).map i) :=
    SSet.Subcomplex.lift_ι _ _
  have hback : back ≫ PA.ι ≫ ((ihom Δ[1]).map i) = PX.ι :=
    (strictPathFiberInverseData V a b).property
  letI : Mono ((ihom Δ[1]).map i) := path_map_mono i
  refine {
    hom := forward
    inv := back
    hom_inv_id := ?_
    inv_hom_id := ?_
  }
  · apply (cancel_mono PA.ι).mp
    apply (cancel_mono ((ihom Δ[1]).map i)).mp
    calc
      (forward ≫ back) ≫ PA.ι ≫ ((ihom Δ[1]).map i) =
          forward ≫ PX.ι := by rw [Category.assoc, hback]
      _ = PA.ι ≫ ((ihom Δ[1]).map i) := hforward
      _ = (𝟙 (PA : SSet)) ≫ PA.ι ≫ ((ihom Δ[1]).map i) := by simp
  · apply (cancel_mono PX.ι).mp
    calc
      (back ≫ forward) ≫ PX.ι =
          back ≫ PA.ι ≫ ((ihom Δ[1]).map i) := by rw [Category.assoc, hforward]
      _ = PX.ι := hback
      _ = (𝟙 (PX : SSet)) ≫ PX.ι := by simp

end

end DaggerOriginalFullVertexSubcomplex
