import OriginalProductNormalizedMono

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable (n : ℕ) (factor : Fin n → NecklaceCode) (T : NecklaceCode)

/-- Present the literal binary product from the crossing argument as one finite product. -/
def productCutPresentation : productSpace.{u} n factor ⨯ T.toSSet ≅
    productSpace.{u} (n + 1) (Fin.cases T factor) where
  hom := Pi.lift (fun i ↦ Fin.cases
    (prod.snd : productSpace n factor ⨯ T.toSSet ⟶ T.toSSet)
    (fun j ↦ prod.fst ≫ Pi.π (fun i ↦ (factor i).toSSet) j) i)
  inv := prod.lift
    (Pi.lift (fun j ↦ Pi.π
      (fun i : Fin (n + 1) ↦
        (Fin.cases (motive := fun _ ↦ NecklaceCode) T factor i).toSSet) j.succ))
    (Pi.π (fun i : Fin (n + 1) ↦
      (Fin.cases (motive := fun _ ↦ NecklaceCode) T factor i).toSSet) 0)
  hom_inv_id := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, Category.id_comp]
      apply Pi.hom_ext
      intro i
      simp only [Category.assoc, Pi.lift_π, Fin.cases_succ]
    · simp only [Category.assoc, prod.lift_snd, Pi.lift_π, Fin.cases_zero, Category.id_comp]
  inv_hom_id := by
    apply Pi.hom_ext
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [Category.assoc, Pi.lift_π, Fin.cases_zero, prod.lift_snd, Category.id_comp]
    · simp only [Category.assoc, Pi.lift_π, Fin.cases_succ, prod.lift_fst_assoc,
        Category.id_comp]

theorem productCut_necklace_mono_of_nondegenerate
    {a b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌)}
    (P : NecklacesOver (productSpace n factor ⨯ T.toSSet) a b)
    (hP : ∀ c : P.code.Bead,
      beadElement P c ∈ (productSpace n factor ⨯ T.toSSet).nonDegenerate c.length) :
    Mono P.map := by
  let e := productCutPresentation n factor T
  let Q := (NecklacesOver.postcomp e.hom).obj P
  have hQ : ∀ c : Q.code.Bead,
      beadElement Q c ∈ (productSpace (n + 1) (Fin.cases T factor)).nonDegenerate c.length := by
    intro c
    change SSet.yonedaEquiv (P.code.beadSimplex c ≫ P.map ≫ e.hom) ∈ _
    rw [← Category.assoc, SSet.yonedaEquiv_comp]
    exact (SSet.nonDegenerate_iff_of_isIso e.hom (beadElement P c)).2 (hP c)
  have hm : Mono (P.map ≫ e.hom) := product_necklace_mono_of_nondegenerate Q hQ
  exact mono_of_mono P.map e.hom

/-- Normalization is monomorphic for the exact binary target of the gate diagram. -/
theorem normOver_productCut_mono
    {a b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌)}
    (P : NecklacesOver (productSpace n factor ⨯ T.toSSet) a b) :
    Mono (normOver P).map :=
  productCut_necklace_mono_of_nondegenerate n factor T
    (normOver P) (normOver_beads_nondegenerate P)

end

end DaggerOriginalProductGadget
