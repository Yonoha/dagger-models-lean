import OriginalProductCutPresentation
import OriginalFlagSupportFlank
import OriginalFlagNormalizationJointImages

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} {d : ℕ}

/-- Every flag contains the actual necklace joints, without a flank condition. -/
theorem necklaceJointImage_subset_support (P : NecklacesOver X a b) (F : Flag.{u} P.code d) :
    necklaceJointImage P ⊆
      flagVertexSupport (Quot.mk _ (⟨P, F⟩ : RawFlag X a b (op ⦋d⦌))) := by
  rintro v ⟨k, hk, rfl⟩
  exact ⟨ULift.up k, F.joints _ hk, rfl⟩

/-- Existing normalization and flankification preserve the whole original class and support. -/
theorem exists_monic_flanked_support_of_normalization
    (hm : ∀ P : NecklacesOver X a b, Mono (normOver P).map)
    (x : (flagHom X a b).obj (op ⦋d⦌)) :
    ∃ (P : NecklacesOver X a b) (F : Flag.{u} P.code d),
      Mono P.map ∧ Flanked F ∧ Quot.mk _ (⟨P, F⟩ : RawFlag X a b (op ⦋d⦌)) = x ∧
        flagVertexSupport x = necklaceJointImage P := by
  obtain ⟨P, F, hF, hx, _⟩ := exists_flanked_support x
  let Q := normOver P
  let G := originalNormalizedFlag P F
  have hG : Flanked G := originalNormalizedFlag_flanked P F hF
  have hclass : Quot.mk (flagRelation X a b (op ⦋d⦌)) (⟨P, F⟩ : RawFlag X a b (op ⦋d⦌)) =
      Quot.mk (flagRelation X a b (op ⦋d⦌)) (⟨Q, G⟩ : RawFlag X a b (op ⦋d⦌)) :=
    Quot.sound ⟨originalNormalization P, rfl⟩
  have hx' : Quot.mk _ (⟨Q, G⟩ : RawFlag X a b (op ⦋d⦌)) = x := hclass.symm.trans hx
  exact ⟨Q, G, hm P, hG, hx',
    (congrArg flagVertexSupport hx').symm.trans (flagVertexSupport_flanked Q G hG)⟩

/-- Full gate-image characterization by actual monomorphic flanked necklaces. -/
theorem gate_support_iff_monic_flanked_of_normalization
    (hm : ∀ P : NecklacesOver X a b, Mono (normOver P).map)
    (S : Set (X.obj (op ⦋0⦌))) (x : (flagHom X a b).obj (op ⦋d⦌)) :
    S ⊆ flagVertexSupport x ↔
      ∃ (P : NecklacesOver X a b) (F : Flag.{u} P.code d),
        Mono P.map ∧ Flanked F ∧ Quot.mk _ (⟨P, F⟩ : RawFlag X a b (op ⦋d⦌)) = x ∧
          S ⊆ necklaceJointImage P := by
  constructor
  · intro hS
    obtain ⟨P, F, hP, hF, hx, hs⟩ := exists_monic_flanked_support_of_normalization hm x
    exact ⟨P, F, hP, hF, hx, hs ▸ hS⟩
  · rintro ⟨P, F, _, hF, hx, hS⟩
    rw [← hx, flagVertexSupport_flanked P F hF]
    exact hS

/-- The same original Hom class has an injective representative over every finite product. -/
theorem product_exists_monic_flanked_support (n : ℕ) (factor : Fin n → NecklaceCode)
    {a b : (productSpace.{u} n factor).obj (op ⦋0⦌)}
    (x : (flagHom (productSpace n factor) a b).obj (op ⦋d⦌)) :
    ∃ (P : NecklacesOver (productSpace n factor) a b) (F : Flag.{u} P.code d),
      Mono P.map ∧ Flanked F ∧ Quot.mk _
        (⟨P, F⟩ : RawFlag (productSpace n factor) a b (op ⦋d⦌)) = x ∧
          flagVertexSupport x = necklaceJointImage P :=
  exists_monic_flanked_support_of_normalization normOver_product_mono x

/-- The original binary product gate subcomplex has exactly the monic-flanked representative image.
The ordered-target monomorphism is proved, not an extra input to this characterization. -/
theorem productCut_gate_support_iff_monic_flanked (n : ℕ) (factor : Fin n → NecklaceCode)
    (T : NecklaceCode) {a b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌)}
    (S : Set ((productSpace n factor ⨯ T.toSSet).obj (op ⦋0⦌)))
    (x : (flagHom (productSpace n factor ⨯ T.toSSet) a b).obj (op ⦋d⦌)) :
    x ∈ (flagGateSubcomplex a b S).obj (op ⦋d⦌) ↔
      ∃ (P : NecklacesOver (productSpace n factor ⨯ T.toSSet) a b) (F : Flag.{u} P.code d),
        Mono P.map ∧ Flanked F ∧ Quot.mk _
          (⟨P, F⟩ : RawFlag (productSpace n factor ⨯ T.toSSet) a b (op ⦋d⦌)) = x ∧
            S ⊆ necklaceJointImage P :=
  gate_support_iff_monic_flanked_of_normalization (normOver_productCut_mono n factor T) S x

/-- Exact image characterization for all flags on the paper's monomorphic gate necklaces. -/
theorem productCut_gate_support_iff_monic (n : ℕ) (factor : Fin n → NecklaceCode)
    (T : NecklaceCode) {a b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌)}
    (S : Set ((productSpace n factor ⨯ T.toSSet).obj (op ⦋0⦌)))
    (x : (flagHom (productSpace n factor ⨯ T.toSSet) a b).obj (op ⦋d⦌)) :
    x ∈ (flagGateSubcomplex a b S).obj (op ⦋d⦌) ↔
      ∃ (P : NecklacesOver (productSpace n factor ⨯ T.toSSet) a b) (F : Flag.{u} P.code d),
        Mono P.map ∧ Quot.mk _
          (⟨P, F⟩ : RawFlag (productSpace n factor ⨯ T.toSSet) a b (op ⦋d⦌)) = x ∧
            S ⊆ necklaceJointImage P := by
  constructor
  · intro h
    obtain ⟨P, F, hP, _, hx, hS⟩ :=
      (productCut_gate_support_iff_monic_flanked n factor T S x).mp h
    exact ⟨P, F, hP, hx, hS⟩
  · rintro ⟨P, F, _, hx, hS⟩
    change S ⊆ flagVertexSupport x
    rw [← hx]
    exact hS.trans (necklaceJointImage_subset_support P F)

end

end DaggerOriginalProductGadget
