import OriginalCounitRightConeRelativeLineMapsReconciled
import OriginalCounitRightConeCrossTimeSectionLawsReconciled
import OriginalCounitRightConeRelativeHomMapReconciled
import OriginalChosenHomMapEnrichedLawsReconciled
import OriginalChosenHomMapFunctorialityReconciled

/-!
# Endpoint laws for the original relative-cone Hom map

The time-zero cross-time section is a strict right inverse of the actual
relative-homotopy Hom map. The time-one retraction is retained with both
original endpoint casts, without a weak-equivalence assertion.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial EnrichedCategory MonoidalCategory
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeContractibilityRetraction
open DaggerOriginalCounitRightConeRelativeHomotopy
open DaggerOriginalCounitRightConeRelativeHomMap
open DaggerOriginalCounitRightConeRelativeLineMaps
open DaggerOriginalCounitRightConeCrossTimeSections
open DaggerOriginalRigidificationDirectedProductProjection
open DaggerOriginalRigidificationConstantArrowIdentity
open DaggerOriginalChosenHomMapFunctoriality
open DaggerOriginalChosenHomMapEnrichedLaws
open DaggerModels.OrdinaryRigidification.DirectedIntervalHom

universe u

namespace DaggerOriginalCounitRightConeRelativeHomMapEndpointLaws

noncomputable section

private abbrev I : SSet.{u} := Δ[1]

private theorem map_comp_fixed {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (a b : A.obj (op ⦋0⦌)) (c d : B.obj (op ⦋0⦌)) (e h : C.obj (op ⦋0⦌))
    (hfc : f.app (op ⦋0⦌) a = c) (hfd : f.app (op ⦋0⦌) b = d)
    (hgc : g.app (op ⦋0⦌) c = e) (hgd : g.app (op ⦋0⦌) d = h)
    (hfgc : (f ≫ g).app (op ⦋0⦌) a = e)
    (hfgd : (f ≫ g).app (op ⦋0⦌) b = h) :
    (originalChosenHomMap f a b ≫
        targetHomTransport (congrArg (RV B) hfc) (congrArg (RV B) hfd)) ≫
      (originalChosenHomMap g c d ≫
        targetHomTransport (congrArg (RV C) hgc) (congrArg (RV C) hgd)) =
    originalChosenHomMap (f ≫ g) a b ≫
      targetHomTransport (congrArg (RV C) hfgc) (congrArg (RV C) hfgd) := by
  cases hfc
  cases hfd
  rw [originalChosenHomMap_comp]
  simp only [SSet.comp_app, types_comp_apply, targetHomTransport, eqToHom_refl,
    Category.comp_id, Category.assoc]

private theorem map_congr_fixed {A B : SSet.{u}} (f g : A ⟶ B) (hfg : f = g)
    (a b : A.obj (op ⦋0⦌)) (c d : B.obj (op ⦋0⦌))
    (hfc : f.app (op ⦋0⦌) a = c) (hfd : f.app (op ⦋0⦌) b = d)
    (hgc : g.app (op ⦋0⦌) a = c) (hgd : g.app (op ⦋0⦌) b = d) :
    originalChosenHomMap f a b ≫
        targetHomTransport (congrArg (RV B) hfc) (congrArg (RV B) hfd) =
      originalChosenHomMap g a b ≫
        targetHomTransport (congrArg (RV B) hgc) (congrArg (RV B) hgd) := by
  cases hfg
  rfl

private theorem map_eComp_fixed {A B : SSet.{u}} (f : A ⟶ B)
    (a b c : A.obj (op ⦋0⦌)) (a' b' c' : B.obj (op ⦋0⦌))
    (ha : f.app (op ⦋0⦌) a = a') (hb : f.app (op ⦋0⦌) b = b')
    (hc : f.app (op ⦋0⦌) c = c') :
    eComp SSet (RV A a) (RV A b) (RV A c) ≫
        (originalChosenHomMap f a c ≫
          targetHomTransport (congrArg (RV B) ha) (congrArg (RV B) hc)) =
      ((originalChosenHomMap f a b ≫
          targetHomTransport (congrArg (RV B) ha) (congrArg (RV B) hb)) ⊗ₘ
        (originalChosenHomMap f b c ≫
          targetHomTransport (congrArg (RV B) hb) (congrArg (RV B) hc))) ≫
        eComp SSet (RV B a') (RV B b') (RV B c') := by
  cases ha
  cases hb
  cases hc
  simpa only [targetHomTransport, eqToHom_refl, Category.comp_id] using
    (map_eComp f a b c)

private theorem horizontal_zero_homH (n : ℕ) :
    horizontal (cone.{u} n) (alpha.{u} n) (omega.{u} n) vertexZero.{u} ≫
      (originalChosenHomMap (relativeHomotopy.{u} n)
          (alpha.{u} n, vertexZero.{u}) (omega.{u} n, vertexZero.{u}) ≫
        targetHomTransport
          (congrArg (RV (cone.{u} n)) (alpha_fixed_vertex.{u} n vertexZero.{u}))
          (congrArg (RV (cone.{u} n)) (omega_fixed_vertex.{u} n vertexZero.{u}))) =
      𝟙 (Q.{u} n) := by
  let X : SSet.{u} := cone.{u} n
  let a := alpha.{u} n
  let b := omega.{u} n
  have hfa : (horizontalAt X vertexZero.{u} ≫ relativeHomotopy.{u} n).app
      (op ⦋0⦌) a = a := by
    rw [horizontal_relative_zero]
    rfl
  have hfb : (horizontalAt X vertexZero.{u} ≫ relativeHomotopy.{u} n).app
      (op ⦋0⦌) b = b := by
    rw [horizontal_relative_zero]
    rfl
  calc
    _ = originalChosenHomMap
          (horizontalAt X vertexZero.{u} ≫ relativeHomotopy.{u} n) a b ≫
          targetHomTransport (congrArg (RV X) hfa) (congrArg (RV X) hfb) := by
      unfold horizontal
      exact map_comp_fixed (horizontalAt X vertexZero.{u}) (relativeHomotopy.{u} n)
        a b (a, vertexZero.{u}) (b, vertexZero.{u}) a b
        (horizontalAt_vertex X a vertexZero.{u})
        (horizontalAt_vertex X b vertexZero.{u})
        (alpha_fixed_vertex.{u} n vertexZero.{u})
        (omega_fixed_vertex.{u} n vertexZero.{u}) hfa hfb
    _ = originalChosenHomMap (𝟙 X) a b ≫
          targetHomTransport
            (congrArg (RV X) (rfl : (𝟙 X : X ⟶ X).app (op ⦋0⦌) a = a))
            (congrArg (RV X) (rfl : (𝟙 X : X ⟶ X).app (op ⦋0⦌) b = b)) := by
      exact map_congr_fixed _ _ (horizontal_relative_zero.{u} n) a b a b
        hfa hfb rfl rfl
    _ = 𝟙 (Q.{u} n) := by
      rw [originalChosenHomMap_id]
      simp only [targetHomTransport, eqToHom_refl, Category.comp_id]
      rfl

private theorem vertical_omega_homH (n : ℕ) :
    vertical (cone.{u} n) (omega.{u} n) ≫
      (originalChosenHomMap (relativeHomotopy.{u} n)
          (omega.{u} n, vertexZero.{u}) (omega.{u} n, vertexOne.{u}) ≫
        targetHomTransport
          (congrArg (RV (cone.{u} n)) (omega_fixed_vertex.{u} n vertexZero.{u}))
          (congrArg (RV (cone.{u} n)) (omega_fixed_vertex.{u} n vertexOne.{u}))) =
      eId SSet (RV (cone.{u} n) (omega.{u} n)) := by
  let X : SSet.{u} := cone.{u} n
  let b := omega.{u} n
  have hfa : (verticalAt X b ≫ relativeHomotopy.{u} n).app
      (op ⦋0⦌) vertexZero.{u} = b := by
    rw [vertical_relative_omega]
    exact const_zero X b
  have hfb : (verticalAt X b ≫ relativeHomotopy.{u} n).app
      (op ⦋0⦌) vertexOne.{u} = b := by
    rw [vertical_relative_omega]
    exact const_one X b
  have hcomp := map_comp_fixed (verticalAt X b) (relativeHomotopy.{u} n)
    vertexZero.{u} vertexOne.{u} (b, vertexZero.{u}) (b, vertexOne.{u}) b b
    (verticalAt_vertex X b vertexZero.{u})
    (verticalAt_vertex X b vertexOne.{u})
    (omega_fixed_vertex.{u} n vertexZero.{u})
    (omega_fixed_vertex.{u} n vertexOne.{u}) hfa hfb
  have hconst :
      originalChosenHomMap (verticalAt X b ≫ relativeHomotopy.{u} n)
          vertexZero.{u} vertexOne.{u} ≫
        targetHomTransport (congrArg (RV X) hfa) (congrArg (RV X) hfb) =
      constantHom X b := by
    unfold constantHom
    exact map_congr_fixed _ _ (vertical_relative_omega.{u} n)
      vertexZero.{u} vertexOne.{u} b b hfa hfb (const_zero X b) (const_one X b)
  calc
    _ = directedArrow.{u} ≫
          (originalChosenHomMap (verticalAt X b ≫ relativeHomotopy.{u} n)
              vertexZero.{u} vertexOne.{u} ≫
            targetHomTransport (congrArg (RV X) hfa) (congrArg (RV X) hfb)) := by
      unfold vertical
      simpa only [Category.assoc] using congrArg (fun t ↦ directedArrow.{u} ≫ t) hcomp
    _ = directedArrow.{u} ≫ constantHom X b := by rw [hconst]
    _ = eId SSet (RV X b) := directed_constant_identity X b

private theorem retraction_alpha (n : ℕ) :
    (projection.{u} n ≫ lastEdge.{u} n).app (op ⦋0⦌) (alpha.{u} n) =
      alpha.{u} n := by
  rw [← horizontal_relative_one]
  simp only [SSet.comp_app, types_comp_apply, horizontalAt_vertex, alpha_fixed_vertex]

private theorem retraction_omega (n : ℕ) :
    (projection.{u} n ≫ lastEdge.{u} n).app (op ⦋0⦌) (omega.{u} n) =
      omega.{u} n := by
  rw [← horizontal_relative_one]
  simp only [SSet.comp_app, types_comp_apply, horizontalAt_vertex, omega_fixed_vertex]

/-- The actual cone edge retraction on the original Q Hom, with both casts. -/
def retractionHom (n : ℕ) : Q.{u} n ⟶ Q.{u} n :=
  originalChosenHomMap (projection.{u} n ≫ lastEdge.{u} n)
      (alpha.{u} n) (omega.{u} n) ≫
    targetHomTransport
      (congrArg (RV (cone.{u} n)) (retraction_alpha.{u} n))
      (congrArg (RV (cone.{u} n)) (retraction_omega.{u} n))

/-- The first literal cross-time section retracts under the actual Hom homotopy. -/
theorem s0_homH (n : ℕ) :
    s0.{u} n ≫ homH.{u} n = 𝟙 (Q.{u} n) := by
  let X : SSet.{u} := cone.{u} n
  let a := alpha.{u} n
  let b := omega.{u} n
  change sectionZero X a b ≫ homH.{u} n = 𝟙 (Q.{u} n)
  unfold sectionZero homH
  simp only [Category.assoc]
  rw [map_eComp_fixed (relativeHomotopy.{u} n)
    (a, vertexZero.{u}) (b, vertexZero.{u}) (b, vertexOne.{u}) a b b
    (alpha_fixed_vertex.{u} n vertexZero.{u})
    (omega_fixed_vertex.{u} n vertexZero.{u})
    (omega_fixed_vertex.{u} n vertexOne.{u})]
  rw [← Category.assoc (_ ⊗ₘ _) (_ ⊗ₘ _) _]
  rw [tensorHom_comp_tensorHom]
  rw [horizontal_zero_homH n, vertical_omega_homH n]
  exact e_comp_id SSet (RV X a) (RV X b)

private theorem horizontal_one_homH (n : ℕ) :
    horizontal (cone.{u} n) (alpha.{u} n) (omega.{u} n) vertexOne.{u} ≫
      (originalChosenHomMap (relativeHomotopy.{u} n)
          (alpha.{u} n, vertexOne.{u}) (omega.{u} n, vertexOne.{u}) ≫
        targetHomTransport
          (congrArg (RV (cone.{u} n)) (alpha_fixed_vertex.{u} n vertexOne.{u}))
          (congrArg (RV (cone.{u} n)) (omega_fixed_vertex.{u} n vertexOne.{u}))) =
      retractionHom.{u} n := by
  let X : SSet.{u} := cone.{u} n
  let a := alpha.{u} n
  let b := omega.{u} n
  have hfa : (horizontalAt X vertexOne.{u} ≫ relativeHomotopy.{u} n).app
      (op ⦋0⦌) a = a := by
    rw [horizontal_relative_one]
    exact retraction_alpha.{u} n
  have hfb : (horizontalAt X vertexOne.{u} ≫ relativeHomotopy.{u} n).app
      (op ⦋0⦌) b = b := by
    rw [horizontal_relative_one]
    exact retraction_omega.{u} n
  calc
    _ = originalChosenHomMap
          (horizontalAt X vertexOne.{u} ≫ relativeHomotopy.{u} n) a b ≫
          targetHomTransport (congrArg (RV X) hfa) (congrArg (RV X) hfb) := by
      unfold horizontal
      exact map_comp_fixed (horizontalAt X vertexOne.{u}) (relativeHomotopy.{u} n)
        a b (a, vertexOne.{u}) (b, vertexOne.{u}) a b
        (horizontalAt_vertex X a vertexOne.{u})
        (horizontalAt_vertex X b vertexOne.{u})
        (alpha_fixed_vertex.{u} n vertexOne.{u})
        (omega_fixed_vertex.{u} n vertexOne.{u}) hfa hfb
    _ = retractionHom.{u} n := by
      unfold retractionHom
      exact map_congr_fixed _ _ (horizontal_relative_one.{u} n) a b a b
        hfa hfb (retraction_alpha.{u} n) (retraction_omega.{u} n)

private theorem vertical_alpha_homH (n : ℕ) :
    vertical (cone.{u} n) (alpha.{u} n) ≫
      (originalChosenHomMap (relativeHomotopy.{u} n)
          (alpha.{u} n, vertexZero.{u}) (alpha.{u} n, vertexOne.{u}) ≫
        targetHomTransport
          (congrArg (RV (cone.{u} n)) (alpha_fixed_vertex.{u} n vertexZero.{u}))
          (congrArg (RV (cone.{u} n)) (alpha_fixed_vertex.{u} n vertexOne.{u}))) =
      eId SSet (RV (cone.{u} n) (alpha.{u} n)) := by
  let X : SSet.{u} := cone.{u} n
  let a := alpha.{u} n
  have hfa : (verticalAt X a ≫ relativeHomotopy.{u} n).app
      (op ⦋0⦌) vertexZero.{u} = a := by
    rw [vertical_relative_alpha]
    exact const_zero X a
  have hfb : (verticalAt X a ≫ relativeHomotopy.{u} n).app
      (op ⦋0⦌) vertexOne.{u} = a := by
    rw [vertical_relative_alpha]
    exact const_one X a
  have hcomp := map_comp_fixed (verticalAt X a) (relativeHomotopy.{u} n)
    vertexZero.{u} vertexOne.{u} (a, vertexZero.{u}) (a, vertexOne.{u}) a a
    (verticalAt_vertex X a vertexZero.{u})
    (verticalAt_vertex X a vertexOne.{u})
    (alpha_fixed_vertex.{u} n vertexZero.{u})
    (alpha_fixed_vertex.{u} n vertexOne.{u}) hfa hfb
  have hconst :
      originalChosenHomMap (verticalAt X a ≫ relativeHomotopy.{u} n)
          vertexZero.{u} vertexOne.{u} ≫
        targetHomTransport (congrArg (RV X) hfa) (congrArg (RV X) hfb) =
      constantHom X a := by
    unfold constantHom
    exact map_congr_fixed _ _ (vertical_relative_alpha.{u} n)
      vertexZero.{u} vertexOne.{u} a a hfa hfb (const_zero X a) (const_one X a)
  calc
    _ = directedArrow.{u} ≫
          (originalChosenHomMap (verticalAt X a ≫ relativeHomotopy.{u} n)
              vertexZero.{u} vertexOne.{u} ≫
            targetHomTransport (congrArg (RV X) hfa) (congrArg (RV X) hfb)) := by
      unfold vertical
      simpa only [Category.assoc] using congrArg (fun t ↦ directedArrow.{u} ≫ t) hcomp
    _ = directedArrow.{u} ≫ constantHom X a := by rw [hconst]
    _ = eId SSet (RV X a) := directed_constant_identity X a

/-- The second literal cross-time section becomes the original edge retraction. -/
theorem s1_homH (n : ℕ) :
    s1.{u} n ≫ homH.{u} n = retractionHom.{u} n := by
  let X : SSet.{u} := cone.{u} n
  let a := alpha.{u} n
  let b := omega.{u} n
  change sectionOne X a b ≫ homH.{u} n = retractionHom.{u} n
  unfold sectionOne homH
  simp only [Category.assoc]
  rw [map_eComp_fixed (relativeHomotopy.{u} n)
    (a, vertexZero.{u}) (a, vertexOne.{u}) (b, vertexOne.{u}) a a b
    (alpha_fixed_vertex.{u} n vertexZero.{u})
    (alpha_fixed_vertex.{u} n vertexOne.{u})
    (omega_fixed_vertex.{u} n vertexOne.{u})]
  rw [← Category.assoc (_ ⊗ₘ _) (_ ⊗ₘ _) _]
  rw [tensorHom_comp_tensorHom]
  rw [vertical_alpha_homH n, horizontal_one_homH n]
  have hunit : (λ_ (Q.{u} n)).inv ≫
      (eId SSet (RV X a) ▷ Q.{u} n) ≫
        eComp SSet (RV X a) (RV X a) (RV X b) = 𝟙 (Q.{u} n) :=
    e_id_comp SSet (RV X a) (RV X b)
  have hnat := leftUnitor_inv_naturality (retractionHom.{u} n)
  calc
    (λ_ (Q.{u} n)).inv ≫
        (eId SSet (RV X a) ⊗ₘ retractionHom.{u} n) ≫
          eComp SSet (RV X a) (RV X a) (RV X b) =
      ((λ_ (Q.{u} n)).inv ≫
        (𝟙 (𝟙_ SSet.{u}) ⊗ₘ retractionHom.{u} n)) ≫
          (eId SSet (RV X a) ⊗ₘ 𝟙 (Q.{u} n)) ≫
            eComp SSet (RV X a) (RV X a) (RV X b) := by
        simp only [Category.assoc]
        rw [← Category.assoc (_ ⊗ₘ _) (_ ⊗ₘ _) _]
        rw [tensorHom_comp_tensorHom]
        simp only [Category.id_comp, Category.comp_id]
    _ = (retractionHom.{u} n ≫ (λ_ (Q.{u} n)).inv) ≫
          (eId SSet (RV X a) ⊗ₘ 𝟙 (Q.{u} n)) ≫
            eComp SSet (RV X a) (RV X a) (RV X b) := by
        rw [id_tensorHom, ← hnat]
    _ = retractionHom.{u} n := by
        simp only [tensorHom_id, Category.assoc, hunit, Category.comp_id]

end

end DaggerOriginalCounitRightConeRelativeHomMapEndpointLaws
