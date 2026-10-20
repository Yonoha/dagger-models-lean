import OriginalCounitRightConeCrossTimeProjectionMapsReconciled
import OriginalRigidificationConstantArrowIdentityReconciled
import OriginalChosenHomMapEnrichedLawsReconciled
import OriginalChosenHomMapFunctorialityReconciled

/-!
# Strict right-inverse equations for both actual cross-time sections

Every equation below is an equality of whole simplicial-set maps. The
vertical identity comes from the actual zero-simplex Hom, and the final
step uses the original enriched-unit laws.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial EnrichedCategory MonoidalCategory
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerModels.OrdinaryRigidification.DirectedIntervalHom
open DaggerOriginalRigidificationDirectedProductProjection
open DaggerOriginalCounitRightConeCrossTimeSections
open DaggerOriginalCounitRightConeCrossTimeProjectionMaps
open DaggerOriginalRigidificationConstantArrowIdentity
open DaggerOriginalChosenHomMapFunctoriality
open DaggerOriginalChosenHomMapEnrichedLaws

universe u

namespace DaggerOriginalCounitRightConeCrossTimeSectionLaws

noncomputable section

private abbrev I : SSet.{u} := Δ[1]

/-- Placing a horizontal arrow and projecting recovers that whole arrow. -/
theorem horizontal_projection (X : SSet.{u})
    (a b : X.obj (op ⦋0⦌)) (i : I.{u}.obj (op ⦋0⦌)) :
    horizontal X a b i ≫
      originalChosenHomMap (fst X I.{u}) (a, i) (b, i) =
        𝟙 (firstHom X a b) := by
  have comp_transport (c d : (X ⊗ I.{u}).obj (op ⦋0⦌))
      (hc : (horizontalAt X i).app (op ⦋0⦌) a = c)
      (hd : (horizontalAt X i).app (op ⦋0⦌) b = d)
      (hgc : (fst X I.{u}).app (op ⦋0⦌) c = a)
      (hgd : (fst X I.{u}).app (op ⦋0⦌) d = b)
      (hfc : (horizontalAt X i ≫ fst X I.{u}).app (op ⦋0⦌) a = a)
      (hfd : (horizontalAt X i ≫ fst X I.{u}).app (op ⦋0⦌) b = b) :
      (originalChosenHomMap (horizontalAt X i) a b ≫
          targetHomTransport (congrArg (RV (X ⊗ I.{u})) hc)
            (congrArg (RV (X ⊗ I.{u})) hd)) ≫
        (originalChosenHomMap (fst X I.{u}) c d ≫
          targetHomTransport (congrArg (RV X) hgc) (congrArg (RV X) hgd)) =
      originalChosenHomMap (horizontalAt X i ≫ fst X I.{u}) a b ≫
        targetHomTransport (congrArg (RV X) hfc) (congrArg (RV X) hfd) := by
    cases hc
    cases hd
    rw [originalChosenHomMap_comp]
    simp only [SSet.comp_app, types_comp_apply, targetHomTransport, eqToHom_refl,
      Category.comp_id]
  have hfc : (horizontalAt X i ≫ fst X I.{u}).app (op ⦋0⦌) a = a := by
    rw [horizontalAt_fst]
    rfl
  have hfd : (horizontalAt X i ≫ fst X I.{u}).app (op ⦋0⦌) b = b := by
    rw [horizontalAt_fst]
    rfl
  calc
    horizontal X a b i ≫ originalChosenHomMap (fst X I.{u}) (a, i) (b, i) =
        originalChosenHomMap (horizontalAt X i ≫ fst X I.{u}) a b ≫
          targetHomTransport (congrArg (RV X) hfc) (congrArg (RV X) hfd) := by
      unfold horizontal
      simpa only [targetHomTransport, eqToHom_refl, Category.comp_id] using
        comp_transport (a, i) (b, i) (horizontalAt_vertex X a i)
          (horizontalAt_vertex X b i) rfl rfl hfc hfd
    _ = 𝟙 (firstHom X a b) := by
      have map_congr (f g : X ⟶ X) (hfg : f = g)
          (hf0 : f.app (op ⦋0⦌) a = a) (hf1 : f.app (op ⦋0⦌) b = b)
          (hg0 : g.app (op ⦋0⦌) a = a) (hg1 : g.app (op ⦋0⦌) b = b) :
          originalChosenHomMap f a b ≫
              targetHomTransport (congrArg (RV X) hf0) (congrArg (RV X) hf1) =
            originalChosenHomMap g a b ≫
              targetHomTransport (congrArg (RV X) hg0) (congrArg (RV X) hg1) := by
        cases hfg
        rfl
      rw [map_congr _ (𝟙 X) (horizontalAt_fst X i) hfc hfd rfl rfl,
        originalChosenHomMap_id]
      simp only [targetHomTransport, eqToHom_refl, Category.comp_id]

/-- Placing the directed vertical arrow and projecting gives enriched identity. -/
theorem vertical_projection (X : SSet.{u}) (a : X.obj (op ⦋0⦌)) :
    vertical X a ≫ projection X a a = eId SSet (RV X a) := by
  have comp_transport (c d : (X ⊗ I.{u}).obj (op ⦋0⦌))
      (hc : (verticalAt X a).app (op ⦋0⦌) vertexZero.{u} = c)
      (hd : (verticalAt X a).app (op ⦋0⦌) vertexOne.{u} = d)
      (hgc : (fst X I.{u}).app (op ⦋0⦌) c = a)
      (hgd : (fst X I.{u}).app (op ⦋0⦌) d = a)
      (hfc : (verticalAt X a ≫ fst X I.{u}).app (op ⦋0⦌) vertexZero.{u} = a)
      (hfd : (verticalAt X a ≫ fst X I.{u}).app (op ⦋0⦌) vertexOne.{u} = a) :
      (originalChosenHomMap (verticalAt X a) vertexZero.{u} vertexOne.{u} ≫
          targetHomTransport (congrArg (RV (X ⊗ I.{u})) hc)
            (congrArg (RV (X ⊗ I.{u})) hd)) ≫
        (originalChosenHomMap (fst X I.{u}) c d ≫
          targetHomTransport (congrArg (RV X) hgc) (congrArg (RV X) hgd)) =
      originalChosenHomMap (verticalAt X a ≫ fst X I.{u})
          vertexZero.{u} vertexOne.{u} ≫
        targetHomTransport (congrArg (RV X) hfc) (congrArg (RV X) hfd) := by
    cases hc
    cases hd
    rw [originalChosenHomMap_comp]
    simp only [SSet.comp_app, types_comp_apply, targetHomTransport, eqToHom_refl,
      Category.comp_id, Category.assoc]
  have hfc : (verticalAt X a ≫ fst X I.{u}).app (op ⦋0⦌) vertexZero.{u} = a := by
    rw [verticalAt_fst]
    exact const_zero X a
  have hfd : (verticalAt X a ≫ fst X I.{u}).app (op ⦋0⦌) vertexOne.{u} = a := by
    rw [verticalAt_fst]
    exact const_one X a
  have hmap :
      originalChosenHomMap (verticalAt X a ≫ fst X I.{u})
          vertexZero.{u} vertexOne.{u} ≫
        targetHomTransport (congrArg (RV X) hfc) (congrArg (RV X) hfd) =
      constantHom X a := by
    have map_congr (f g : I.{u} ⟶ X) (hfg : f = g)
        (hf0 : f.app (op ⦋0⦌) vertexZero.{u} = a)
        (hf1 : f.app (op ⦋0⦌) vertexOne.{u} = a)
        (hg0 : g.app (op ⦋0⦌) vertexZero.{u} = a)
        (hg1 : g.app (op ⦋0⦌) vertexOne.{u} = a) :
        originalChosenHomMap f vertexZero.{u} vertexOne.{u} ≫
          targetHomTransport (congrArg (RV X) hf0) (congrArg (RV X) hf1) =
        originalChosenHomMap g vertexZero.{u} vertexOne.{u} ≫
          targetHomTransport (congrArg (RV X) hg0) (congrArg (RV X) hg1) := by
      cases hfg
      rfl
    unfold constantHom
    exact map_congr _ _ (verticalAt_fst X a) hfc hfd
      (const_zero X a) (const_one X a)
  calc
    vertical X a ≫ projection X a a =
        directedArrow.{u} ≫
          (originalChosenHomMap (verticalAt X a ≫ fst X I.{u})
              vertexZero.{u} vertexOne.{u} ≫
            targetHomTransport (congrArg (RV X) hfc) (congrArg (RV X) hfd)) := by
      unfold vertical projection
      simp only [Category.assoc]
      simpa only [targetHomTransport, eqToHom_refl, Category.comp_id,
        Category.assoc] using congrArg (fun t ↦ directedArrow.{u} ≫ t)
          (comp_transport (a, vertexZero.{u}) (a, vertexOne.{u})
            (verticalAt_vertex X a vertexZero.{u})
            (verticalAt_vertex X a vertexOne.{u}) rfl rfl hfc hfd)
    _ = eId SSet (RV X a) := by
      rw [hmap]
      exact directed_constant_identity X a

/-- Horizontal-zero then vertical-target is a strict section of projection. -/
theorem sectionZero_projection (X : SSet.{u})
    (a b : X.obj (op ⦋0⦌)) :
    sectionZero X a b ≫ projection X a b = 𝟙 (firstHom X a b) := by
  unfold sectionZero projection
  simp only [Category.assoc]
  rw [map_eComp (fst X I.{u}) (a, vertexZero.{u})
    (b, vertexZero.{u}) (b, vertexOne.{u})]
  rw [← Category.assoc (_ ⊗ₘ _) (_ ⊗ₘ _) _]
  rw [tensorHom_comp_tensorHom]
  have hv : vertical X b ≫
      originalChosenHomMap (fst X I.{u}) (b, vertexZero.{u}) (b, vertexOne.{u}) =
        eId SSet (RV X b) := vertical_projection X b
  rw [horizontal_projection X a b vertexZero.{u}, hv]
  exact e_comp_id SSet (RV X a) (RV X b)

/-- Vertical-source then horizontal-one is a strict section of projection. -/
theorem sectionOne_projection (X : SSet.{u})
    (a b : X.obj (op ⦋0⦌)) :
    sectionOne X a b ≫ projection X a b = 𝟙 (firstHom X a b) := by
  unfold sectionOne projection
  simp only [Category.assoc]
  rw [map_eComp (fst X I.{u}) (a, vertexZero.{u})
    (a, vertexOne.{u}) (b, vertexOne.{u})]
  rw [← Category.assoc (_ ⊗ₘ _) (_ ⊗ₘ _) _]
  rw [tensorHom_comp_tensorHom]
  have hv : vertical X a ≫
      originalChosenHomMap (fst X I.{u}) (a, vertexZero.{u}) (a, vertexOne.{u}) =
        eId SSet (RV X a) := vertical_projection X a
  rw [hv, horizontal_projection X a b vertexOne.{u}]
  exact e_id_comp SSet (RV X a) (RV X b)

/-- The first literal cone cross-time section is a strict right inverse. -/
theorem s0_projection (n : ℕ) :
    s0.{u} n ≫ coneProjection.{u} n =
      𝟙 (DaggerOriginalCounitRightCone.Q.{u} n) :=
  sectionZero_projection
    (DaggerOriginalCounitRightCone.cone.{u} n)
    (DaggerOriginalCounitRightCone.alpha.{u} n)
    (DaggerOriginalCounitRightCone.omega.{u} n)

/-- The second literal cone cross-time section is a strict right inverse. -/
theorem s1_projection (n : ℕ) :
    s1.{u} n ≫ coneProjection.{u} n =
      𝟙 (DaggerOriginalCounitRightCone.Q.{u} n) :=
  sectionOne_projection
    (DaggerOriginalCounitRightCone.cone.{u} n)
    (DaggerOriginalCounitRightCone.alpha.{u} n)
    (DaggerOriginalCounitRightCone.omega.{u} n)

end

end DaggerOriginalCounitRightConeCrossTimeSectionLaws
