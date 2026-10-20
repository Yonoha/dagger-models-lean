import OriginalOrdinaryCoreTriangleLift

/-!
# The actual core inclusion on original homotopy categories

The induced functor is the native hoFunctor applied to the literal original
core inclusion. Actual triangle lifting reflects left homotopies, hence path
class equality. Every isomorphism between the same vertices has a core edge
representative. This preserves the original path quotient and exact endpoints;
it does not assert the still unresolved higher outer-horn filling theorem.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreEdgeMaximality
open DaggerOriginalInnerHornFillers
open DaggerOriginalOrdinaryKanCoreInnerHorns
open DaggerOriginalQuasicategoryPathEdgeRepresentatives
open DaggerOriginalQuasicategoryEdgeHomotopies
open DaggerOriginalQuasicategoryPathTriangleWitnesses
open DaggerOriginalQuasicategoryInverseEdgeRepresentatives
open DaggerOriginalOrdinaryCoreTriangleLift

universe u

namespace DaggerOriginalOrdinaryCoreHomotopyInclusion

noncomputable section

/-- The native homotopy functor applied to the literal original core inclusion. -/
def coreHomotopyInclusion (X : SSet.{u}) :
    SSet.hoFunctor.obj (ordinaryCoreCandidate X : SSet.{u}) ⥤ SSet.hoFunctor.obj X :=
  (SSet.hoFunctor.map (ordinaryCoreCandidate X).ι).toFunctor

/-- Its map on a literal original core edge is the same edge after the actual inclusion. -/
theorem coreHomotopyInclusion_homMk (X : SSet.{u})
    {x y : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋0⦌)} (e : SSet.Edge x y) :
    (coreHomotopyInclusion X).map (SSet.Truncated.HomotopyCategory.homMk e) =
      SSet.Truncated.HomotopyCategory.homMk (e.map (ordinaryCoreCandidate X).ι) := rfl

/-- The actual inclusion reflects left homotopy triangles between the same core edges. -/
theorem core_leftHomotopic_iff (X : SSet.{u})
    {x y : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋0⦌)} {e f : SSet.Edge x y} :
    leftHomotopic (e.map (ordinaryCoreCandidate X).ι) (f.map (ordinaryCoreCandidate X).ι) ↔
      leftHomotopic e f := by
  constructor
  · rintro ⟨t⟩
    have v : (e.map (ordinaryCoreCandidate X).ι).CompStruct
        ((SSet.Edge.id y).map (ordinaryCoreCandidate X).ι)
        (f.map (ordinaryCoreCandidate X).ι) := by
      rw [SSet.Edge.map_id]
      exact t
    exact ⟨liftCoreTriangle X v⟩
  · rintro ⟨t⟩
    have v := t.map (ordinaryCoreCandidate X).ι
    rw [SSet.Edge.map_id] at v
    exact ⟨v⟩

/-- Equality of exact original core edge classes is reflected by the actual inclusion. -/
theorem core_homMk_eq_of_inclusion (X : SSet.{u}) (hX : innerHornFillers X)
    {x y : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋0⦌)} {e f : SSet.Edge x y}
    (h : SSet.Truncated.HomotopyCategory.homMk (e.map (ordinaryCoreCandidate X).ι) =
      SSet.Truncated.HomotopyCategory.homMk (f.map (ordinaryCoreCandidate X).ι)) :
    SSet.Truncated.HomotopyCategory.homMk e = SSet.Truncated.HomotopyCategory.homMk f := by
  apply (original_homMk_eq_iff_leftHomotopic
    (innerHornFillers_ordinaryCoreCandidate X hX)).mpr
  exact (core_leftHomotopic_iff X).mp ((original_homMk_eq_iff_leftHomotopic hX).mp h)

/-- The same original core inclusion induces a faithful functor on the native path quotients. -/
theorem coreHomotopyInclusion_faithful (X : SSet.{u}) (hX : innerHornFillers X) :
    (coreHomotopyInclusion X).Faithful where
  map_injective {x y} f g h := by
    obtain ⟨a, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective x
    obtain ⟨b, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective y
    obtain ⟨e, rfl⟩ := original_homMk_surjective (ordinaryCoreCandidate X : SSet.{u})
      (innerHornFillers_ordinaryCoreCandidate X hX) f
    obtain ⟨k, rfl⟩ := original_homMk_surjective (ordinaryCoreCandidate X : SSet.{u})
      (innerHornFillers_ordinaryCoreCandidate X hX) g
    rw [coreHomotopyInclusion_homMk, coreHomotopyInclusion_homMk] at h
    exact core_homMk_eq_of_inclusion X hX h

/-- Every ambient original isomorphism with the same endpoints has an actual core edge preimage. -/
theorem core_edge_preimage_of_isIso (X : SSet.{u}) (hX : innerHornFillers X)
    {x y : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋0⦌)}
    (f : SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) x.val ⟶
      SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) y.val) [IsIso f] :
    ∃ e : SSet.Edge x y,
      (coreHomotopyInclusion X).map (SSet.Truncated.HomotopyCategory.homMk e) = f := by
  obtain ⟨e, he⟩ := original_homMk_surjective X hX f
  have hi : IsIso (SSet.Truncated.HomotopyCategory.homMk e) := by
    rw [he]
    infer_instance
  have hm : e.edge ∈ (ordinaryCoreCandidate X).obj (op ⦋1⦌) :=
    (mem_ordinaryCoreCandidate_one_iff X e.edge).mpr
      ((edgeIsInvertible_iff_original_homMk_isIso X e).mpr hi)
  let k : SSet.Edge x y := SSet.Edge.mk ⟨e.edge, hm⟩
    (by apply Subtype.ext; exact e.src_eq) (by apply Subtype.ext; exact e.tgt_eq)
  have hk : k.map (ordinaryCoreCandidate X).ι = e := SSet.Edge.ext rfl
  refine ⟨k, ?_⟩
  rw [coreHomotopyInclusion_homMk, hk]
  exact he

end

end DaggerOriginalOrdinaryCoreHomotopyInclusion
