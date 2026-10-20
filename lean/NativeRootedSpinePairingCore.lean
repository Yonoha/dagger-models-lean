import NativeRootedSpineProperness

/-! A full native PairingCore collapses the generator spine to its actual root vertex. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerNativeGeneratorSpineSimplices DaggerNativeRootedQuiverPairingData
open DaggerNativeRootedSpineCells DaggerNativeSpineRootSubcomplex
open DaggerNativeRootedSpineProperness
universe u
namespace DaggerNativeRootedSpinePairingCore
noncomputable section

variable {W : Type u} [Quiver.{u + 1} W] (D : Data W)

def pairingCore : (rootComplex D.root).PairingCore where
  ι := D.Cell
  d _ := 0
  type₁ := upper D
  index := index D
  nonDegenerate₁ := upper_nonDegenerate D
  nonDegenerate₂ x := by
    rw [delta_upper]
    exact vertex_nonDegenerate W x.val
  notMem₁ := upper_notMem_root D
  notMem₂ x := by
    rw [delta_upper]
    exact vertex_notMem_root D x
  injective_type₁ he := upper_injective D ((SSet.S.ext_iff _ _).mp he)
  injective_type₂ he := by
    rw [delta_upper, delta_upper] at he
    exact Subtype.ext (vertex_injective W ((SSet.S.ext_iff _ _).mp he))
  type₁_neq_type₂ x y he := by
    have hd := SSet.S.dim_eq_of_mk_eq he
    change 1 = 0 at hd
    omega
  surjective' x := by
    obtain ⟨n, s, hs, hn, rfl⟩ := x.mk_surjective
    have hd := nonDegenerate_dimension_le_one W s hs
    cases n with
    | zero =>
      obtain ⟨v, hv⟩ := vertex_surjective W s
      subst s
      have hv : v ≠ D.root := by
        intro he
        exact hn ((vertex_mem_root_iff D.root v).mpr he)
      let c : D.Cell := ⟨v, hv⟩
      refine ⟨c, Or.inr ?_⟩
      change SSet.S.mk (X := spine W) (vertex W v) =
        SSet.S.mk ((spine W).δ (index D c) (upper D c))
      rw [delta_upper]
    | succ n =>
      cases n with
      | zero =>
        obtain ⟨u, v, e, he⟩ := edge_surjective W s hs
        obtain ⟨c, hc⟩ := edge_covered D e
        refine ⟨c, Or.inl ?_⟩
        change SSet.S.mk (X := spine W) s = SSet.S.mk (upper D c)
        exact congrArg (SSet.S.mk (X := spine W)) (he.trans hc.symm)
      | succ n => omega

instance pairingCoreProper : (pairingCore D).IsProper where
  isUniquelyCodimOneFace x := by
    change SSet.IsUniquelyCodimOneFace (X := spine W)
      ((spine W).δ (index D x) (upper D x)) (upper D x)
    rw [delta_upper]
    exact unique_vertex_face D x

instance pairingCoreRegular : (pairingCore D).IsRegular := by
  rw [SSet.Subcomplex.PairingCore.isRegular_iff]
  refine ⟨fun x ↦ D.height x.val, fun x y _ h ↦ ?_⟩
  apply face_height_lt D h.1
  have hf := h.2
  change SSet.IsFace (X := spine W)
    ((spine W).δ (index D x) (upper D x)) (upper D y) at hf
  rw [delta_upper] at hf
  exact hf

theorem root_inclusion_anodyne : SSet.anodyneExtensions (rootComplex D.root).ι :=
  (pairingCore D).pairing.anodyneExtensions

end
end DaggerNativeRootedSpinePairingCore
