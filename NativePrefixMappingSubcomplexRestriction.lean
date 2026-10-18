import ActualQuasicategoryMappingFibres

/-! Exact restriction of native prefix mapping fibres to any original subcomplex. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalSimplexCoslice DaggerOriginalOrdinalJoinLeft
open DaggerActualQuasicategoryMappingFibres
universe u
namespace DaggerNativePrefixMappingSubcomplexRestriction
noncomputable section
variable (X : SSet.{u}) (A : X.Subcomplex) (k : SimplexCategory)
variable (σ : (A : SSet.{u}).obj (op k)) (b : (A : SSet.{u}).obj (op ⦋0⦌))

def part : (prefixMapping X k σ.val b.val).Subcomplex where
  obj q := setOf (fun s ↦ s.val.val ∈ A.obj (op ((ordinalJoinLeft k).obj q.unop)))
  map {_ _} α _ hs := A.map ((ordinalJoinLeft k).map α.unop).op hs

def forward : prefixMapping (A : SSet.{u}) k σ b ⟶ (part X A k σ b : SSet.{u}) :=
  SSet.Subcomplex.lift (map A.ι k σ b) (by
    intro _ _ hs
    obtain ⟨t, rfl⟩ := hs
    exact t.val.val.property)

theorem forward_comp : forward X A k σ b ≫ (part X A k σ b).ι = map A.ι k σ b :=
  SSet.Subcomplex.lift_ι _ _

def toCoslice : (part X A k σ b : SSet.{u}) ⟶ simplexCoslice k (A : SSet.{u}) σ where
  app q s := ⟨⟨s.val.val.val, s.property⟩, by
    apply Subtype.ext
    exact s.val.val.property⟩
  naturality q r α := by
    funext s
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem toCoslice_projection : toCoslice X A k σ b ≫ cosliceProjection k (A : SSet.{u}) σ =
    (SSet.const b : (part X A k σ b : SSet.{u}) ⟶ (A : SSet.{u})) := by
  apply (cancel_mono A.ι).mp
  apply NatTrans.ext
  funext q s
  have h := (SSet.Subcomplex.fiber_isPullback (cosliceProjection k X σ.val) b.val).w
  have hh := congrFun (NatTrans.congr_app h q) s.val
  simpa only [SSet.yonedaEquiv_symm_zero, SSet.comp_const] using hh

def backward : (part X A k σ b : SSet.{u}) ⟶ prefixMapping (A : SSet.{u}) k σ b :=
  (SSet.Subcomplex.fiber_isPullback (cosliceProjection k (A : SSet.{u}) σ) b).lift
    (toCoslice X A k σ b) (SSet.stdSimplex.objZeroIsTerminal.from _) (by
      rw [toCoslice_projection]
      simp only [SSet.yonedaEquiv_symm_zero, SSet.comp_const])

theorem backward_comp_fiber : backward X A k σ b ≫
    (SSet.Subcomplex.fiber (cosliceProjection k (A : SSet.{u}) σ) b).ι =
      toCoslice X A k σ b :=
  (SSet.Subcomplex.fiber_isPullback (cosliceProjection k (A : SSet.{u}) σ) b).lift_fst _ _ _

theorem backward_comp_map : backward X A k σ b ≫ map A.ι k σ b = (part X A k σ b).ι := by
  apply NatTrans.ext
  funext q s
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun t : (simplexCoslice k (A : SSet.{u}) σ).obj q ↦ t.val.val)
    (congrFun (NatTrans.congr_app (backward_comp_fiber X A k σ b) q) s)

theorem map_mono : Mono (map A.ι k σ b) where
  right_cancellation := by
    intro E f g h
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : (prefixMapping X k σ.val b.val).obj q ↦ t.val.val)
      (congrFun (NatTrans.congr_app h q) s)

def restrictionIso : prefixMapping (A : SSet.{u}) k σ b ≅ (part X A k σ b : SSet.{u}) where
  hom := forward X A k σ b
  inv := backward X A k σ b
  hom_inv_id := by
    have := map_mono X A k σ b
    apply (cancel_mono (map A.ι k σ b)).mp
    rw [Category.assoc, backward_comp_map, forward_comp, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (part X A k σ b).ι).mp
    rw [Category.assoc, forward_comp, backward_comp_map, Category.id_comp]

theorem restrictionIso_hom_comp : (restrictionIso X A k σ b).hom ≫ (part X A k σ b).ι =
    map A.ι k σ b := forward_comp X A k σ b

theorem restrictionIso_inv_comp : (restrictionIso X A k σ b).inv ≫ map A.ι k σ b =
    (part X A k σ b).ι := backward_comp_map X A k σ b

end
end DaggerNativePrefixMappingSubcomplexRestriction
