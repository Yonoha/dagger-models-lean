import NativeSimplexIndexResolutionColumnRoundtrips

/-! Recover the original under-category arrows and full chains from their parameters. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeSimplexIndexResolution DaggerNativeSimplicialReplacementCells
open DaggerNativeSimplexIndexResolutionColumnData
open DaggerNativeSimplexIndexResolutionColumnRoundtrips DaggerOriginalProductGadget
universe u
namespace DaggerNativeSimplexIndexResolutionColumnInverse
noncomputable section

theorem parameterArrow_heq (X : SSet.{u}) (k : SimplexCategoryᵒᵖ) (P : LiftedIndex X)
    (t : ((diagram X).obj P).obj k) (x : X.obj k) (f : simplexObj X k x ⟶ P)
    (ht : t.down = f.down.left) : HEq (parameterArrow X k P t) f := by
  have hx : (ULiftHom.down.{0, u, u}.obj P).hom.app k t = x := by
    have ht' : t = ULift.up f.down.left := ULift.ext _ _ ht
    rw [ht']
    exact underArrow_image X k x P f
  cases hx
  apply heq_of_eq
  apply ULift.ext
  exact CostructuredArrow.hom_ext _ _ ht

theorem underObject_eq {C : Type u} [Category.{u} C] {s : C}
    {a b : StructuredArrow s (𝟭 C)} (h : a.right = b.right)
    (hh : HEq a.hom b.hom) : a = b :=
  Comma.ext (Subsingleton.elim _ _) h hh

theorem underHom_heq {C : Type u} [Category.{u} C] {s : C}
    {a b c d : StructuredArrow s (𝟭 C)} (ha : a = c) (hb : b = d)
    (f : a ⟶ b) (g : c ⟶ d) (h : HEq f.right g.right) : HEq f g := by
  cases ha
  cases hb
  exact heq_of_eq (StructuredArrow.hom_ext f g (eq_of_heq h))

def chainLift {C : Type u} [Category.{u} C] {s : C} {n : ℕ}
    (c : Fin (n + 1) ⥤ C) (f : s ⟶ c.obj 0) :
    Fin (n + 1) ⥤ StructuredArrow s (𝟭 C) where
  obj i := StructuredArrow.mk (Y := c.obj i) (f ≫ c.map (homOfLE (Fin.zero_le i)))
  map {i j} g := StructuredArrow.homMk (c.map g) (by
    change (f ≫ c.map _) ≫ c.map g = f ≫ c.map _
    rw [Category.assoc, ← c.map_comp]
    congr 1)
  map_id i := by apply StructuredArrow.hom_ext; exact c.map_id i
  map_comp g h := by apply StructuredArrow.hom_ext; exact c.map_comp g h

theorem chain_reconstruct {C : Type u} [Category.{u} C] {s : C} {n : ℕ}
    (B : Fin (n + 1) ⥤ StructuredArrow s (𝟭 C)) :
    chainLift (B ⋙ StructuredArrow.proj s (𝟭 C)) (B.obj 0).hom = B := by
  have hobj : ∀ i,
      (chainLift (B ⋙ StructuredArrow.proj s (𝟭 C)) (B.obj 0).hom).obj i = B.obj i := by
    intro i
    apply underObject_eq
      (a := (chainLift (B ⋙ StructuredArrow.proj s (𝟭 C)) (B.obj 0).hom).obj i)
      (b := B.obj i) rfl
    exact heq_of_eq (StructuredArrow.w (B.map (homOfLE (Fin.zero_le i))))
  refine CategoryTheory.Functor.hext hobj ?_
  intro i j f
  apply underHom_heq (hobj i) (hobj j)
  rfl

theorem chainLift_heq {C : Type u} [Category.{u} C] {s s' : C} {n : ℕ}
    {c c' : Fin (n + 1) ⥤ C} {f : s ⟶ c.obj 0} {f' : s' ⟶ c'.obj 0}
    (hs : s = s') (hc : c = c') (hf : HEq f f') :
    HEq (chainLift c f) (chainLift c' f') := by
  cases hs
  cases hc
  cases hf
  rfl

theorem parameterArrow_general_heq (X : SSet.{u}) (k : SimplexCategoryᵒᵖ)
    (P Q : LiftedIndex X) (t : ((diagram X).obj P).obj k) (x : X.obj k)
    (f : simplexObj X k x ⟶ Q) (hP : P = Q) (ht : HEq t.down f.down.left) :
    HEq (parameterArrow X k P t) f := by
  cases hP
  exact parameterArrow_heq X k P t x f (eq_of_heq ht)

/-- Reconstruction retains all objects and arrows of the original under-chain. -/
theorem underChain_heq (X : SSet.{u}) (q k : SimplexCategoryᵒᵖ)
    (c : (nerve (LiftedIndex X)).obj q) (t : ((diagram X).obj (first c)).obj k)
    (x : X.obj k) (B : (nerve (Under X k x)).obj q)
    (hx : (ULiftHom.down.{0, u, u}.obj (first c)).hom.app k t = x)
    (hc : B ⋙ StructuredArrow.proj (simplexObj X k x) (𝟭 (LiftedIndex X)) = c)
    (hf : HEq (B.obj 0).hom.down.left t.down) : HEq (underChain X q k ⟨c, t⟩) B := by
  have hstart := parameterArrow_general_heq X k (first c) (B.obj 0).right t x
    (B.obj 0).hom (CategoryTheory.Functor.congr_obj hc 0).symm hf.symm
  have hlift := chainLift_heq (congrArg (simplexObj X k) hx) hc.symm hstart
  exact hlift.trans (heq_of_eq (chain_reconstruct B))

theorem to_from (X : SSet.{u}) (q k : SimplexCategoryᵒᵖ)
    (z : (familySSet (columnFamily X k)).obj q) :
    toFamily X q k (fromFamily X q k z) = z := by
  rcases z with ⟨x, B⟩
  exact Sigma.ext (image_fromFamily X q k ⟨x, B⟩)
    (underChain_heq X q k _ _ x B (image_fromFamily X q k ⟨x, B⟩) rfl HEq.rfl)

end
end DaggerNativeSimplexIndexResolutionColumnInverse
