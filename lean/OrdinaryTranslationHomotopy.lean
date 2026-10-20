import OrdinaryTranslationMaps
import TopCatModelCategory.SSet.Homotopy
import TopCatModelCategory.SSet.KanComplexWHomotopy
import TopCatModelCategory.TopCat.Homotopy
import TopCatModelCategory.TopCat.HornDeformationRetract

set_option autoImplicit false
set_option maxHeartbeats 0
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite Simplicial DaggerModels

universe o v

namespace DaggerOrdinaryTranslation

noncomputable section
variable (C : SimplicialCat.{o, v})

abbrev R : SSet.{v} ⥤ SSet.{v} := SSet.toTop ⋙ TopCat.toSSet

/-- The genuine scalar reorder followed by original precomposition. -/
def edgePre {x' x : C.Obj} (e : H C x' x _⦋1⦌) (y : C.Obj) :
    H C x y ⊗ Δ[1] ⟶ H C x' y :=
  lift (snd _ _ ≫ SSet.yonedaEquiv.symm e) (fst _ _) ≫ C.enriched.comp x' x y

def edgePost (x : C.Obj) {y y' : C.Obj} (e : H C y y' _⦋1⦌) :
    H C x y ⊗ Δ[1] ⟶ H C x y' :=
  lift (fst _ _) (snd _ _ ≫ SSet.yonedaEquiv.symm e) ≫ C.enriched.comp x y y'

private theorem edge_vertex_zero {Y Z : SSet.{v}} (e : Y _⦋1⦌) :
    SSet.const (X := Z) (SSet.stdSimplex.obj₀Equiv.symm 0) ≫
      SSet.yonedaEquiv.symm e = SSet.const (Y.δ 1 e) := by
  rw [SSet.const_comp]
  congr 1
  have hc : (SSet.stdSimplex.obj₀Equiv.symm 0 : (Δ[1] : SSet.{v}) _⦋0⦌) =
      SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ 1) := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    rfl
  rw [hc]
  rfl

private theorem edge_vertex_one {Y Z : SSet.{v}} (e : Y _⦋1⦌) :
    SSet.const (X := Z) (SSet.stdSimplex.obj₀Equiv.symm 1) ≫
      SSet.yonedaEquiv.symm e = SSet.const (Y.δ 0 e) := by
  rw [SSet.const_comp]
  congr 1
  have hc : (SSet.stdSimplex.obj₀Equiv.symm 1 : (Δ[1] : SSet.{v}) _⦋0⦌) =
      SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ 0) := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    rfl
  rw [hc]
  rfl

theorem edgePre_zero {x' x : C.Obj} (e : H C x' x _⦋1⦌) (y : C.Obj) :
    SSet.ι₀ ≫ edgePre C e y = pre C ((H C x' x).δ 1 e) y := by
  dsimp only [edgePre, pre]
  rw [← Category.assoc]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, SSet.ι₀_snd_assoc, edge_vertex_zero]
  · simp

theorem edgePre_one {x' x : C.Obj} (e : H C x' x _⦋1⦌) (y : C.Obj) :
    SSet.ι₁ ≫ edgePre C e y = pre C ((H C x' x).δ 0 e) y := by
  dsimp only [edgePre, pre]
  rw [← Category.assoc]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, SSet.ι₁_snd_assoc, edge_vertex_one]
  · simp

theorem edgePost_zero (x : C.Obj) {y y' : C.Obj} (e : H C y y' _⦋1⦌) :
    SSet.ι₀ ≫ edgePost C x e = post C x ((H C y y').δ 1 e) := by
  dsimp only [edgePost, post]
  rw [← Category.assoc]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp only [Category.assoc, lift_snd, SSet.ι₀_snd_assoc, edge_vertex_zero]

theorem edgePost_one (x : C.Obj) {y y' : C.Obj} (e : H C y y' _⦋1⦌) :
    SSet.ι₁ ≫ edgePost C x e = post C x ((H C y y').δ 0 e) := by
  dsimp only [edgePost, post]
  rw [← Category.assoc]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp only [Category.assoc, lift_snd, SSet.ι₁_snd_assoc, edge_vertex_one]

def edgePreHomotopy {x' x : C.Obj} (e : H C x' x _⦋1⦌) (y : C.Obj) :
    SSet.Homotopy (pre C ((H C x' x).δ 1 e) y) (pre C ((H C x' x).δ 0 e) y) :=
  SSet.Homotopy.mk (edgePre C e y) (edgePre_zero C e y) (edgePre_one C e y)

def edgePostHomotopy (x : C.Obj) {y y' : C.Obj} (e : H C y y' _⦋1⦌) :
    SSet.Homotopy (post C x ((H C y y').δ 1 e)) (post C x ((H C y y').δ 0 e)) :=
  SSet.Homotopy.mk (edgePost C x e) (edgePost_zero C x e) (edgePost_one C x e)

/-- Actual pi0 equality induces homotopy on the original singular-realization maps. -/
theorem preHomotopy_exists {x' x : C.Obj} {a₀ a₁ : H C x' x _⦋0⦌}
    (h : SSet.π₀.mk a₀ = SSet.π₀.mk a₁) (y : C.Obj) :
    Nonempty (SSet.Homotopy (R.map (pre C a₀ y)) (R.map (pre C a₁ y))) := by
  have he := (SSet.π₀.mk_eq_mk_iff a₀ a₁).1 h
  clear h
  induction he with
  | rel a b h =>
    rcases h with ⟨e, ha, hb⟩
    exact ⟨((edgePreHomotopy C e y).congr (by rw [ha]) (by rw [hb])).toTop.toSSet⟩
  | refl => exact ⟨SSet.Subcomplex.RelativeMorphism.Homotopy.ofEq rfl⟩
  | symm _ _ _ ih => exact ⟨ih.some.symm⟩
  | trans _ _ _ _ _ ih ih' => exact ⟨ih.some.trans ih'.some⟩

theorem postHomotopy_exists (x : C.Obj) {y y' : C.Obj} {b₀ b₁ : H C y y' _⦋0⦌}
    (h : SSet.π₀.mk b₀ = SSet.π₀.mk b₁) :
    Nonempty (SSet.Homotopy (R.map (post C x b₀)) (R.map (post C x b₁))) := by
  have he := (SSet.π₀.mk_eq_mk_iff b₀ b₁).1 h
  clear h
  induction he with
  | rel a b h =>
    rcases h with ⟨e, ha, hb⟩
    exact ⟨((edgePostHomotopy C x e).congr (by rw [ha]) (by rw [hb])).toTop.toSSet⟩
  | refl => exact ⟨SSet.Subcomplex.RelativeMorphism.Homotopy.ofEq rfl⟩
  | symm _ _ _ ih => exact ⟨ih.some.symm⟩
  | trans _ _ _ _ _ ih ih' => exact ⟨ih.some.trans ih'.some⟩


/-- A chosen full homotopy with the exact singular-realization endpoint maps. -/
def preHomotopy {x' x : C.Obj} {a₀ a₁ : H C x' x _⦋0⦌}
    (h : SSet.π₀.mk a₀ = SSet.π₀.mk a₁) (y : C.Obj) :
    SSet.Homotopy (R.map (pre C a₀ y)) (R.map (pre C a₁ y)) :=
  (preHomotopy_exists C h y).some

def postHomotopy (x : C.Obj) {y y' : C.Obj} {b₀ b₁ : H C y y' _⦋0⦌}
    (h : SSet.π₀.mk b₀ = SSet.π₀.mk b₁) :
    SSet.Homotopy (R.map (post C x b₀)) (R.map (post C x b₁)) :=
  (postHomotopy_exists C x h).some

end

end DaggerOrdinaryTranslation
