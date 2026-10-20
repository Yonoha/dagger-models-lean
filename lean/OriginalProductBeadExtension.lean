import OriginalProductGadgetData
import ChosenNecklaceMapInclusion
import ChosenNecklaceSingleBead

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalProductGadget

noncomputable section

open DaggerChosenRigidificationNecklace

/-- Extend a necklace map into a simplex using its existing monotone vertex operator. -/
def simplexExtension (T : NecklaceCode) (n : ℕ) (f : T.toSSet ⟶ Δ[n]) :
    (Δ[T.len] : SSet.{u}) ⟶ Δ[n] :=
  SSet.stdSimplex.map (SimplexCategory.Hom.mk
    (NecklaceCode.orderMap (f ≫ (NecklaceCode.singleIso n).inv)))

theorem simplexExtension_fac (T : NecklaceCode) (n : ℕ) (f : T.toSSet ⟶ Δ[n]) :
    T.inclusion ≫ simplexExtension T n f = f := by
  have h := NecklaceCode.map_inclusion
    (T := T) (U := NecklaceCode.single n) (f ≫ (NecklaceCode.singleIso n).inv)
  rw [← NecklaceCode.singleIso_hom] at h
  have h' : f = T.inclusion ≫ simplexExtension T n f := by
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      simplexExtension] using h
  exact h'.symm

theorem simplexExtension_unique (T : NecklaceCode) (n : ℕ)
    (f : T.toSSet ⟶ Δ[n]) (g : (Δ[T.len] : SSet.{u}) ⟶ Δ[n])
    (hg : T.inclusion ≫ g = f) : g = simplexExtension T n f := by
  apply stdSimplex_hom_ext
  intro x
  let y := T.verticesEquiv.symm
    (ULift.up (SSet.stdSimplex.obj₀Equiv x))
  have hy : T.inclusion.app (op ⦋0⦌) y = x := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    simpa only [y] using T.inclusion_vertex
      (ULift.up (SSet.stdSimplex.obj₀Equiv x))
  have h₁ := congrFun (NatTrans.congr_app hg (op ⦋0⦌)) y
  have h₂ := congrFun
    (NatTrans.congr_app (simplexExtension_fac T n f) (op ⦋0⦌)) y
  change g.app _ (T.inclusion.app _ y) = f.app _ y at h₁
  change (simplexExtension T n f).app _ (T.inclusion.app _ y) = f.app _ y at h₂
  rw [hy] at h₁ h₂
  exact h₁.trans h₂.symm

/-- The actual finite product of standard simplex beads. -/
def simplexProduct (m : ℕ) (dim : Fin m → ℕ) : SSet.{u} :=
  ∏ᶜ fun i : Fin m ↦ (Δ[dim i] : SSet.{u})

/-- Extend a necklace map into every bead component, then use the product UP. -/
def simplexProductExtension (T : NecklaceCode) (m : ℕ) (dim : Fin m → ℕ)
    (f : NecklaceCode.toSSet.{u} T ⟶ simplexProduct.{u} m dim) :
    (Δ[T.len] : SSet.{u}) ⟶ simplexProduct.{u} m dim :=
  Pi.lift (fun i : Fin m ↦ simplexExtension T (dim i)
    (f ≫ Pi.π (fun j : Fin m ↦ (Δ[dim j] : SSet.{u})) i))

theorem simplexProductExtension_fac (T : NecklaceCode) (m : ℕ) (dim : Fin m → ℕ)
    (f : NecklaceCode.toSSet.{u} T ⟶ simplexProduct.{u} m dim) :
    T.inclusion ≫ simplexProductExtension T m dim f = f := by
  apply Pi.hom_ext
  intro i
  change (T.inclusion ≫ Pi.lift (fun j : Fin m ↦ simplexExtension T (dim j)
    (f ≫ Pi.π (fun k : Fin m ↦ (Δ[dim k] : SSet.{u})) j))) ≫
      Pi.π (fun j : Fin m ↦ (Δ[dim j] : SSet.{u})) i =
        f ≫ Pi.π (fun j : Fin m ↦ (Δ[dim j] : SSet.{u})) i
  rw [Category.assoc, Pi.lift_π, simplexExtension_fac]

theorem simplexProductExtension_unique (T : NecklaceCode) (m : ℕ) (dim : Fin m → ℕ)
    (f : NecklaceCode.toSSet.{u} T ⟶ simplexProduct.{u} m dim)
    (g : (Δ[T.len] : SSet.{u}) ⟶ simplexProduct.{u} m dim)
    (hg : T.inclusion ≫ g = f) : g = simplexProductExtension T m dim f := by
  apply Pi.hom_ext
  intro i
  have hi : T.inclusion ≫
      (g ≫ Pi.π (fun j : Fin m ↦ (Δ[dim j] : SSet.{u})) i) =
        f ≫ Pi.π (fun j : Fin m ↦ (Δ[dim j] : SSet.{u})) i := by
    rw [← Category.assoc, hg]
  have h := simplexExtension_unique T (dim i)
    (f ≫ Pi.π (fun j : Fin m ↦ (Δ[dim j] : SSet.{u})) i)
    (g ≫ Pi.π (fun j : Fin m ↦ (Δ[dim j] : SSet.{u})) i) hi
  change g ≫ Pi.π (fun j : Fin m ↦ (Δ[dim j] : SSet.{u})) i =
    (Pi.lift (fun j : Fin m ↦ simplexExtension T (dim j)
      (f ≫ Pi.π (fun k : Fin m ↦ (Δ[dim k] : SSet.{u})) j))) ≫
        Pi.π (fun j : Fin m ↦ (Δ[dim j] : SSet.{u})) i
  rw [Pi.lift_π]
  exact h

/-- Transport between actual one-bead necklace codes and standard simplex beads. -/
def beadProductIso (m : ℕ) (dim : Fin m → ℕ) :
    productSpace.{u} m (fun i ↦ NecklaceCode.single (dim i)) ≅
      simplexProduct.{u} m dim :=
  Pi.mapIso (fun i ↦ NecklaceCode.singleIso (dim i))

/-- The extension into the literal product of necklace beads. -/
def beadProductExtension (T : NecklaceCode) (m : ℕ) (dim : Fin m → ℕ)
    (f : NecklaceCode.toSSet.{u} T ⟶
      productSpace.{u} m (fun i ↦ NecklaceCode.single (dim i))) :
    (Δ[T.len] : SSet.{u}) ⟶
      productSpace.{u} m (fun i ↦ NecklaceCode.single (dim i)) :=
  simplexProductExtension T m dim (f ≫ (beadProductIso m dim).hom) ≫
    (beadProductIso m dim).inv

theorem beadProductExtension_fac (T : NecklaceCode) (m : ℕ) (dim : Fin m → ℕ)
    (f : NecklaceCode.toSSet.{u} T ⟶
      productSpace.{u} m (fun i ↦ NecklaceCode.single (dim i))) :
    T.inclusion ≫ beadProductExtension T m dim f = f := by
  dsimp [beadProductExtension]
  rw [← Category.assoc, simplexProductExtension_fac, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

theorem beadProductExtension_unique (T : NecklaceCode) (m : ℕ) (dim : Fin m → ℕ)
    (f : NecklaceCode.toSSet.{u} T ⟶
      productSpace.{u} m (fun i ↦ NecklaceCode.single (dim i)))
    (g : (Δ[T.len] : SSet.{u}) ⟶
      productSpace.{u} m (fun i ↦ NecklaceCode.single (dim i)))
    (hg : T.inclusion ≫ g = f) : g = beadProductExtension T m dim f := by
  apply (cancel_mono (beadProductIso m dim).hom).1
  rw [beadProductExtension, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply simplexProductExtension_unique
  rw [← Category.assoc, hg]

/-- The ambient simplex map already determined by a necklace map. -/
def ambientSimplexMap {T U : NecklaceCode}
    (h : NecklaceCode.toSSet.{u} T ⟶ NecklaceCode.toSSet.{u} U) :
    (Δ[T.len] : SSet.{u}) ⟶ (Δ[U.len] : SSet.{u}) :=
  SSet.stdSimplex.map (SimplexCategory.Hom.mk (NecklaceCode.orderMap h))

theorem ambientSimplexMap_fac {T U : NecklaceCode}
    (h : NecklaceCode.toSSet.{u} T ⟶ NecklaceCode.toSSet.{u} U) :
    T.inclusion ≫ ambientSimplexMap h = h ≫ U.inclusion := by
  exact (NecklaceCode.map_inclusion h).symm

theorem ambientSimplexMap_unique {T U : NecklaceCode}
    (h : NecklaceCode.toSSet.{u} T ⟶ NecklaceCode.toSSet.{u} U)
    (g : (Δ[T.len] : SSet.{u}) ⟶ (Δ[U.len] : SSet.{u}))
    (hg : T.inclusion ≫ g = h ≫ U.inclusion) : g = ambientSimplexMap h := by
  exact (simplexExtension_unique T U.len (h ≫ U.inclusion) g hg).trans
    (simplexExtension_unique T U.len (h ≫ U.inclusion)
      (ambientSimplexMap h) (ambientSimplexMap_fac h)).symm

theorem ambientSimplexMap_id (T : NecklaceCode) :
    ambientSimplexMap (𝟙 (T.toSSet : SSet.{u})) = 𝟙 (Δ[T.len] : SSet.{u}) := by
  symm
  apply ambientSimplexMap_unique
  simp

theorem ambientSimplexMap_comp {T U V : NecklaceCode}
    (h : NecklaceCode.toSSet.{u} T ⟶ NecklaceCode.toSSet.{u} U)
    (k : NecklaceCode.toSSet.{u} U ⟶ NecklaceCode.toSSet.{u} V) :
    ambientSimplexMap (h ≫ k) = ambientSimplexMap h ≫ ambientSimplexMap k := by
  have hfac : T.inclusion ≫ (ambientSimplexMap h ≫ ambientSimplexMap k) =
      (h ≫ k) ≫ V.inclusion := by
    rw [← Category.assoc, ambientSimplexMap_fac, Category.assoc,
      ambientSimplexMap_fac, ← Category.assoc]
  exact (ambientSimplexMap_unique (h ≫ k)
    (ambientSimplexMap h ≫ ambientSimplexMap k) hfac).symm

theorem beadProductExtension_naturality {T U : NecklaceCode}
    (h : NecklaceCode.toSSet.{u} T ⟶ NecklaceCode.toSSet.{u} U)
    (m : ℕ) (dim : Fin m → ℕ)
    (f : NecklaceCode.toSSet.{u} U ⟶
      productSpace.{u} m (fun i ↦ NecklaceCode.single (dim i))) :
    ambientSimplexMap h ≫ beadProductExtension U m dim f =
      beadProductExtension T m dim (h ≫ f) := by
  apply beadProductExtension_unique T m dim (h ≫ f)
  rw [← Category.assoc, ambientSimplexMap_fac, Category.assoc,
    beadProductExtension_fac]

end

end DaggerOriginalProductGadget
