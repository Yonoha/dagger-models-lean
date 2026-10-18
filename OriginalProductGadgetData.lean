import ChosenNecklaceCategory

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalProductGadget

noncomputable section

open DaggerChosenRigidificationNecklace

/-- The actual finite product of the simplicial sets represented by necklace codes. -/
def productSpace (n : ℕ) (factor : Fin n → NecklaceCode) : SSet.{u} :=
  ∏ᶜ fun i : Fin n ↦ NecklaceCode.toSSet.{u} (factor i)

/-- A component of a product vertex, read through the necklace's vertex equivalence. -/
def vertex (n : ℕ) (factor : Fin n → NecklaceCode) (i : Fin n)
    (x : (productSpace.{u} n factor).obj (op ⦋0⦌)) : Fin ((factor i).len + 1) :=
  ((factor i).verticesEquiv
    ((Pi.π (fun j : Fin n ↦ NecklaceCode.toSSet.{u} (factor j)) i).app _ x)).down

/-- A finite product of actual necklaces with comparable chosen endpoints. -/
structure Code where
  arity : ℕ
  factor : Fin arity → NecklaceCode
  alpha : (productSpace.{u} arity factor).obj (op ⦋0⦌)
  omega : (productSpace.{u} arity factor).obj (op ⦋0⦌)
  comparable : ∀ i : Fin arity, vertex arity factor i alpha ≤ vertex arity factor i omega

def Code.space (P : Code.{u}) : SSet.{u} := productSpace P.arity P.factor

/-- The empty product carries its unique chosen vertex at both ends. -/
def zeroVertex : (productSpace.{u} 0 (fun i : Fin 0 ↦ i.elim0)).obj (op ⦋0⦌) :=
  (Pi.lift (P := (Δ[0] : SSet.{u})) (fun i : Fin 0 ↦ i.elim0)).app _
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))

def zero : Code.{u} where
  arity := 0
  factor := fun i ↦ i.elim0
  alpha := zeroVertex
  omega := zeroVertex
  comparable := fun i ↦ i.elim0

/-- The zero-factor realization is a terminal simplicial set. -/
def zeroIsTerminal : IsTerminal zero.space :=
  IsTerminal.ofUniqueHom
    (fun _ ↦ Pi.lift (fun i : Fin 0 ↦ i.elim0))
    (fun _ m ↦ Pi.hom_ext m _ (fun i : Fin 0 ↦ i.elim0))

def zeroSpaceIso : zero.space ≅ (Δ[0] : SSet.{u}) :=
  zeroIsTerminal.uniqueUpToIso SSet.stdSimplex.isTerminalObj₀

/-- A single existing necklace, presented as a one-factor product gadget. -/
def singleton (T : NecklaceCode) : Code.{u} where
  arity := 1
  factor := fun _ ↦ T
  alpha := (Pi.lift (fun _ : Fin 1 ↦ 𝟙 T.toSSet)).app _ T.first
  omega := (Pi.lift (fun _ : Fin 1 ↦ 𝟙 T.toSSet)).app _ T.last
  comparable := by
    intro i
    have hπ (x : T.toSSet.obj (op ⦋0⦌)) :
        (Pi.π (fun _ : Fin 1 ↦ T.toSSet) i).app _
          ((Pi.lift (fun _ : Fin 1 ↦ 𝟙 T.toSSet)).app _ x) = x := by
      change ((Pi.lift (fun _ : Fin 1 ↦ 𝟙 T.toSSet) ≫
        Pi.π (fun _ : Fin 1 ↦ T.toSSet) i).app _) x = x
      rw [Pi.lift_π]
      rfl
    change (T.verticesEquiv
      ((Pi.π (fun _ : Fin 1 ↦ T.toSSet) i).app _
        ((Pi.lift (fun _ : Fin 1 ↦ 𝟙 T.toSSet)).app _ T.first))).down ≤
      (T.verticesEquiv
        ((Pi.π (fun _ : Fin 1 ↦ T.toSSet) i).app _
          ((Pi.lift (fun _ : Fin 1 ↦ 𝟙 T.toSSet)).app _ T.last))).down
    rw [hπ T.first, hπ T.last]
    simp [NecklaceCode.first, NecklaceCode.last]

def singletonSpaceIso (T : NecklaceCode) : (singleton T).space ≅ T.toSSet :=
  productUniqueIso (fun _ : Fin 1 ↦ T.toSSet)

theorem singletonSpaceIso_hom (T : NecklaceCode) :
    (singletonSpaceIso T).hom = Pi.π (fun _ : Fin 1 ↦ T.toSSet) 0 := by
  rfl

theorem singletonSpaceIso_alpha (T : NecklaceCode) :
    (singletonSpaceIso T).hom.app (op ⦋0⦌) (singleton T).alpha = T.first := by
  rw [singletonSpaceIso_hom]
  change ((Pi.lift (fun _ : Fin 1 ↦ 𝟙 T.toSSet) ≫
    Pi.π (fun _ : Fin 1 ↦ T.toSSet) 0).app _) T.first = T.first
  rw [Pi.lift_π]
  rfl

theorem singletonSpaceIso_omega (T : NecklaceCode) :
    (singletonSpaceIso T).hom.app (op ⦋0⦌) (singleton T).omega = T.last := by
  rw [singletonSpaceIso_hom]
  change ((Pi.lift (fun _ : Fin 1 ↦ 𝟙 T.toSSet) ≫
    Pi.π (fun _ : Fin 1 ↦ T.toSSet) 0).app _) T.last = T.last
  rw [Pi.lift_π]
  rfl

theorem singletonSpaceIso_inv_alpha (T : NecklaceCode) :
    (singletonSpaceIso T).inv.app (op ⦋0⦌) T.first = (singleton T).alpha := by
  have h := congrFun
    (NatTrans.congr_app (singletonSpaceIso T).hom_inv_id (op ⦋0⦌))
    (singleton T).alpha
  change (singletonSpaceIso T).inv.app _
    ((singletonSpaceIso T).hom.app _ (singleton T).alpha) = (singleton T).alpha at h
  rw [singletonSpaceIso_alpha] at h
  exact h

theorem singletonSpaceIso_inv_omega (T : NecklaceCode) :
    (singletonSpaceIso T).inv.app (op ⦋0⦌) T.last = (singleton T).omega := by
  have h := congrFun
    (NatTrans.congr_app (singletonSpaceIso T).hom_inv_id (op ⦋0⦌))
    (singleton T).omega
  change (singletonSpaceIso T).inv.app _
    ((singletonSpaceIso T).hom.app _ (singleton T).omega) = (singleton T).omega at h
  rw [singletonSpaceIso_omega] at h
  exact h

/-- Every actual endpoint-preserving simplicial map is a gadget morphism. -/
structure Hom (P Q : Code.{u}) where
  map : P.space ⟶ Q.space
  alpha : map.app (op ⦋0⦌) P.alpha = Q.alpha
  omega : map.app (op ⦋0⦌) P.omega = Q.omega

/-- Conjugate an actual necklace map by the one-factor product isomorphisms. -/
def singletonMap {T U : NecklaceCode} (f : NecklaceCode.Hom.{u} T U) :
    Hom (singleton T) (singleton U) where
  map := (singletonSpaceIso T).hom ≫ f.map ≫ (singletonSpaceIso U).inv
  alpha := by
    change (singletonSpaceIso U).inv.app _
      (f.map.app _ ((singletonSpaceIso T).hom.app _ (singleton T).alpha)) =
        (singleton U).alpha
    rw [singletonSpaceIso_alpha, f.first, singletonSpaceIso_inv_alpha]
  omega := by
    change (singletonSpaceIso U).inv.app _
      (f.map.app _ ((singletonSpaceIso T).hom.app _ (singleton T).omega)) =
        (singleton U).omega
    rw [singletonSpaceIso_omega, f.last, singletonSpaceIso_inv_omega]

namespace Hom

@[ext] theorem ext {P Q : Code.{u}} {f g : Hom P Q} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (P : Code.{u}) : Hom P P where
  map := 𝟙 _
  alpha := rfl
  omega := rfl

def comp {P Q R : Code.{u}} (f : Hom P Q) (g : Hom Q R) : Hom P R where
  map := f.map ≫ g.map
  alpha := by change g.map.app _ (f.map.app _ P.alpha) = R.alpha; rw [f.alpha, g.alpha]
  omega := by change g.map.app _ (f.map.app _ P.omega) = R.omega; rw [f.omega, g.omega]

end Hom

instance : Category.{u} Code.{u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext (Category.id_comp f.map)
  comp_id f := Hom.ext (Category.comp_id f.map)
  assoc f g h := Hom.ext (Category.assoc f.map g.map h.map)

def realization : Code.{u} ⥤ SSet.{u} where
  obj P := P.space
  map f := f.map

/-- The existing category of all endpoint-preserving necklace maps sits in gadgets. -/
def singletonFunctor : NecklaceCode ⥤ Code.{u} where
  obj := singleton
  map := singletonMap
  map_id T := by
    apply Hom.ext
    change (singletonSpaceIso T).hom ≫ 𝟙 (T.toSSet) ≫
      (singletonSpaceIso T).inv = 𝟙 ((singleton T).space)
    simp
  map_comp f g := by
    apply Hom.ext
    change (singletonSpaceIso _).hom ≫ (f.map ≫ g.map) ≫
      (singletonSpaceIso _).inv =
        ((singletonSpaceIso _).hom ≫ f.map ≫ (singletonSpaceIso _).inv) ≫
          ((singletonSpaceIso _).hom ≫ g.map ≫ (singletonSpaceIso _).inv)
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Every morphism between one-factor gadgets comes from a necklace morphism. -/
def singletonPreimage {T U : NecklaceCode} (f : Hom (singleton T) (singleton U)) :
    NecklaceCode.Hom.{u} T U where
  map := (singletonSpaceIso T).inv ≫ f.map ≫ (singletonSpaceIso U).hom
  first := by
    change (singletonSpaceIso U).hom.app _
      (f.map.app _ ((singletonSpaceIso T).inv.app _ T.first)) = U.first
    rw [singletonSpaceIso_inv_alpha, f.alpha, singletonSpaceIso_alpha]
  last := by
    change (singletonSpaceIso U).hom.app _
      (f.map.app _ ((singletonSpaceIso T).inv.app _ T.last)) = U.last
    rw [singletonSpaceIso_inv_omega, f.omega, singletonSpaceIso_omega]

/-- The old necklace category is fully faithful inside the product gadgets. -/
def singletonFullyFaithful : singletonFunctor.{u}.FullyFaithful where
  preimage := singletonPreimage
  map_preimage := by
    intro T U f
    apply Hom.ext
    change (singletonSpaceIso T).hom ≫
      ((singletonSpaceIso T).inv ≫ f.map ≫ (singletonSpaceIso U).hom) ≫
        (singletonSpaceIso U).inv = f.map
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id]
  preimage_map := by
    intro T U f
    apply NecklaceCode.Hom.ext
    change (singletonSpaceIso T).inv ≫
      ((singletonSpaceIso T).hom ≫ f.map ≫ (singletonSpaceIso U).inv) ≫
        (singletonSpaceIso U).hom = f.map
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id]

end

end DaggerOriginalProductGadget
