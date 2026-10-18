import OriginalFlagDegree
import OriginalFlagFlankArrow

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option trace.Elab.command true

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} {n : ℕ}

def flankOver (P : NecklacesOver X a b) (F : Flag.{u} P.code n) :
    NecklacesOver X a b where
  code := flankCode F
  map := ((flankInclusion F).map :
    NecklaceCode.toSSet.{u} (flankCode F) ⟶ NecklaceCode.toSSet.{u} P.code) ≫ P.map
  first := (congrArg (P.map.app (op ⦋0⦌)) (flankInclusion F).first).trans P.first
  last := (congrArg (P.map.app (op ⦋0⦌)) (flankInclusion F).last).trans P.last

def flankDegreeObj (p : Degree X a b n) : Degree X a b n :=
  ⟨flankOver p.1 p.2, flankFlag p.2⟩

def flankOverMap {p q : Degree X a b n} (f : p ⟶ q) :
    flankOver p.1 p.2 ⟶ flankOver q.1 q.2 where
  hom := flankArrow p.2 q.2 f.val.hom f.property
  w := by
    change (flankArrow p.2 q.2 f.val.hom f.property).map ≫
      ((flankInclusion q.2).map ≫ q.1.map) = (flankInclusion p.2).map ≫ p.1.map
    rw [← Category.assoc, flankArrow_square, Category.assoc, f.val.w]

def flankDegreeMap {p q : Degree X a b n} (f : p ⟶ q) :
    flankDegreeObj p ⟶ flankDegreeObj q :=
  CategoryOfElements.homMk (F := flagDegreeDiagram X a b (op ⦋n⦌))
    _ _ (flankOverMap f)
    (flankArrow_flag p.2 q.2 f.val.hom f.property)

/-- A local consequence of the accepted vertex-extensionality, not a new map construction. -/
theorem flankInclusion_cancel {V T : NecklaceCode} (F : Flag.{u} T n)
    (f g : V.toSSet ⟶ (flankCode F).toSSet)
    (h : f ≫ (flankInclusion F).map = g ≫ (flankInclusion F).map) : f = g := by
  apply hom_ext_vertices (T := V) (U := flankCode F)
  funext v
  apply flankVertex_injective F
  have hh := congrFun (congrArg (mapVertices (T := V) (U := T)) h) v
  rw [mapVertices_comp, mapVertices_comp] at hh
  simpa only [Function.comp_apply, flankInclusion_vertex] using hh

theorem flankDegreeMap_id (p : Degree X a b n) :
    flankDegreeMap (𝟙 p) = 𝟙 (flankDegreeObj p) := by
  apply Subtype.ext
  apply NecklacesOver.Hom.ext
  apply NecklaceCode.Hom.ext
  apply flankInclusion_cancel p.2
  change (flankArrow p.2 p.2 (𝟙 p : p ⟶ p).val.hom
    (𝟙 p : p ⟶ p).property).map ≫ (flankInclusion p.2).map =
    (𝟙 _) ≫ (flankInclusion p.2).map
  rw [flankArrow_square]
  change (flankInclusion p.2).map ≫ (𝟙 _) = (𝟙 _) ≫ (flankInclusion p.2).map
  simp only [Category.comp_id, Category.id_comp]

theorem flankDegreeMap_comp {p q r : Degree X a b n} (f : p ⟶ q) (g : q ⟶ r) :
    flankDegreeMap (f ≫ g) = flankDegreeMap f ≫ flankDegreeMap g := by
  apply Subtype.ext
  apply NecklacesOver.Hom.ext
  apply NecklaceCode.Hom.ext
  apply flankInclusion_cancel r.2
  change (flankArrow p.2 r.2 (f ≫ g).val.hom (f ≫ g).property).map ≫
      (flankInclusion r.2).map =
    ((flankArrow p.2 q.2 f.val.hom f.property).map ≫
      (flankArrow q.2 r.2 g.val.hom g.property).map) ≫ (flankInclusion r.2).map
  rw [flankArrow_square, Category.assoc, flankArrow_square, ← Category.assoc,
    flankArrow_square, Category.assoc]
  rfl

def flankification (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ) :
    Degree X a b n ⥤ Degree X a b n where
  obj := flankDegreeObj (X := X) (a := a) (b := b) (n := n)
  map := flankDegreeMap (X := X) (a := a) (b := b) (n := n)
  map_id := flankDegreeMap_id (X := X) (a := a) (b := b) (n := n)
  map_comp := flankDegreeMap_comp (X := X) (a := a) (b := b) (n := n)

def inclusionOver (p : Degree X a b n) : (flankDegreeObj p).1 ⟶ p.1 where
  hom := flankInclusion p.2
  w := rfl

def inclusionDegree (p : Degree X a b n) : flankDegreeObj p ⟶ p :=
  CategoryOfElements.homMk (F := flagDegreeDiagram X a b (op ⦋n⦌))
    _ _ (inclusionOver p) (flankInclusion_flag p.2)

def inclusion (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ) :
    flankification X a b n ⟶ 𝟭 (Degree X a b n) where
  app := inclusionDegree
  naturality p q f := by
    apply Subtype.ext
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    exact flankArrow_square p.2 q.2 f.val.hom f.property

theorem inclusion_whole_map (p : Degree X a b n) :
    ((inclusion X a b n).app p).val.hom.map = (flankInclusion p.2).map := rfl

theorem flankification_class (p : Degree X a b n) :
    classOf X a b n ((flankification X a b n).obj p) = classOf X a b n p :=
  classOf_map X a b n ((inclusion X a b n).app p)

theorem flankification_flanked (p : Degree X a b n) :
    Flanked ((flankification X a b n).obj p).2 := flankFlag_flanked p.2

end

end DaggerOriginalFlagFlankification
