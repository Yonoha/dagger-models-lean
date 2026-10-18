import OriginalAmbientDaggerIntervalComponents

/-!
# The native simplicial component functor preserves the original tensor operations

Use the original PiZero quotient and native point-to-vertex equivalence. Fixing
one vertex gives an actual simplicial map into the tensor product, so the native
component functor proves compatibility with each quotient relation. Native
Quot.lift2 then pairs the two component classes. The resulting lax monoidal
structure transports arbitrary original enrichments, not just thin intervals.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial
universe u
namespace DaggerOriginalSimplicialPiZeroLaxMonoidal
noncomputable section

/-- Pair an arbitrary original simplex with the native constant simplex at a vertex. -/
def rightVertexInclusion (X Y : SSet.{u}) (b : Y.obj (op ⦋0⦌)) : X ⟶ X ⊗ Y :=
  (ρ_ X).inv ≫ X ◁ (SSet.unitHomEquiv Y).symm b

/-- The right inclusion pairs the unchanged original vertices. -/
theorem rightVertexInclusion_zero (X Y : SSet.{u}) (b : Y.obj (op ⦋0⦌))
    (a : X.obj (op ⦋0⦌)) : (rightVertexInclusion X Y b).app (op ⦋0⦌) a = (a, b) := by
  change (a, ((SSet.unitHomEquiv Y).symm b).app (op ⦋0⦌) PUnit.unit) = (a, b)
  exact congrArg (fun z ↦ (a, z)) ((SSet.unitHomEquiv Y).apply_symm_apply b)

/-- Pair a native constant simplex at a vertex with an arbitrary original simplex. -/
def leftVertexInclusion (X Y : SSet.{u}) (a : X.obj (op ⦋0⦌)) : Y ⟶ X ⊗ Y :=
  (λ_ Y).inv ≫ (SSet.unitHomEquiv X).symm a ▷ Y

/-- The left inclusion pairs the unchanged original vertices. -/
theorem leftVertexInclusion_zero (X Y : SSet.{u}) (a : X.obj (op ⦋0⦌))
    (b : Y.obj (op ⦋0⦌)) : (leftVertexInclusion X Y a).app (op ⦋0⦌) b = (a, b) := by
  change (((SSet.unitHomEquiv X).symm a).app (op ⦋0⦌) PUnit.unit, b) = (a, b)
  exact congrArg (fun z ↦ (z, b)) ((SSet.unitHomEquiv X).apply_symm_apply a)

/-- The native relation in the second Hom coordinate remains the native product relation. -/
theorem pair_respects_right (X Y : SSet.{u}) (a : X.obj (op ⦋0⦌))
    (b c : Y.obj (op ⦋0⦌)) (h : SSet.π₀Rel b c) :
    SSet.π₀.mk (X := X ⊗ Y) (a, b) = SSet.π₀.mk (a, c) := by
  have hh : SSet.mapπ₀ (leftVertexInclusion X Y a) (SSet.π₀.mk b) =
      SSet.mapπ₀ (leftVertexInclusion X Y a) (SSet.π₀.mk c) :=
    congrArg (SSet.mapπ₀ (leftVertexInclusion X Y a)) (Quot.sound h)
  simpa only [SSet.mapπ₀_mk, leftVertexInclusion_zero] using hh

/-- The native relation in the first Hom coordinate remains the native product relation. -/
theorem pair_respects_left (X Y : SSet.{u}) (a b : X.obj (op ⦋0⦌))
    (c : Y.obj (op ⦋0⦌)) (h : SSet.π₀Rel a b) :
    SSet.π₀.mk (X := X ⊗ Y) (a, c) = SSet.π₀.mk (b, c) := by
  have hh : SSet.mapπ₀ (rightVertexInclusion X Y c) (SSet.π₀.mk a) =
      SSet.mapπ₀ (rightVertexInclusion X Y c) (SSet.π₀.mk b) :=
    congrArg (SSet.mapπ₀ (rightVertexInclusion X Y c)) (Quot.sound h)
  simpa only [SSet.mapπ₀_mk, rightVertexInclusion_zero] using hh

/-- Pair the two actual native component classes by the native quotient eliminator. -/
def pairComponents (X Y : SSet.{u}) : X.π₀ → Y.π₀ → (X ⊗ Y).π₀ :=
  Quot.lift₂ (fun a b ↦ SSet.π₀.mk (X := X ⊗ Y) (a, b))
    (pair_respects_right X Y) (pair_respects_left X Y)

/-- On all original vertices the quotient pairing is the original tensor vertex. -/
theorem pairComponents_mk (X Y : SSet.{u})
    (a : X.obj (op ⦋0⦌)) (b : Y.obj (op ⦋0⦌)) :
    pairComponents X Y (SSet.π₀.mk a) (SSet.π₀.mk b) = SSet.π₀.mk (a, b) := rfl

/-- The component functor transports the exact original identities and compositions. -/
instance piZeroLaxMonoidal : SSet.π₀Functor.{u}.LaxMonoidal where
  ε _ := SSet.π₀.mk PUnit.unit
  μ X Y p := pairComponents X Y p.1 p.2
  μ_natural_left f Z := by
    funext p
    obtain ⟨a, ha⟩ := SSet.π₀.mk_surjective p.1
    obtain ⟨b, hb⟩ := SSet.π₀.mk_surjective p.2
    obtain ⟨_, _⟩ := p
    cases ha
    cases hb
    rfl
  μ_natural_right X f := by
    funext p
    obtain ⟨a, ha⟩ := SSet.π₀.mk_surjective p.1
    obtain ⟨b, hb⟩ := SSet.π₀.mk_surjective p.2
    obtain ⟨_, _⟩ := p
    cases ha
    cases hb
    rfl
  associativity X Y Z := by
    funext p
    obtain ⟨⟨a, b⟩, c⟩ := p
    obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
    obtain ⟨b, rfl⟩ := SSet.π₀.mk_surjective b
    obtain ⟨c, rfl⟩ := SSet.π₀.mk_surjective c
    rfl
  left_unitality X := by
    funext p
    obtain ⟨a, b⟩ := p
    cases a
    obtain ⟨b, rfl⟩ := SSet.π₀.mk_surjective b
    rfl
  right_unitality X := by
    funext p
    obtain ⟨a, b⟩ := p
    cases b
    obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
    rfl

end
end DaggerOriginalSimplicialPiZeroLaxMonoidal
