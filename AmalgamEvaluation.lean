import AmalgamRawNaturality
import AmalgamUnitBoundary

/-! Exact declaration terms recovered from the saved original AmalgamEvaluation module.
The handwritten source was unavailable. No theorem statement or definition is redesigned. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

universe u u_1

noncomputable section

theorem DaggerAmalgamSuccessor.familyOO_degreeEquiv_map :
  ∀ (C B : DaggerModels.SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj) (a d : C.Obj)
    (n : Nat) {q q' : Opposite.{1} SimplexCategory}
    (α :
      @Quiver.Hom.{1, 0} (Opposite.{1} SimplexCategory)
        (@Quiver.opposite.{0, 1} SimplexCategory
          (@CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory
            (@CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)))
        q q')
    (h :
      @CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
          SimplexCategory.smallCategory)
        (Type u) CategoryTheory.types.{u}
        (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q),
    @Eq.{u + 1} (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n)
      (@DFunLike.coe.{u + 1, u + 1, u + 1}
        (Equiv.{u + 1, u + 1}
          (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
          (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n))
        (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
        (fun _x_1 => DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n)
        (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
          (Equiv.{u + 1, u + 1}
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
            (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n))
          (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
          (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n)
          (@Equiv.instEquivLike.{u + 1, u + 1}
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
            (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n)))
        (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u} C B x b a d n q')
        (@CategoryTheory.Functor.map.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q q' α h))
      (@DaggerAmalgamRawNaturality.mapOO.{u} C B x b q q' α a d n
        (@DFunLike.coe.{u + 1, u + 1, u + 1}
          (Equiv.{u + 1, u + 1}
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
            (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n))
          (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
          (fun _x_1 => DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n)
          (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
            (Equiv.{u + 1, u + 1}
              (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u) CategoryTheory.types.{u}
                (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
              (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n))
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
            (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n)
            (@Equiv.instEquivLike.{u + 1, u + 1}
              (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u) CategoryTheory.types.{u}
                (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
              (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n)))
          (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u} C B x b a d n q) h)) :=
  fun C B x b a d n {q q'} α h =>
    @Nat.casesAuxOn.{0}
      (fun a_1 =>
        @Eq.{1} Nat n a_1 →
          @Eq.{u + 1} (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n)
            (@DFunLike.coe.{u + 1, u + 1, u + 1}
              (Equiv.{u + 1, u + 1}
                (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
                (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n))
              (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u) CategoryTheory.types.{u}
                (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
              (fun _x_1 => DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n)
              (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                (Equiv.{u + 1, u + 1}
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
                  (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n))
                (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
                (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n)
                (@Equiv.instEquivLike.{u + 1, u + 1}
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
                  (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n)))
              (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u} C B x b a d n q')
              (@CategoryTheory.Functor.map.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u) CategoryTheory.types.{u}
                (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q q' α h))
            (@DaggerAmalgamRawNaturality.mapOO.{u} C B x b q q' α a d n
              (@DFunLike.coe.{u + 1, u + 1, u + 1}
                (Equiv.{u + 1, u + 1}
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
                  (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n))
                (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
                (fun _x_1 => DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n)
                (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                  (Equiv.{u + 1, u + 1}
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
                    (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n))
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
                  (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n)
                  (@Equiv.instEquivLike.{u + 1, u + 1}
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
                    (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n)))
                (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u} C B x b a d n q) h)))
      n
      (fun h_1 =>
        @Eq.ndrec.{0, 1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (fun n =>
            ∀
              (h :
                @CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q),
              @Eq.{u + 1} (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n)
                (@DFunLike.coe.{u + 1, u + 1, u + 1}
                  (Equiv.{u + 1, u + 1}
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
                    (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n))
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
                  (fun _x_1 => DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n)
                  (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                    (Equiv.{u + 1, u + 1}
                      (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u) CategoryTheory.types.{u}
                        (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
                      (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n))
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
                    (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n)
                    (@Equiv.instEquivLike.{u + 1, u + 1}
                      (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u) CategoryTheory.types.{u}
                        (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
                      (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n)))
                  (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u} C B x b a d n q')
                  (@CategoryTheory.Functor.map.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q q' α h))
                (@DaggerAmalgamRawNaturality.mapOO.{u} C B x b q q' α a d n
                  (@DFunLike.coe.{u + 1, u + 1, u + 1}
                    (Equiv.{u + 1, u + 1}
                      (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u) CategoryTheory.types.{u}
                        (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
                      (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n))
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
                    (fun _x_1 => DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n)
                    (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                      (Equiv.{u + 1, u + 1}
                        (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u) CategoryTheory.types.{u}
                          (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
                        (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n))
                      (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u) CategoryTheory.types.{u}
                        (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
                      (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n)
                      (@Equiv.instEquivLike.{u + 1, u + 1}
                        (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u) CategoryTheory.types.{u}
                          (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
                        (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n)))
                    (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u} C B x b a d n q)
                    h)))
          (fun h =>
            @Eq.refl.{u + 1}
              (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@DFunLike.coe.{u + 1, u + 1, u + 1}
                (Equiv.{u + 1, u + 1}
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    q')
                  (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  q')
                (fun _x_1 =>
                  DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                  (Equiv.{u + 1, u + 1}
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      q')
                    (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    q')
                  (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Equiv.instEquivLike.{u + 1, u + 1}
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      q')
                    (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u} C B x b a d
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q')
                (@CategoryTheory.Functor.map.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  q q' α h)))
          n
          (@Eq.symm.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            h_1)
          h)
      (fun n_1 h_1 =>
        @Eq.ndrec.{0, 1} Nat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (fun n =>
            ∀
              (h :
                @CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q),
              @Eq.{u + 1} (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n)
                (@DFunLike.coe.{u + 1, u + 1, u + 1}
                  (Equiv.{u + 1, u + 1}
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
                    (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n))
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
                  (fun _x_1 => DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n)
                  (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                    (Equiv.{u + 1, u + 1}
                      (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u) CategoryTheory.types.{u}
                        (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
                      (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n))
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
                    (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n)
                    (@Equiv.instEquivLike.{u + 1, u + 1}
                      (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u) CategoryTheory.types.{u}
                        (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q')
                      (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d n)))
                  (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u} C B x b a d n q')
                  (@CategoryTheory.Functor.map.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q q' α h))
                (@DaggerAmalgamRawNaturality.mapOO.{u} C B x b q q' α a d n
                  (@DFunLike.coe.{u + 1, u + 1, u + 1}
                    (Equiv.{u + 1, u + 1}
                      (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u) CategoryTheory.types.{u}
                        (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
                      (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n))
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
                    (fun _x_1 => DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n)
                    (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                      (Equiv.{u + 1, u + 1}
                        (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u) CategoryTheory.types.{u}
                          (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
                        (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n))
                      (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u) CategoryTheory.types.{u}
                        (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
                      (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n)
                      (@Equiv.instEquivLike.{u + 1, u + 1}
                        (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u) CategoryTheory.types.{u}
                          (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
                        (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n)))
                    (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u} C B x b a d n q)
                    h)))
          (fun h =>
            @Eq.refl.{u + 1}
              (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@DFunLike.coe.{u + 1, u + 1, u + 1}
                (Equiv.{u + 1, u + 1}
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    q')
                  (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  q')
                (fun _x_1 =>
                  DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                  (Equiv.{u + 1, u + 1}
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      q')
                    (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    q')
                  (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@Equiv.instEquivLike.{u + 1, u + 1}
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      q')
                    (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q' a d
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u} C B x b a d
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  q')
                (@CategoryTheory.Functor.map.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  q q' α h)))
          n
          (@Eq.symm.{1} Nat n
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            h_1)
          h)
      (@Eq.refl.{1} Nat n)

theorem DaggerAmalgamSuccessor.familyNO_degreeEquiv_map :
  ∀ (C B : DaggerModels.SimplicialCat.{u, u}) (x : C.Obj) (b z : B.Obj) (d : C.Obj)
    (n : Nat) {q q' : Opposite.{1} SimplexCategory}
    (α :
      @Quiver.Hom.{1, 0} (Opposite.{1} SimplexCategory)
        (@Quiver.opposite.{0, 1} SimplexCategory
          (@CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory
            (@CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)))
        q q')
    (h :
      @CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
          SimplexCategory.smallCategory)
        (Type u) CategoryTheory.types.{u}
        (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q),
    @Eq.{u + 1} (DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q' z d n)
      (@DFunLike.coe.{u + 1, u + 1, u + 1}
        (Equiv.{u + 1, u + 1}
          (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q')
          (DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q' z d n))
        (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q')
        (fun _x_1 => DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q' z d n)
        (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
          (Equiv.{u + 1, u + 1}
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q')
            (DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q' z d n))
          (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q')
          (DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q' z d n)
          (@Equiv.instEquivLike.{u + 1, u + 1}
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q')
            (DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q' z d n)))
        (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u} C B x b z d n q')
        (@CategoryTheory.Functor.map.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q q' α h))
      (@DaggerAmalgamRawNaturality.mapNO.{u} C B x b q q' α z d n
        (@DFunLike.coe.{u + 1, u + 1, u + 1}
          (Equiv.{u + 1, u + 1}
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q)
            (DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q z d n))
          (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q)
          (fun _x_1 => DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q z d n)
          (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
            (Equiv.{u + 1, u + 1}
              (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u) CategoryTheory.types.{u}
                (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q)
              (DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q z d n))
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q)
            (DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q z d n)
            (@Equiv.instEquivLike.{u + 1, u + 1}
              (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u) CategoryTheory.types.{u}
                (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q)
              (DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q z d n)))
          (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u} C B x b z d n q) h)) :=
  fun C B x b z d n {q q'} α h =>
    @rfl.{u + 1} (DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q' z d n)
      (@DFunLike.coe.{u + 1, u + 1, u + 1}
        (Equiv.{u + 1, u + 1}
          (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q')
          (DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q' z d n))
        (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q')
        (fun _x_1 => DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q' z d n)
        (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
          (Equiv.{u + 1, u + 1}
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q')
            (DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q' z d n))
          (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q')
          (DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q' z d n)
          (@Equiv.instEquivLike.{u + 1, u + 1}
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q')
            (DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q' z d n)))
        (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u} C B x b z d n q')
        (@CategoryTheory.Functor.map.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q q' α h))

theorem DaggerAmalgamSuccessor.familyNN_degreeEquiv_map :
  ∀ (C B : DaggerModels.SimplicialCat.{u, u}) (x : C.Obj) (b z w : B.Obj) (n : Nat)
    {q q' : Opposite.{1} SimplexCategory}
    (α :
      @Quiver.Hom.{1, 0} (Opposite.{1} SimplexCategory)
        (@Quiver.opposite.{0, 1} SimplexCategory
          (@CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory
            (@CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)))
        q q')
    (h :
      @CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
          SimplexCategory.smallCategory)
        (Type u) CategoryTheory.types.{u}
        (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q),
    @Eq.{u + 1} (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n)
      (@DFunLike.coe.{u + 1, u + 1, u + 1}
        (Equiv.{u + 1, u + 1}
          (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
          (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n))
        (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
        (fun _x_1 => DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n)
        (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
          (Equiv.{u + 1, u + 1}
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
            (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n))
          (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
          (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n)
          (@Equiv.instEquivLike.{u + 1, u + 1}
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
            (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n)))
        (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u} C B x b z w n q')
        (@CategoryTheory.Functor.map.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q q' α h))
      (@DaggerAmalgamRawNaturality.mapNN.{u} C B x b q q' α z w n
        (@DFunLike.coe.{u + 1, u + 1, u + 1}
          (Equiv.{u + 1, u + 1}
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
            (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n))
          (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
          (fun _x_1 => DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n)
          (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
            (Equiv.{u + 1, u + 1}
              (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u) CategoryTheory.types.{u}
                (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
              (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n))
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
            (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n)
            (@Equiv.instEquivLike.{u + 1, u + 1}
              (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u) CategoryTheory.types.{u}
                (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
              (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n)))
          (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u} C B x b z w n q) h)) :=
  fun C B x b z w n {q q'} α h =>
    @Nat.casesAuxOn.{0}
      (fun a =>
        @Eq.{1} Nat n a →
          @Eq.{u + 1} (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n)
            (@DFunLike.coe.{u + 1, u + 1, u + 1}
              (Equiv.{u + 1, u + 1}
                (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
                (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n))
              (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u) CategoryTheory.types.{u}
                (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
              (fun _x_1 => DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n)
              (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                (Equiv.{u + 1, u + 1}
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
                  (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n))
                (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
                (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n)
                (@Equiv.instEquivLike.{u + 1, u + 1}
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
                  (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n)))
              (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u} C B x b z w n q')
              (@CategoryTheory.Functor.map.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u) CategoryTheory.types.{u}
                (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q q' α h))
            (@DaggerAmalgamRawNaturality.mapNN.{u} C B x b q q' α z w n
              (@DFunLike.coe.{u + 1, u + 1, u + 1}
                (Equiv.{u + 1, u + 1}
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
                  (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n))
                (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
                (fun _x_1 => DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n)
                (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                  (Equiv.{u + 1, u + 1}
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
                    (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n))
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
                  (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n)
                  (@Equiv.instEquivLike.{u + 1, u + 1}
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
                    (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n)))
                (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u} C B x b z w n q) h)))
      n
      (fun h_1 =>
        @Eq.ndrec.{0, 1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (fun n =>
            ∀
              (h :
                @CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q),
              @Eq.{u + 1} (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n)
                (@DFunLike.coe.{u + 1, u + 1, u + 1}
                  (Equiv.{u + 1, u + 1}
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
                    (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n))
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
                  (fun _x_1 => DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n)
                  (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                    (Equiv.{u + 1, u + 1}
                      (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u) CategoryTheory.types.{u}
                        (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
                      (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n))
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
                    (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n)
                    (@Equiv.instEquivLike.{u + 1, u + 1}
                      (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u) CategoryTheory.types.{u}
                        (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
                      (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n)))
                  (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u} C B x b z w n q')
                  (@CategoryTheory.Functor.map.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q q' α h))
                (@DaggerAmalgamRawNaturality.mapNN.{u} C B x b q q' α z w n
                  (@DFunLike.coe.{u + 1, u + 1, u + 1}
                    (Equiv.{u + 1, u + 1}
                      (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u) CategoryTheory.types.{u}
                        (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
                      (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n))
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
                    (fun _x_1 => DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n)
                    (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                      (Equiv.{u + 1, u + 1}
                        (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u) CategoryTheory.types.{u}
                          (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
                        (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n))
                      (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u) CategoryTheory.types.{u}
                        (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
                      (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n)
                      (@Equiv.instEquivLike.{u + 1, u + 1}
                        (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u) CategoryTheory.types.{u}
                          (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
                        (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n)))
                    (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u} C B x b z w n q)
                    h)))
          (fun h =>
            @Eq.refl.{u + 1}
              (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@DFunLike.coe.{u + 1, u + 1, u + 1}
                (Equiv.{u + 1, u + 1}
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    q')
                  (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  q')
                (fun _x_1 =>
                  DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                  (Equiv.{u + 1, u + 1}
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      q')
                    (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    q')
                  (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Equiv.instEquivLike.{u + 1, u + 1}
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      q')
                    (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u} C B x b z w
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q')
                (@CategoryTheory.Functor.map.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  q q' α h)))
          n
          (@Eq.symm.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            h_1)
          h)
      (fun n_1 h_1 =>
        @Eq.ndrec.{0, 1} Nat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (fun n =>
            ∀
              (h :
                @CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q),
              @Eq.{u + 1} (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n)
                (@DFunLike.coe.{u + 1, u + 1, u + 1}
                  (Equiv.{u + 1, u + 1}
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
                    (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n))
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
                  (fun _x_1 => DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n)
                  (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                    (Equiv.{u + 1, u + 1}
                      (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u) CategoryTheory.types.{u}
                        (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
                      (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n))
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
                    (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n)
                    (@Equiv.instEquivLike.{u + 1, u + 1}
                      (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u) CategoryTheory.types.{u}
                        (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q')
                      (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w n)))
                  (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u} C B x b z w n q')
                  (@CategoryTheory.Functor.map.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q q' α h))
                (@DaggerAmalgamRawNaturality.mapNN.{u} C B x b q q' α z w n
                  (@DFunLike.coe.{u + 1, u + 1, u + 1}
                    (Equiv.{u + 1, u + 1}
                      (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u) CategoryTheory.types.{u}
                        (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
                      (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n))
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
                    (fun _x_1 => DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n)
                    (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                      (Equiv.{u + 1, u + 1}
                        (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u) CategoryTheory.types.{u}
                          (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
                        (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n))
                      (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u) CategoryTheory.types.{u}
                        (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
                      (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n)
                      (@Equiv.instEquivLike.{u + 1, u + 1}
                        (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u) CategoryTheory.types.{u}
                          (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
                        (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n)))
                    (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u} C B x b z w n q)
                    h)))
          (fun h =>
            @Eq.refl.{u + 1}
              (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@DFunLike.coe.{u + 1, u + 1, u + 1}
                (Equiv.{u + 1, u + 1}
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    q')
                  (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  q')
                (fun _x_1 =>
                  DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                  (Equiv.{u + 1, u + 1}
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      q')
                    (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    q')
                  (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@Equiv.instEquivLike.{u + 1, u + 1}
                    (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u) CategoryTheory.types.{u}
                      (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      q')
                    (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q' z w
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u} C B x b z w
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  q')
                (@CategoryTheory.Functor.map.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  q q' α h)))
          n
          (@Eq.symm.{1} Nat n
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            h_1)
          h)
      (@Eq.refl.{1} Nat n)

theorem DaggerAmalgamSuccessor.evaluationNN._proof_1 :
  ∀ (C B : DaggerModels.SimplicialCat.{u_1, u_1}) (x : C.Obj) (b z w : B.Obj) (n : Nat)
    ⦃q q' : Opposite.{1} SimplexCategory⦄
    (α :
      @Quiver.Hom.{1, 0} (Opposite.{1} SimplexCategory)
        (@CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)))
        q q'),
    @Eq.{u_1 + 1}
      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q →
        @CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q')
      (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
        (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
          CategoryTheory.types.{u_1})
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q')
        (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q q' α)
        fun h =>
        @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
          (DaggerAmalgamPresentation.free.{u_1} C B x b)
          (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
          (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
          (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
          (DaggerAmalgamPaddedClassification.decodeNN.{u_1} C B x b q' z w n
            (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
              (Equiv.{u_1 + 1, u_1 + 1}
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n))
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
              (fun _x_1 => DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n)
              (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                  (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n)
                (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                  (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n)))
              (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z w n q') h)))
      (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
        (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
          CategoryTheory.types.{u_1})
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q')
        (fun h =>
          @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
            (DaggerAmalgamPaddedClassification.decodeNN.{u_1} C B x b q z w n
              (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                  (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                (fun _x_1 => DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                    (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                  (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                  (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                    (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)))
                (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z w n q) h)))
        (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q q' α)) :=
  fun C B x b z w n ⦃q q'⦄ α =>
    @funext.{u_1 + 1, u_1 + 1}
      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
          SimplexCategory.smallCategory)
        (Type u_1) CategoryTheory.types.{u_1}
        (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
      (fun _x_1 =>
        @CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q')
      (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
        (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
          CategoryTheory.types.{u_1})
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q')
        (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q q' α)
        fun h =>
        @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
          (DaggerAmalgamPresentation.free.{u_1} C B x b)
          (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
          (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
          (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
          (DaggerAmalgamPaddedClassification.decodeNN.{u_1} C B x b q' z w n
            (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
              (Equiv.{u_1 + 1, u_1 + 1}
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n))
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
              (fun _x_1 => DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n)
              (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                  (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n)
                (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                  (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n)))
              (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z w n q') h)))
      (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
        (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
          CategoryTheory.types.{u_1})
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q')
        (fun h =>
          @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
            (DaggerAmalgamPaddedClassification.decodeNN.{u_1} C B x b q z w n
              (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                  (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                (fun _x_1 => DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                    (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                  (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                  (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                    (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)))
                (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z w n q) h)))
        (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q q' α))
      fun h =>
      @id.{0}
        (@Eq.{u_1 + 1}
          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u_1) CategoryTheory.types.{u_1}
            (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b)
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
            q')
          (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
            (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
              CategoryTheory.types.{u_1})
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
              q')
            (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q q' α)
            (fun h =>
              @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                (DaggerAmalgamPaddedClassification.decodeNN.{u_1} C B x b q' z w n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                      (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                        (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                      (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                        (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n)))
                    (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z w n q')
                    h)))
            h)
          (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
            (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
              CategoryTheory.types.{u_1})
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
              q)
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
              q')
            (fun h =>
              @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                (DaggerAmalgamPaddedClassification.decodeNN.{u_1} C B x b q z w n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                      (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                        (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                      (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                        (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)))
                    (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z w n q)
                    h)))
            (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
              q q' α)
            h))
        (@Eq.mpr.{0}
          (@Eq.{u_1 + 1}
            (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
            (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
              (DaggerAmalgamPaddedClassification.decodeNN.{u_1} C B x b q' z w n
                (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                    (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                  (fun _x_1 =>
                    DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n)
                  (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                      (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                    (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n)
                    (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                      (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n)))
                  (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z w n q')
                  (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q q' α h))))
            (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
              (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                CategoryTheory.types.{u_1})
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                q)
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                q')
              (fun h =>
                @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                  (DaggerAmalgamPaddedClassification.decodeNN.{u_1} C B x b q z w n
                    (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                        (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                      (fun _x_1 =>
                        DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                      (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                        (Equiv.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                          (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                        (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                        (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                          (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)))
                      (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z w n q)
                      h)))
              (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                q q' α)
              h))
          (@Eq.{u_1 + 1}
            (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
            (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
              (DaggerAmalgamPaddedClassification.decodeNN.{u_1} C B x b q' z w n
                (@DaggerAmalgamRawNaturality.mapNN.{u_1} C B x b q q' α z w n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                      (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                        (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                      (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                        (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)))
                    (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z w n q)
                    h))))
            (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
              (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                CategoryTheory.types.{u_1})
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                q)
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                q')
              (fun h =>
                @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                  (DaggerAmalgamPaddedClassification.decodeNN.{u_1} C B x b q z w n
                    (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                        (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                      (fun _x_1 =>
                        DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                      (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                        (Equiv.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                          (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                        (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                        (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                          (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)))
                      (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z w n q)
                      h)))
              (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                q q' α)
              h))
          (@id.{0}
            (@Eq.{1} Prop
              (@Eq.{u_1 + 1}
                (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                  (DaggerAmalgamPaddedClassification.decodeNN.{u_1} C B x b q' z w n
                    (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                        (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                      (fun _x_1 =>
                        DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n)
                      (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                        (Equiv.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                          (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n))
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                        (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n)
                        (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                          (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n)))
                      (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z w n
                        q')
                      (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q q' α
                        h))))
                (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
                  (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                    CategoryTheory.types.{u_1})
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                    q)
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                    q')
                  (fun h =>
                    @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                      (DaggerAmalgamPaddedClassification.decodeNN.{u_1} C B x b q z w n
                        (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                          (Equiv.{u_1 + 1, u_1 + 1}
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                            (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                          (fun _x_1 =>
                            DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                          (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                            (Equiv.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                              (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w
                                n))
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                            (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                            (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                              (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w
                                n)))
                          (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z w
                            n q)
                          h)))
                  (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                    q q' α)
                  h))
              (@Eq.{u_1 + 1}
                (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                  (DaggerAmalgamPaddedClassification.decodeNN.{u_1} C B x b q' z w n
                    (@DaggerAmalgamRawNaturality.mapNN.{u_1} C B x b q q' α z w n
                      (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                        (Equiv.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                          (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                        (fun _x_1 =>
                          DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                        (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                          (Equiv.{u_1 + 1, u_1 + 1}
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                            (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                          (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                          (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                            (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w
                              n)))
                        (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z w n
                          q)
                        h))))
                (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
                  (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                    CategoryTheory.types.{u_1})
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                    q)
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                    q')
                  (fun h =>
                    @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                      (DaggerAmalgamPaddedClassification.decodeNN.{u_1} C B x b q z w n
                        (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                          (Equiv.{u_1 + 1, u_1 + 1}
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                            (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                          (fun _x_1 =>
                            DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                          (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                            (Equiv.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                              (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w
                                n))
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                            (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                            (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                              (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w
                                n)))
                          (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z w
                            n q)
                          h)))
                  (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                    q q' α)
                  h)))
            (@congrArg.{u_1 + 1, 1}
              (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n) Prop
              (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                  (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                (fun _x_1 => DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n)
                (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                    (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                  (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n)
                  (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q')
                    (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q' z w n)))
                (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z w n q')
                (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q q' α h))
              (@DaggerAmalgamRawNaturality.mapNN.{u_1} C B x b q q' α z w n
                (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                    (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                  (fun _x_1 => DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                  (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                      (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                    (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                    (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                      (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)))
                  (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z w n q) h))
              (fun _a =>
                @Eq.{u_1 + 1}
                  (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
                    (DaggerAmalgamPresentation.free.{u_1} C B x b)
                    (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                    (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                    (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                  (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                    (DaggerAmalgamPresentation.free.{u_1} C B x b)
                    (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                    (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                    (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                    (DaggerAmalgamPaddedClassification.decodeNN.{u_1} C B x b q' z w n _a))
                  (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
                    (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                      CategoryTheory.types.{u_1})
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                        (DaggerAmalgamPresentation.free.{u_1} C B x b)
                        (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                        (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                        (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                      q)
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                        (DaggerAmalgamPresentation.free.{u_1} C B x b)
                        (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                        (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                        (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                      q')
                    (fun h =>
                      @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                        (DaggerAmalgamPresentation.free.{u_1} C B x b)
                        (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                        (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                        (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                        (DaggerAmalgamPaddedClassification.decodeNN.{u_1} C B x b q z w n
                          (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                            (Equiv.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                              (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w
                                n))
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                            (fun _x_1 =>
                              DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                            (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                              (Equiv.{u_1 + 1, u_1 + 1}
                                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                  (Opposite.{1} SimplexCategory)
                                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                    SimplexCategory.smallCategory)
                                  (Type u_1) CategoryTheory.types.{u_1}
                                  (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n)
                                  q)
                                (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w
                                  n))
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                              (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w
                                n)
                              (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                  (Opposite.{1} SimplexCategory)
                                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                    SimplexCategory.smallCategory)
                                  (Type u_1) CategoryTheory.types.{u_1}
                                  (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n)
                                  q)
                                (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w
                                  n)))
                            (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z
                              w n q)
                            h)))
                    (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                        (DaggerAmalgamPresentation.free.{u_1} C B x b)
                        (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                        (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                        (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                      q q' α)
                    h))
              (@DaggerAmalgamSuccessor.familyNN_degreeEquiv_map.{u_1} C B x b z w n q q' α
                h)))
          (@Eq.symm.{u_1 + 1}
            (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
            (@DaggerModels.SimplicialCat.HomQuotient.map.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q q' α
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
              (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                (DaggerAmalgamPaddedClassification.decodeNN.{u_1} C B x b q z w n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                      (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                        (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                      (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                        (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)))
                    (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z w n q)
                    h))))
            (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
              (DaggerAmalgamPaddedClassification.decodeNN.{u_1} C B x b q' z w n
                (@DaggerAmalgamRawNaturality.mapNN.{u_1} C B x b q q' α z w n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                      (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                        (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                      (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                        (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)))
                    (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z w n q)
                    h))))
            (@DaggerAmalgamRawNaturality.map_mk_decodeNN.{u_1} C B x b q q' α z w n
              (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                  (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                (fun _x_1 => DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                    (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                  (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)
                  (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNN.{u_1} C B x b z w n) q)
                    (DaggerAmalgamPaddedClassification.RawNN.{u_1} C B x b q z w n)))
                (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u_1} C B x b z w n q) h))))

theorem DaggerAmalgamSuccessor.evaluationOO._proof_1 :
  ∀ (C B : DaggerModels.SimplicialCat.{u_1, u_1}) (x : C.Obj) (b : B.Obj) (a d : C.Obj)
    (n : Nat) ⦃q q' : Opposite.{1} SimplexCategory⦄
    (α :
      @Quiver.Hom.{1, 0} (Opposite.{1} SimplexCategory)
        (@CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)))
        q q'),
    @Eq.{u_1 + 1}
      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q →
        @CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q')
      (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
        (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
          CategoryTheory.types.{u_1})
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q')
        (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q q' α)
        fun h =>
        @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
          (DaggerAmalgamPresentation.free.{u_1} C B x b)
          (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
          (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
          (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
          (DaggerAmalgamPaddedClassification.decodeOO.{u_1} C B x b q' a d n
            (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
              (Equiv.{u_1 + 1, u_1 + 1}
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n))
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
              (fun _x_1 => DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n)
              (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                  (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n)
                (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                  (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n)))
              (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a d n q') h)))
      (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
        (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
          CategoryTheory.types.{u_1})
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q')
        (fun h =>
          @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
            (DaggerAmalgamPaddedClassification.decodeOO.{u_1} C B x b q a d n
              (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                  (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                (fun _x_1 => DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                    (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                  (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                  (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                    (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)))
                (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a d n q) h)))
        (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q q' α)) :=
  fun C B x b a d n ⦃q q'⦄ α =>
    @funext.{u_1 + 1, u_1 + 1}
      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
          SimplexCategory.smallCategory)
        (Type u_1) CategoryTheory.types.{u_1}
        (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
      (fun _x_1 =>
        @CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q')
      (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
        (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
          CategoryTheory.types.{u_1})
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q')
        (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q q' α)
        fun h =>
        @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
          (DaggerAmalgamPresentation.free.{u_1} C B x b)
          (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
          (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
          (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
          (DaggerAmalgamPaddedClassification.decodeOO.{u_1} C B x b q' a d n
            (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
              (Equiv.{u_1 + 1, u_1 + 1}
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n))
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
              (fun _x_1 => DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n)
              (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                  (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n)
                (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                  (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n)))
              (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a d n q') h)))
      (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
        (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
          CategoryTheory.types.{u_1})
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q')
        (fun h =>
          @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
            (DaggerAmalgamPaddedClassification.decodeOO.{u_1} C B x b q a d n
              (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                  (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                (fun _x_1 => DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                    (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                  (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                  (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                    (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)))
                (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a d n q) h)))
        (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q q' α))
      fun h =>
      @id.{0}
        (@Eq.{u_1 + 1}
          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u_1) CategoryTheory.types.{u_1}
            (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b)
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
            q')
          (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
            (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
              CategoryTheory.types.{u_1})
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
              q')
            (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q q' α)
            (fun h =>
              @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                (DaggerAmalgamPaddedClassification.decodeOO.{u_1} C B x b q' a d n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                      (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                        (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                      (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                        (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n)))
                    (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a d n q')
                    h)))
            h)
          (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
            (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
              CategoryTheory.types.{u_1})
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
              q)
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
              q')
            (fun h =>
              @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                (DaggerAmalgamPaddedClassification.decodeOO.{u_1} C B x b q a d n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                      (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                        (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                      (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                        (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)))
                    (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a d n q)
                    h)))
            (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
              q q' α)
            h))
        (@Eq.mpr.{0}
          (@Eq.{u_1 + 1}
            (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
            (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
              (DaggerAmalgamPaddedClassification.decodeOO.{u_1} C B x b q' a d n
                (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                    (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                  (fun _x_1 =>
                    DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n)
                  (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                      (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                    (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n)
                    (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                      (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n)))
                  (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a d n q')
                  (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q q' α h))))
            (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
              (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                CategoryTheory.types.{u_1})
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                q)
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                q')
              (fun h =>
                @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                  (DaggerAmalgamPaddedClassification.decodeOO.{u_1} C B x b q a d n
                    (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                        (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                      (fun _x_1 =>
                        DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                      (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                        (Equiv.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                          (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                        (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                        (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                          (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)))
                      (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a d n q)
                      h)))
              (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                q q' α)
              h))
          (@Eq.{u_1 + 1}
            (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
            (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
              (DaggerAmalgamPaddedClassification.decodeOO.{u_1} C B x b q' a d n
                (@DaggerAmalgamRawNaturality.mapOO.{u_1} C B x b q q' α a d n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                      (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                        (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                      (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                        (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)))
                    (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a d n q)
                    h))))
            (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
              (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                CategoryTheory.types.{u_1})
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                q)
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                q')
              (fun h =>
                @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                  (DaggerAmalgamPaddedClassification.decodeOO.{u_1} C B x b q a d n
                    (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                        (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                      (fun _x_1 =>
                        DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                      (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                        (Equiv.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                          (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                        (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                        (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                          (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)))
                      (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a d n q)
                      h)))
              (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                q q' α)
              h))
          (@id.{0}
            (@Eq.{1} Prop
              (@Eq.{u_1 + 1}
                (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                  (DaggerAmalgamPaddedClassification.decodeOO.{u_1} C B x b q' a d n
                    (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                        (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                      (fun _x_1 =>
                        DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n)
                      (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                        (Equiv.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                          (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n))
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                        (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n)
                        (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                          (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n)))
                      (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a d n
                        q')
                      (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q q' α
                        h))))
                (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
                  (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                    CategoryTheory.types.{u_1})
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                    q)
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                    q')
                  (fun h =>
                    @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                      (DaggerAmalgamPaddedClassification.decodeOO.{u_1} C B x b q a d n
                        (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                          (Equiv.{u_1 + 1, u_1 + 1}
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                            (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                          (fun _x_1 =>
                            DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                          (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                            (Equiv.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                              (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d
                                n))
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                            (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                            (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                              (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d
                                n)))
                          (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a d
                            n q)
                          h)))
                  (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                    q q' α)
                  h))
              (@Eq.{u_1 + 1}
                (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                  (DaggerAmalgamPaddedClassification.decodeOO.{u_1} C B x b q' a d n
                    (@DaggerAmalgamRawNaturality.mapOO.{u_1} C B x b q q' α a d n
                      (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                        (Equiv.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                          (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                        (fun _x_1 =>
                          DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                        (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                          (Equiv.{u_1 + 1, u_1 + 1}
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                            (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                          (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                          (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                            (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d
                              n)))
                        (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a d n
                          q)
                        h))))
                (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
                  (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                    CategoryTheory.types.{u_1})
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                    q)
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                    q')
                  (fun h =>
                    @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                      (DaggerAmalgamPaddedClassification.decodeOO.{u_1} C B x b q a d n
                        (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                          (Equiv.{u_1 + 1, u_1 + 1}
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                            (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                          (fun _x_1 =>
                            DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                          (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                            (Equiv.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                              (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d
                                n))
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                            (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                            (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                              (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d
                                n)))
                          (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a d
                            n q)
                          h)))
                  (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                    q q' α)
                  h)))
            (@congrArg.{u_1 + 1, 1}
              (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n) Prop
              (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                  (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                (fun _x_1 => DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n)
                (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                    (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                  (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n)
                  (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q')
                    (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q' a d n)))
                (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a d n q')
                (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q q' α h))
              (@DaggerAmalgamRawNaturality.mapOO.{u_1} C B x b q q' α a d n
                (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                    (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                  (fun _x_1 => DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                  (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                      (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                    (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                    (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                      (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)))
                  (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a d n q) h))
              (fun _a =>
                @Eq.{u_1 + 1}
                  (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
                    (DaggerAmalgamPresentation.free.{u_1} C B x b)
                    (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                    (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                    (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                  (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                    (DaggerAmalgamPresentation.free.{u_1} C B x b)
                    (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                    (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                    (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                    (DaggerAmalgamPaddedClassification.decodeOO.{u_1} C B x b q' a d n _a))
                  (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
                    (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                      CategoryTheory.types.{u_1})
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                        (DaggerAmalgamPresentation.free.{u_1} C B x b)
                        (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                        (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                        (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                      q)
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                        (DaggerAmalgamPresentation.free.{u_1} C B x b)
                        (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                        (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                        (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                      q')
                    (fun h =>
                      @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                        (DaggerAmalgamPresentation.free.{u_1} C B x b)
                        (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                        (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                        (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                        (DaggerAmalgamPaddedClassification.decodeOO.{u_1} C B x b q a d n
                          (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                            (Equiv.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                              (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d
                                n))
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                            (fun _x_1 =>
                              DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                            (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                              (Equiv.{u_1 + 1, u_1 + 1}
                                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                  (Opposite.{1} SimplexCategory)
                                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                    SimplexCategory.smallCategory)
                                  (Type u_1) CategoryTheory.types.{u_1}
                                  (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n)
                                  q)
                                (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d
                                  n))
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                              (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d
                                n)
                              (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                  (Opposite.{1} SimplexCategory)
                                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                    SimplexCategory.smallCategory)
                                  (Type u_1) CategoryTheory.types.{u_1}
                                  (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n)
                                  q)
                                (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d
                                  n)))
                            (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a
                              d n q)
                            h)))
                    (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                        (DaggerAmalgamPresentation.free.{u_1} C B x b)
                        (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                        (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                        (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                      q q' α)
                    h))
              (@DaggerAmalgamSuccessor.familyOO_degreeEquiv_map.{u_1} C B x b a d n q q' α
                h)))
          (@Eq.symm.{u_1 + 1}
            (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
            (@DaggerModels.SimplicialCat.HomQuotient.map.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q q' α
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
              (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                (DaggerAmalgamPaddedClassification.decodeOO.{u_1} C B x b q a d n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                      (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                        (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                      (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                        (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)))
                    (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a d n q)
                    h))))
            (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
              (DaggerAmalgamPaddedClassification.decodeOO.{u_1} C B x b q' a d n
                (@DaggerAmalgamRawNaturality.mapOO.{u_1} C B x b q q' α a d n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                      (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                        (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                      (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                        (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)))
                    (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a d n q)
                    h))))
            (@DaggerAmalgamRawNaturality.map_mk_decodeOO.{u_1} C B x b q q' α a d n
              (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                  (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                (fun _x_1 => DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                    (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                  (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)
                  (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyOO.{u_1} C B x b a d n) q)
                    (DaggerAmalgamPaddedClassification.RawOO.{u_1} C B x b q a d n)))
                (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u_1} C B x b a d n q) h))))

def DaggerAmalgamSuccessor.evaluationOO :
  (C B : DaggerModels.SimplicialCat.{u, u}) →
    (x : C.Obj) →
      (b : B.Obj) →
        (a d : C.Obj) →
          (n : Nat) →
            @Quiver.Hom.{u + 1, u + 1} _root_.SSet.{u}
              (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1} _root_.SSet.{u}
                (@CategoryTheory.Category.toCategoryStruct.{u, u + 1} _root_.SSet.{u}
                  SSet.largeCategory.{u}))
              (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n)
              (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
                (DaggerAmalgamPresentation.free.{u} C B x b)
                (DaggerAmalgamPresentation.relations.{u} C B x b)
                (DaggerAmalgamPresentation.leftObj.{u} C B x b a)
                (DaggerAmalgamPresentation.leftObj.{u} C B x b d)) :=
  fun C B x b a d n =>
    @CategoryTheory.NatTrans.mk.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
        SimplexCategory.smallCategory)
      (Type u) CategoryTheory.types.{u}
      (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n)
      (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
        (DaggerAmalgamPresentation.free.{u} C B x b)
        (DaggerAmalgamPresentation.relations.{u} C B x b)
        (DaggerAmalgamPresentation.leftObj.{u} C B x b a)
        (DaggerAmalgamPresentation.leftObj.{u} C B x b d))
      (fun q h =>
        @DaggerModels.SimplicialCat.HomQuotient.mk.{u, u}
          (DaggerAmalgamPresentation.free.{u} C B x b)
          (DaggerAmalgamPresentation.relations.{u} C B x b) q
          (DaggerAmalgamPresentation.leftObj.{u} C B x b a)
          (DaggerAmalgamPresentation.leftObj.{u} C B x b d)
          (DaggerAmalgamPaddedClassification.decodeOO.{u} C B x b q a d n
            (@DFunLike.coe.{u + 1, u + 1, u + 1}
              (Equiv.{u + 1, u + 1}
                (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
                (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n))
              (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u) CategoryTheory.types.{u}
                (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
              (fun _x_1 => DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n)
              (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                (Equiv.{u + 1, u + 1}
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
                  (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n))
                (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
                (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n)
                (@Equiv.instEquivLike.{u + 1, u + 1}
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d n) q)
                  (DaggerAmalgamPaddedClassification.RawOO.{u} C B x b q a d n)))
              (DaggerAmalgamUnitBoundary.familyOO_degreeEquiv.{u} C B x b a d n q) h)))
      (DaggerAmalgamSuccessor.evaluationOO._proof_1.{u} C B x b a d n)

theorem DaggerAmalgamSuccessor.evaluationOO_zero :
  ∀ (C B : DaggerModels.SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj) (a d : C.Obj),
    @Eq.{u + 1}
      (@Quiver.Hom.{u + 1, u + 1} _root_.SSet.{u}
        (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1} _root_.SSet.{u}
          (@CategoryTheory.Category.toCategoryStruct.{u, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u}))
        (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
          (DaggerAmalgamPresentation.free.{u} C B x b)
          (DaggerAmalgamPresentation.relations.{u} C B x b)
          (DaggerAmalgamPresentation.leftObj.{u} C B x b a)
          (DaggerAmalgamPresentation.leftObj.{u} C B x b d)))
      (DaggerAmalgamSuccessor.evaluationOO.{u} C B x b a d
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@CategoryTheory.EnrichedFunctor.map.{u, u + 1, u, u} _root_.SSet.{u}
        SSet.largeCategory.{u}
        (@CategoryTheory.SemiCartesianMonoidalCategory.toMonoidalCategory.{u, u + 1}
          _root_.SSet.{u} SSet.largeCategory.{u}
          (@CategoryTheory.CartesianMonoidalCategory.toSemiCartesianMonoidalCategory.{u,
                u + 1}
            _root_.SSet.{u} SSet.largeCategory.{u} SSet.instCartesianMonoidalCategory.{u}))
        C.Obj C.enriched (DaggerAmalgamPresentation.Q.{u} C B x b).Obj
        (DaggerAmalgamPresentation.Q.{u} C B x b).enriched
        (DaggerAmalgamPresentation.leftLeg.{u} C B x b) a d) :=
  fun C B x b a d =>
    @SSet.hom_ext.{u}
      (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
        (DaggerAmalgamPresentation.free.{u} C B x b)
        (DaggerAmalgamPresentation.relations.{u} C B x b)
        (DaggerAmalgamPresentation.leftObj.{u} C B x b a)
        (DaggerAmalgamPresentation.leftObj.{u} C B x b d))
      (DaggerAmalgamSuccessor.evaluationOO.{u} C B x b a d
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@CategoryTheory.EnrichedFunctor.map.{u, u + 1, u, u} _root_.SSet.{u}
        SSet.largeCategory.{u}
        (@CategoryTheory.SemiCartesianMonoidalCategory.toMonoidalCategory.{u, u + 1}
          _root_.SSet.{u} SSet.largeCategory.{u}
          (@CategoryTheory.CartesianMonoidalCategory.toSemiCartesianMonoidalCategory.{u,
                u + 1}
            _root_.SSet.{u} SSet.largeCategory.{u} SSet.instCartesianMonoidalCategory.{u}))
        C.Obj C.enriched (DaggerAmalgamPresentation.Q.{u} C B x b).Obj
        (DaggerAmalgamPresentation.Q.{u} C B x b).enriched
        (DaggerAmalgamPresentation.leftLeg.{u} C B x b) a d)
      fun q =>
      @CategoryTheory.types_ext.{u}
        (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          q)
        (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
            (DaggerAmalgamPresentation.free.{u} C B x b)
            (DaggerAmalgamPresentation.relations.{u} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u} C B x b a)
            (DaggerAmalgamPresentation.leftObj.{u} C B x b d))
          q)
        (@CategoryTheory.NatTrans.app.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
            (DaggerAmalgamPresentation.free.{u} C B x b)
            (DaggerAmalgamPresentation.relations.{u} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u} C B x b a)
            (DaggerAmalgamPresentation.leftObj.{u} C B x b d))
          (DaggerAmalgamSuccessor.evaluationOO.{u} C B x b a d
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          q)
        (@CategoryTheory.NatTrans.app.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
            (DaggerAmalgamPresentation.free.{u} C B x b)
            (DaggerAmalgamPresentation.relations.{u} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u} C B x b a)
            (DaggerAmalgamPresentation.leftObj.{u} C B x b d))
          (@CategoryTheory.EnrichedFunctor.map.{u, u + 1, u, u} _root_.SSet.{u}
            SSet.largeCategory.{u}
            (@CategoryTheory.SemiCartesianMonoidalCategory.toMonoidalCategory.{u, u + 1}
              _root_.SSet.{u} SSet.largeCategory.{u}
              (@CategoryTheory.CartesianMonoidalCategory.toSemiCartesianMonoidalCategory.{u,
                    u + 1}
                _root_.SSet.{u} SSet.largeCategory.{u}
                SSet.instCartesianMonoidalCategory.{u}))
            C.Obj C.enriched (DaggerAmalgamPresentation.Q.{u} C B x b).Obj
            (DaggerAmalgamPresentation.Q.{u} C B x b).enriched
            (DaggerAmalgamPresentation.leftLeg.{u} C B x b) a d)
          q)
        fun h =>
        @Eq.refl.{u + 1}
          (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
              (DaggerAmalgamPresentation.free.{u} C B x b)
              (DaggerAmalgamPresentation.relations.{u} C B x b)
              (DaggerAmalgamPresentation.leftObj.{u} C B x b a)
              (DaggerAmalgamPresentation.leftObj.{u} C B x b d))
            q)
          (@CategoryTheory.NatTrans.app.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (DaggerAmalgamUnitBoundary.familyOO.{u} C B x b a d
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
              (DaggerAmalgamPresentation.free.{u} C B x b)
              (DaggerAmalgamPresentation.relations.{u} C B x b)
              (DaggerAmalgamPresentation.leftObj.{u} C B x b a)
              (DaggerAmalgamPresentation.leftObj.{u} C B x b d))
            (DaggerAmalgamSuccessor.evaluationOO.{u} C B x b a d
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            q h)

def DaggerAmalgamSuccessor.evaluationNN :
  (C B : DaggerModels.SimplicialCat.{u, u}) →
    (x : C.Obj) →
      (b z w : B.Obj) →
        (n : Nat) →
          @Quiver.Hom.{u + 1, u + 1} _root_.SSet.{u}
            (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1} _root_.SSet.{u}
              (@CategoryTheory.Category.toCategoryStruct.{u, u + 1} _root_.SSet.{u}
                SSet.largeCategory.{u}))
            (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n)
            (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
              (DaggerAmalgamPresentation.free.{u} C B x b)
              (DaggerAmalgamPresentation.relations.{u} C B x b)
              (DaggerAmalgamPresentation.rightObj.{u} C B x b z)
              (DaggerAmalgamPresentation.rightObj.{u} C B x b w)) :=
  fun C B x b z w n =>
    @CategoryTheory.NatTrans.mk.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
        SimplexCategory.smallCategory)
      (Type u) CategoryTheory.types.{u}
      (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n)
      (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
        (DaggerAmalgamPresentation.free.{u} C B x b)
        (DaggerAmalgamPresentation.relations.{u} C B x b)
        (DaggerAmalgamPresentation.rightObj.{u} C B x b z)
        (DaggerAmalgamPresentation.rightObj.{u} C B x b w))
      (fun q h =>
        @DaggerModels.SimplicialCat.HomQuotient.mk.{u, u}
          (DaggerAmalgamPresentation.free.{u} C B x b)
          (DaggerAmalgamPresentation.relations.{u} C B x b) q
          (DaggerAmalgamPresentation.rightObj.{u} C B x b z)
          (DaggerAmalgamPresentation.rightObj.{u} C B x b w)
          (DaggerAmalgamPaddedClassification.decodeNN.{u} C B x b q z w n
            (@DFunLike.coe.{u + 1, u + 1, u + 1}
              (Equiv.{u + 1, u + 1}
                (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
                (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n))
              (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u) CategoryTheory.types.{u}
                (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
              (fun _x_1 => DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n)
              (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                (Equiv.{u + 1, u + 1}
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
                  (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n))
                (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
                (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n)
                (@Equiv.instEquivLike.{u + 1, u + 1}
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w n) q)
                  (DaggerAmalgamPaddedClassification.RawNN.{u} C B x b q z w n)))
              (DaggerAmalgamUnitBoundary.familyNN_degreeEquiv.{u} C B x b z w n q) h)))
      (DaggerAmalgamSuccessor.evaluationNN._proof_1.{u} C B x b z w n)

theorem DaggerAmalgamSuccessor.evaluationNN_zero :
  ∀ (C B : DaggerModels.SimplicialCat.{u, u}) (x : C.Obj) (b z w : B.Obj),
    @Eq.{u + 1}
      (@Quiver.Hom.{u + 1, u + 1} _root_.SSet.{u}
        (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1} _root_.SSet.{u}
          (@CategoryTheory.Category.toCategoryStruct.{u, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u}))
        (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
          (DaggerAmalgamPresentation.free.{u} C B x b)
          (DaggerAmalgamPresentation.relations.{u} C B x b)
          (DaggerAmalgamPresentation.rightObj.{u} C B x b z)
          (DaggerAmalgamPresentation.rightObj.{u} C B x b w)))
      (DaggerAmalgamSuccessor.evaluationNN.{u} C B x b z w
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@CategoryTheory.EnrichedFunctor.map.{u, u + 1, u, u} _root_.SSet.{u}
        SSet.largeCategory.{u}
        (@CategoryTheory.SemiCartesianMonoidalCategory.toMonoidalCategory.{u, u + 1}
          _root_.SSet.{u} SSet.largeCategory.{u}
          (@CategoryTheory.CartesianMonoidalCategory.toSemiCartesianMonoidalCategory.{u,
                u + 1}
            _root_.SSet.{u} SSet.largeCategory.{u} SSet.instCartesianMonoidalCategory.{u}))
        B.Obj B.enriched (DaggerAmalgamPresentation.Q.{u} C B x b).Obj
        (DaggerAmalgamPresentation.Q.{u} C B x b).enriched
        (DaggerAmalgamPresentation.rightLeg.{u} C B x b) z w) :=
  fun C B x b z w =>
    @SSet.hom_ext.{u}
      (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
        (DaggerAmalgamPresentation.free.{u} C B x b)
        (DaggerAmalgamPresentation.relations.{u} C B x b)
        (DaggerAmalgamPresentation.rightObj.{u} C B x b z)
        (DaggerAmalgamPresentation.rightObj.{u} C B x b w))
      (DaggerAmalgamSuccessor.evaluationNN.{u} C B x b z w
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@CategoryTheory.EnrichedFunctor.map.{u, u + 1, u, u} _root_.SSet.{u}
        SSet.largeCategory.{u}
        (@CategoryTheory.SemiCartesianMonoidalCategory.toMonoidalCategory.{u, u + 1}
          _root_.SSet.{u} SSet.largeCategory.{u}
          (@CategoryTheory.CartesianMonoidalCategory.toSemiCartesianMonoidalCategory.{u,
                u + 1}
            _root_.SSet.{u} SSet.largeCategory.{u} SSet.instCartesianMonoidalCategory.{u}))
        B.Obj B.enriched (DaggerAmalgamPresentation.Q.{u} C B x b).Obj
        (DaggerAmalgamPresentation.Q.{u} C B x b).enriched
        (DaggerAmalgamPresentation.rightLeg.{u} C B x b) z w)
      fun q =>
      @CategoryTheory.types_ext.{u}
        (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          q)
        (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
            (DaggerAmalgamPresentation.free.{u} C B x b)
            (DaggerAmalgamPresentation.relations.{u} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u} C B x b z)
            (DaggerAmalgamPresentation.rightObj.{u} C B x b w))
          q)
        (@CategoryTheory.NatTrans.app.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
            (DaggerAmalgamPresentation.free.{u} C B x b)
            (DaggerAmalgamPresentation.relations.{u} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u} C B x b z)
            (DaggerAmalgamPresentation.rightObj.{u} C B x b w))
          (DaggerAmalgamSuccessor.evaluationNN.{u} C B x b z w
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          q)
        (@CategoryTheory.NatTrans.app.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
            (DaggerAmalgamPresentation.free.{u} C B x b)
            (DaggerAmalgamPresentation.relations.{u} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u} C B x b z)
            (DaggerAmalgamPresentation.rightObj.{u} C B x b w))
          (@CategoryTheory.EnrichedFunctor.map.{u, u + 1, u, u} _root_.SSet.{u}
            SSet.largeCategory.{u}
            (@CategoryTheory.SemiCartesianMonoidalCategory.toMonoidalCategory.{u, u + 1}
              _root_.SSet.{u} SSet.largeCategory.{u}
              (@CategoryTheory.CartesianMonoidalCategory.toSemiCartesianMonoidalCategory.{u,
                    u + 1}
                _root_.SSet.{u} SSet.largeCategory.{u}
                SSet.instCartesianMonoidalCategory.{u}))
            B.Obj B.enriched (DaggerAmalgamPresentation.Q.{u} C B x b).Obj
            (DaggerAmalgamPresentation.Q.{u} C B x b).enriched
            (DaggerAmalgamPresentation.rightLeg.{u} C B x b) z w)
          q)
        fun h =>
        @Eq.refl.{u + 1}
          (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
              (DaggerAmalgamPresentation.free.{u} C B x b)
              (DaggerAmalgamPresentation.relations.{u} C B x b)
              (DaggerAmalgamPresentation.rightObj.{u} C B x b z)
              (DaggerAmalgamPresentation.rightObj.{u} C B x b w))
            q)
          (@CategoryTheory.NatTrans.app.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (DaggerAmalgamUnitBoundary.familyNN.{u} C B x b z w
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
              (DaggerAmalgamPresentation.free.{u} C B x b)
              (DaggerAmalgamPresentation.relations.{u} C B x b)
              (DaggerAmalgamPresentation.rightObj.{u} C B x b z)
              (DaggerAmalgamPresentation.rightObj.{u} C B x b w))
            (DaggerAmalgamSuccessor.evaluationNN.{u} C B x b z w
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            q h)

theorem DaggerAmalgamSuccessor.evaluationNO._proof_1 :
  ∀ (C B : DaggerModels.SimplicialCat.{u_1, u_1}) (x : C.Obj) (b z : B.Obj) (d : C.Obj)
    (n : Nat) ⦃q q' : Opposite.{1} SimplexCategory⦄
    (α :
      @Quiver.Hom.{1, 0} (Opposite.{1} SimplexCategory)
        (@CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)))
        q q'),
    @Eq.{u_1 + 1}
      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q →
        @CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q')
      (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
        (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
          CategoryTheory.types.{u_1})
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q')
        (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q q' α)
        fun h =>
        @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
          (DaggerAmalgamPresentation.free.{u_1} C B x b)
          (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
          (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
          (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
          (DaggerAmalgamPaddedClassification.decodeNO.{u_1} C B x b q' z d n
            (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
              (Equiv.{u_1 + 1, u_1 + 1}
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n))
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
              (fun _x_1 => DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n)
              (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                  (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n)
                (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                  (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n)))
              (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z d n q') h)))
      (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
        (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
          CategoryTheory.types.{u_1})
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q')
        (fun h =>
          @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
            (DaggerAmalgamPaddedClassification.decodeNO.{u_1} C B x b q z d n
              (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                  (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                (fun _x_1 => DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                    (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                  (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                  (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                    (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)))
                (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z d n q) h)))
        (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q q' α)) :=
  fun C B x b z d n ⦃q q'⦄ α =>
    @funext.{u_1 + 1, u_1 + 1}
      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
          SimplexCategory.smallCategory)
        (Type u_1) CategoryTheory.types.{u_1}
        (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
      (fun _x_1 =>
        @CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q')
      (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
        (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
          CategoryTheory.types.{u_1})
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q')
        (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q q' α)
        fun h =>
        @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
          (DaggerAmalgamPresentation.free.{u_1} C B x b)
          (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
          (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
          (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
          (DaggerAmalgamPaddedClassification.decodeNO.{u_1} C B x b q' z d n
            (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
              (Equiv.{u_1 + 1, u_1 + 1}
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n))
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
              (fun _x_1 => DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n)
              (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                  (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n)
                (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                  (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n)))
              (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z d n q') h)))
      (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
        (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
          CategoryTheory.types.{u_1})
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q')
        (fun h =>
          @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
            (DaggerAmalgamPaddedClassification.decodeNO.{u_1} C B x b q z d n
              (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                  (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                (fun _x_1 => DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                    (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                  (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                  (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                    (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)))
                (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z d n q) h)))
        (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
          q q' α))
      fun h =>
      @id.{0}
        (@Eq.{u_1 + 1}
          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u_1) CategoryTheory.types.{u_1}
            (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b)
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
            q')
          (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
            (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
              CategoryTheory.types.{u_1})
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
              q')
            (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q q' α)
            (fun h =>
              @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                (DaggerAmalgamPaddedClassification.decodeNO.{u_1} C B x b q' z d n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                      (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                        (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                      (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                        (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n)))
                    (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z d n q')
                    h)))
            h)
          (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
            (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
              CategoryTheory.types.{u_1})
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
              q)
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
              q')
            (fun h =>
              @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                (DaggerAmalgamPaddedClassification.decodeNO.{u_1} C B x b q z d n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                      (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                        (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                      (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                        (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)))
                    (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z d n q)
                    h)))
            (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
              q q' α)
            h))
        (@Eq.mpr.{0}
          (@Eq.{u_1 + 1}
            (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
            (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
              (DaggerAmalgamPaddedClassification.decodeNO.{u_1} C B x b q' z d n
                (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                    (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                  (fun _x_1 =>
                    DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n)
                  (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                      (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                    (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n)
                    (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                      (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n)))
                  (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z d n q')
                  (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q q' α h))))
            (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
              (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                CategoryTheory.types.{u_1})
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                q)
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                q')
              (fun h =>
                @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                  (DaggerAmalgamPaddedClassification.decodeNO.{u_1} C B x b q z d n
                    (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                        (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                      (fun _x_1 =>
                        DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                      (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                        (Equiv.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                          (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                        (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                        (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                          (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)))
                      (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z d n q)
                      h)))
              (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                q q' α)
              h))
          (@Eq.{u_1 + 1}
            (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
            (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
              (DaggerAmalgamPaddedClassification.decodeNO.{u_1} C B x b q' z d n
                (@DaggerAmalgamRawNaturality.mapNO.{u_1} C B x b q q' α z d n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                      (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                        (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                      (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                        (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)))
                    (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z d n q)
                    h))))
            (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
              (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                CategoryTheory.types.{u_1})
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                q)
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                q')
              (fun h =>
                @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                  (DaggerAmalgamPaddedClassification.decodeNO.{u_1} C B x b q z d n
                    (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                        (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                      (fun _x_1 =>
                        DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                      (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                        (Equiv.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                          (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                        (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                        (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                          (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)))
                      (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z d n q)
                      h)))
              (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                q q' α)
              h))
          (@id.{0}
            (@Eq.{1} Prop
              (@Eq.{u_1 + 1}
                (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                  (DaggerAmalgamPaddedClassification.decodeNO.{u_1} C B x b q' z d n
                    (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                        (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                      (fun _x_1 =>
                        DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n)
                      (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                        (Equiv.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                          (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n))
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                        (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n)
                        (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                          (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n)))
                      (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z d n
                        q')
                      (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q q' α
                        h))))
                (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
                  (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                    CategoryTheory.types.{u_1})
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                    q)
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                    q')
                  (fun h =>
                    @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                      (DaggerAmalgamPaddedClassification.decodeNO.{u_1} C B x b q z d n
                        (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                          (Equiv.{u_1 + 1, u_1 + 1}
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                            (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                          (fun _x_1 =>
                            DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                          (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                            (Equiv.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                              (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d
                                n))
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                            (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                            (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                              (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d
                                n)))
                          (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z d
                            n q)
                          h)))
                  (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                    q q' α)
                  h))
              (@Eq.{u_1 + 1}
                (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                  (DaggerAmalgamPaddedClassification.decodeNO.{u_1} C B x b q' z d n
                    (@DaggerAmalgamRawNaturality.mapNO.{u_1} C B x b q q' α z d n
                      (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                        (Equiv.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                          (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                        (fun _x_1 =>
                          DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                        (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                          (Equiv.{u_1 + 1, u_1 + 1}
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                            (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                          (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                          (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                            (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d
                              n)))
                        (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z d n
                          q)
                        h))))
                (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
                  (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                    CategoryTheory.types.{u_1})
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                    q)
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                    q')
                  (fun h =>
                    @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                      (DaggerAmalgamPaddedClassification.decodeNO.{u_1} C B x b q z d n
                        (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                          (Equiv.{u_1 + 1, u_1 + 1}
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                            (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                          (fun _x_1 =>
                            DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                          (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                            (Equiv.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                              (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d
                                n))
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                            (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                            (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                              (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d
                                n)))
                          (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z d
                            n q)
                          h)))
                  (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                    q q' α)
                  h)))
            (@congrArg.{u_1 + 1, 1}
              (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n) Prop
              (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                  (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                (fun _x_1 => DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n)
                (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                    (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                  (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n)
                  (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q')
                    (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q' z d n)))
                (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z d n q')
                (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q q' α h))
              (@DaggerAmalgamRawNaturality.mapNO.{u_1} C B x b q q' α z d n
                (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                    (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                  (fun _x_1 => DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                  (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                      (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                    (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                    (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                      (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)))
                  (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z d n q) h))
              (fun _a =>
                @Eq.{u_1 + 1}
                  (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
                    (DaggerAmalgamPresentation.free.{u_1} C B x b)
                    (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                    (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                    (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                  (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                    (DaggerAmalgamPresentation.free.{u_1} C B x b)
                    (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                    (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                    (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                    (DaggerAmalgamPaddedClassification.decodeNO.{u_1} C B x b q' z d n _a))
                  (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
                    (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                      CategoryTheory.types.{u_1})
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                        (DaggerAmalgamPresentation.free.{u_1} C B x b)
                        (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                        (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                        (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                      q)
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                        (DaggerAmalgamPresentation.free.{u_1} C B x b)
                        (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                        (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                        (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                      q')
                    (fun h =>
                      @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                        (DaggerAmalgamPresentation.free.{u_1} C B x b)
                        (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                        (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                        (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                        (DaggerAmalgamPaddedClassification.decodeNO.{u_1} C B x b q z d n
                          (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                            (Equiv.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                              (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d
                                n))
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                            (fun _x_1 =>
                              DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                            (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                              (Equiv.{u_1 + 1, u_1 + 1}
                                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                  (Opposite.{1} SimplexCategory)
                                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                    SimplexCategory.smallCategory)
                                  (Type u_1) CategoryTheory.types.{u_1}
                                  (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n)
                                  q)
                                (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d
                                  n))
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                              (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d
                                n)
                              (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                  (Opposite.{1} SimplexCategory)
                                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                    SimplexCategory.smallCategory)
                                  (Type u_1) CategoryTheory.types.{u_1}
                                  (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n)
                                  q)
                                (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d
                                  n)))
                            (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z
                              d n q)
                            h)))
                    (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                        (DaggerAmalgamPresentation.free.{u_1} C B x b)
                        (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                        (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                        (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
                      q q' α)
                    h))
              (@DaggerAmalgamSuccessor.familyNO_degreeEquiv_map.{u_1} C B x b z d n q q' α
                h)))
          (@Eq.symm.{u_1 + 1}
            (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d))
            (@DaggerModels.SimplicialCat.HomQuotient.map.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q q' α
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
              (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
                (DaggerAmalgamPaddedClassification.decodeNO.{u_1} C B x b q z d n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                      (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                        (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                      (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                        (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)))
                    (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z d n q)
                    h))))
            (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b z)
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b d)
              (DaggerAmalgamPaddedClassification.decodeNO.{u_1} C B x b q' z d n
                (@DaggerAmalgamRawNaturality.mapNO.{u_1} C B x b q q' α z d n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                      (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                        (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                      (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                        (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)))
                    (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z d n q)
                    h))))
            (@DaggerAmalgamRawNaturality.map_mk_decodeNO.{u_1} C B x b q q' α z d n
              (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                  (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                (fun _x_1 => DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                    (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                  (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)
                  (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyNO.{u_1} C B x b z d n) q)
                    (DaggerAmalgamPaddedClassification.RawNO.{u_1} C B x b q z d n)))
                (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u_1} C B x b z d n q) h))))

def DaggerAmalgamSuccessor.evaluationNO :
  (C B : DaggerModels.SimplicialCat.{u, u}) →
    (x : C.Obj) →
      (b z : B.Obj) →
        (d : C.Obj) →
          (n : Nat) →
            @Quiver.Hom.{u + 1, u + 1} _root_.SSet.{u}
              (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1} _root_.SSet.{u}
                (@CategoryTheory.Category.toCategoryStruct.{u, u + 1} _root_.SSet.{u}
                  SSet.largeCategory.{u}))
              (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n)
              (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
                (DaggerAmalgamPresentation.free.{u} C B x b)
                (DaggerAmalgamPresentation.relations.{u} C B x b)
                (DaggerAmalgamPresentation.rightObj.{u} C B x b z)
                (DaggerAmalgamPresentation.leftObj.{u} C B x b d)) :=
  fun C B x b z d n =>
    @CategoryTheory.NatTrans.mk.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
        SimplexCategory.smallCategory)
      (Type u) CategoryTheory.types.{u}
      (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n)
      (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
        (DaggerAmalgamPresentation.free.{u} C B x b)
        (DaggerAmalgamPresentation.relations.{u} C B x b)
        (DaggerAmalgamPresentation.rightObj.{u} C B x b z)
        (DaggerAmalgamPresentation.leftObj.{u} C B x b d))
      (fun q h =>
        @DaggerModels.SimplicialCat.HomQuotient.mk.{u, u}
          (DaggerAmalgamPresentation.free.{u} C B x b)
          (DaggerAmalgamPresentation.relations.{u} C B x b) q
          (DaggerAmalgamPresentation.rightObj.{u} C B x b z)
          (DaggerAmalgamPresentation.leftObj.{u} C B x b d)
          (DaggerAmalgamPaddedClassification.decodeNO.{u} C B x b q z d n
            (@DFunLike.coe.{u + 1, u + 1, u + 1}
              (Equiv.{u + 1, u + 1}
                (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q)
                (DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q z d n))
              (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u) CategoryTheory.types.{u}
                (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q)
              (fun _x_1 => DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q z d n)
              (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                (Equiv.{u + 1, u + 1}
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q)
                  (DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q z d n))
                (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q)
                (DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q z d n)
                (@Equiv.instEquivLike.{u + 1, u + 1}
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyNO.{u} C B x b z d n) q)
                  (DaggerAmalgamPaddedClassification.RawNO.{u} C B x b q z d n)))
              (DaggerAmalgamUnitBoundary.familyNO_degreeEquiv.{u} C B x b z d n q) h)))
      (DaggerAmalgamSuccessor.evaluationNO._proof_1.{u} C B x b z d n)

theorem DaggerAmalgamSuccessor.familyON_degreeEquiv_map :
  ∀ (C B : DaggerModels.SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj) (a : C.Obj)
    (w : B.Obj) (n : Nat) {q q' : Opposite.{1} SimplexCategory}
    (α :
      @Quiver.Hom.{1, 0} (Opposite.{1} SimplexCategory)
        (@Quiver.opposite.{0, 1} SimplexCategory
          (@CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory
            (@CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)))
        q q')
    (h :
      @CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
          SimplexCategory.smallCategory)
        (Type u) CategoryTheory.types.{u}
        (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q),
    @Eq.{u + 1} (DaggerAmalgamPaddedClassification.RawON.{u} C B x b q' a w n)
      (@DFunLike.coe.{u + 1, u + 1, u + 1}
        (Equiv.{u + 1, u + 1}
          (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q')
          (DaggerAmalgamPaddedClassification.RawON.{u} C B x b q' a w n))
        (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q')
        (fun _x_1 => DaggerAmalgamPaddedClassification.RawON.{u} C B x b q' a w n)
        (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
          (Equiv.{u + 1, u + 1}
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q')
            (DaggerAmalgamPaddedClassification.RawON.{u} C B x b q' a w n))
          (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q')
          (DaggerAmalgamPaddedClassification.RawON.{u} C B x b q' a w n)
          (@Equiv.instEquivLike.{u + 1, u + 1}
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q')
            (DaggerAmalgamPaddedClassification.RawON.{u} C B x b q' a w n)))
        (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u} C B x b a w n q')
        (@CategoryTheory.Functor.map.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q q' α h))
      (@DaggerAmalgamRawNaturality.mapON.{u} C B x b q q' α a w n
        (@DFunLike.coe.{u + 1, u + 1, u + 1}
          (Equiv.{u + 1, u + 1}
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q)
            (DaggerAmalgamPaddedClassification.RawON.{u} C B x b q a w n))
          (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q)
          (fun _x_1 => DaggerAmalgamPaddedClassification.RawON.{u} C B x b q a w n)
          (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
            (Equiv.{u + 1, u + 1}
              (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u) CategoryTheory.types.{u}
                (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q)
              (DaggerAmalgamPaddedClassification.RawON.{u} C B x b q a w n))
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q)
            (DaggerAmalgamPaddedClassification.RawON.{u} C B x b q a w n)
            (@Equiv.instEquivLike.{u + 1, u + 1}
              (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u) CategoryTheory.types.{u}
                (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q)
              (DaggerAmalgamPaddedClassification.RawON.{u} C B x b q a w n)))
          (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u} C B x b a w n q) h)) :=
  fun C B x b a w n {q q'} α h =>
    @rfl.{u + 1} (DaggerAmalgamPaddedClassification.RawON.{u} C B x b q' a w n)
      (@DFunLike.coe.{u + 1, u + 1, u + 1}
        (Equiv.{u + 1, u + 1}
          (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q')
          (DaggerAmalgamPaddedClassification.RawON.{u} C B x b q' a w n))
        (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q')
        (fun _x_1 => DaggerAmalgamPaddedClassification.RawON.{u} C B x b q' a w n)
        (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
          (Equiv.{u + 1, u + 1}
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q')
            (DaggerAmalgamPaddedClassification.RawON.{u} C B x b q' a w n))
          (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u) CategoryTheory.types.{u}
            (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q')
          (DaggerAmalgamPaddedClassification.RawON.{u} C B x b q' a w n)
          (@Equiv.instEquivLike.{u + 1, u + 1}
            (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u) CategoryTheory.types.{u}
              (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q')
            (DaggerAmalgamPaddedClassification.RawON.{u} C B x b q' a w n)))
        (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u} C B x b a w n q')
        (@CategoryTheory.Functor.map.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u) CategoryTheory.types.{u}
          (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q q' α h))

theorem DaggerAmalgamSuccessor.evaluationON._proof_1 :
  ∀ (C B : DaggerModels.SimplicialCat.{u_1, u_1}) (x : C.Obj) (b : B.Obj) (a : C.Obj)
    (w : B.Obj) (n : Nat) ⦃q q' : Opposite.{1} SimplexCategory⦄
    (α :
      @Quiver.Hom.{1, 0} (Opposite.{1} SimplexCategory)
        (@CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)))
        q q'),
    @Eq.{u_1 + 1}
      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q →
        @CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q')
      (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
        (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
          CategoryTheory.types.{u_1})
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q')
        (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q q' α)
        fun h =>
        @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
          (DaggerAmalgamPresentation.free.{u_1} C B x b)
          (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
          (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
          (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
          (DaggerAmalgamPaddedClassification.decodeON.{u_1} C B x b q' a w n
            (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
              (Equiv.{u_1 + 1, u_1 + 1}
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n))
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
              (fun _x_1 => DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n)
              (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                  (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n)
                (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                  (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n)))
              (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a w n q') h)))
      (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
        (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
          CategoryTheory.types.{u_1})
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q')
        (fun h =>
          @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
            (DaggerAmalgamPaddedClassification.decodeON.{u_1} C B x b q a w n
              (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                  (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                (fun _x_1 => DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                    (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                  (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                  (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                    (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)))
                (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a w n q) h)))
        (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q q' α)) :=
  fun C B x b a w n ⦃q q'⦄ α =>
    @funext.{u_1 + 1, u_1 + 1}
      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
          SimplexCategory.smallCategory)
        (Type u_1) CategoryTheory.types.{u_1}
        (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
      (fun _x_1 =>
        @CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q')
      (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
        (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
          CategoryTheory.types.{u_1})
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q')
        (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q q' α)
        fun h =>
        @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
          (DaggerAmalgamPresentation.free.{u_1} C B x b)
          (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
          (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
          (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
          (DaggerAmalgamPaddedClassification.decodeON.{u_1} C B x b q' a w n
            (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
              (Equiv.{u_1 + 1, u_1 + 1}
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n))
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
              (fun _x_1 => DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n)
              (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                  (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n)
                (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                  (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n)))
              (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a w n q') h)))
      (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
        (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
          CategoryTheory.types.{u_1})
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q)
        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q')
        (fun h =>
          @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
            (DaggerAmalgamPaddedClassification.decodeON.{u_1} C B x b q a w n
              (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                  (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                (fun _x_1 => DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                    (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                  (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                  (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                    (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)))
                (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a w n q) h)))
        (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          (Type u_1) CategoryTheory.types.{u_1}
          (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
            (DaggerAmalgamPresentation.free.{u_1} C B x b)
            (DaggerAmalgamPresentation.relations.{u_1} C B x b)
            (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
            (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
          q q' α))
      fun h =>
      @id.{0}
        (@Eq.{u_1 + 1}
          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            (Type u_1) CategoryTheory.types.{u_1}
            (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b)
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
            q')
          (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
            (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
              CategoryTheory.types.{u_1})
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
              q')
            (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q q' α)
            (fun h =>
              @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                (DaggerAmalgamPaddedClassification.decodeON.{u_1} C B x b q' a w n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                      (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                        (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                      (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                        (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n)))
                    (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a w n q')
                    h)))
            h)
          (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
            (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
              CategoryTheory.types.{u_1})
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
              q)
            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
              q')
            (fun h =>
              @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                (DaggerAmalgamPaddedClassification.decodeON.{u_1} C B x b q a w n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                      (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                        (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                      (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                        (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)))
                    (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a w n q)
                    h)))
            (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              (Type u_1) CategoryTheory.types.{u_1}
              (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
              q q' α)
            h))
        (@Eq.mpr.{0}
          (@Eq.{u_1 + 1}
            (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
            (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
              (DaggerAmalgamPaddedClassification.decodeON.{u_1} C B x b q' a w n
                (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                    (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                  (fun _x_1 =>
                    DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n)
                  (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                      (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                    (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n)
                    (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                      (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n)))
                  (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a w n q')
                  (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q q' α h))))
            (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
              (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                CategoryTheory.types.{u_1})
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                q)
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                q')
              (fun h =>
                @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                  (DaggerAmalgamPaddedClassification.decodeON.{u_1} C B x b q a w n
                    (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                        (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                      (fun _x_1 =>
                        DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                      (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                        (Equiv.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                          (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                        (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                        (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                          (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)))
                      (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a w n q)
                      h)))
              (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                q q' α)
              h))
          (@Eq.{u_1 + 1}
            (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
            (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
              (DaggerAmalgamPaddedClassification.decodeON.{u_1} C B x b q' a w n
                (@DaggerAmalgamRawNaturality.mapON.{u_1} C B x b q q' α a w n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                      (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                        (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                      (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                        (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)))
                    (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a w n q)
                    h))))
            (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
              (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                CategoryTheory.types.{u_1})
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                q)
              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                q')
              (fun h =>
                @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                  (DaggerAmalgamPaddedClassification.decodeON.{u_1} C B x b q a w n
                    (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                        (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                      (fun _x_1 =>
                        DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                      (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                        (Equiv.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                          (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                        (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                        (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                          (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)))
                      (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a w n q)
                      h)))
              (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u_1) CategoryTheory.types.{u_1}
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                q q' α)
              h))
          (@id.{0}
            (@Eq.{1} Prop
              (@Eq.{u_1 + 1}
                (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                  (DaggerAmalgamPaddedClassification.decodeON.{u_1} C B x b q' a w n
                    (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                        (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                      (fun _x_1 =>
                        DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n)
                      (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                        (Equiv.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                          (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n))
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                        (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n)
                        (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                          (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n)))
                      (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a w n
                        q')
                      (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q q' α
                        h))))
                (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
                  (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                    CategoryTheory.types.{u_1})
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                    q)
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                    q')
                  (fun h =>
                    @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                      (DaggerAmalgamPaddedClassification.decodeON.{u_1} C B x b q a w n
                        (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                          (Equiv.{u_1 + 1, u_1 + 1}
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                            (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                          (fun _x_1 =>
                            DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                          (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                            (Equiv.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                              (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w
                                n))
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                            (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                            (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                              (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w
                                n)))
                          (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a w
                            n q)
                          h)))
                  (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                    q q' α)
                  h))
              (@Eq.{u_1 + 1}
                (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                  (DaggerAmalgamPresentation.free.{u_1} C B x b)
                  (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                  (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                  (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                  (DaggerAmalgamPaddedClassification.decodeON.{u_1} C B x b q' a w n
                    (@DaggerAmalgamRawNaturality.mapON.{u_1} C B x b q q' α a w n
                      (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                        (Equiv.{u_1 + 1, u_1 + 1}
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                          (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                        (fun _x_1 =>
                          DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                        (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                          (Equiv.{u_1 + 1, u_1 + 1}
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                            (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                          (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                          (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                            (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w
                              n)))
                        (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a w n
                          q)
                        h))))
                (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
                  (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                    CategoryTheory.types.{u_1})
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                    q)
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                    q')
                  (fun h =>
                    @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                      (DaggerAmalgamPaddedClassification.decodeON.{u_1} C B x b q a w n
                        (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                          (Equiv.{u_1 + 1, u_1 + 1}
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                            (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                          (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                            (Opposite.{1} SimplexCategory)
                            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                              SimplexCategory.smallCategory)
                            (Type u_1) CategoryTheory.types.{u_1}
                            (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                          (fun _x_1 =>
                            DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                          (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                            (Equiv.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                              (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w
                                n))
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                            (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                            (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                              (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w
                                n)))
                          (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a w
                            n q)
                          h)))
                  (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                      (DaggerAmalgamPresentation.free.{u_1} C B x b)
                      (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                      (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                      (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                    q q' α)
                  h)))
            (@congrArg.{u_1 + 1, 1}
              (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n) Prop
              (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                  (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                (fun _x_1 => DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n)
                (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                    (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                  (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n)
                  (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q')
                    (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q' a w n)))
                (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a w n q')
                (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q q' α h))
              (@DaggerAmalgamRawNaturality.mapON.{u_1} C B x b q q' α a w n
                (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                    (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                  (fun _x_1 => DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                  (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                      (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                    (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                    (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                      (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)))
                  (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a w n q) h))
              (fun _a =>
                @Eq.{u_1 + 1}
                  (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
                    (DaggerAmalgamPresentation.free.{u_1} C B x b)
                    (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                    (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                    (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                  (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                    (DaggerAmalgamPresentation.free.{u_1} C B x b)
                    (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
                    (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                    (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                    (DaggerAmalgamPaddedClassification.decodeON.{u_1} C B x b q' a w n _a))
                  (@CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (Type u_1)
                    (@CategoryTheory.Category.toCategoryStruct.{u_1, u_1 + 1} (Type u_1)
                      CategoryTheory.types.{u_1})
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                        (DaggerAmalgamPresentation.free.{u_1} C B x b)
                        (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                        (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                        (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                      q)
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                        (DaggerAmalgamPresentation.free.{u_1} C B x b)
                        (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                        (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                        (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                      q')
                    (fun h =>
                      @DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                        (DaggerAmalgamPresentation.free.{u_1} C B x b)
                        (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                        (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                        (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                        (DaggerAmalgamPaddedClassification.decodeON.{u_1} C B x b q a w n
                          (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                            (Equiv.{u_1 + 1, u_1 + 1}
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                              (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w
                                n))
                            (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                              (Opposite.{1} SimplexCategory)
                              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                SimplexCategory.smallCategory)
                              (Type u_1) CategoryTheory.types.{u_1}
                              (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                            (fun _x_1 =>
                              DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                            (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                              (Equiv.{u_1 + 1, u_1 + 1}
                                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                  (Opposite.{1} SimplexCategory)
                                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                    SimplexCategory.smallCategory)
                                  (Type u_1) CategoryTheory.types.{u_1}
                                  (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n)
                                  q)
                                (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w
                                  n))
                              (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                (Opposite.{1} SimplexCategory)
                                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                  SimplexCategory.smallCategory)
                                (Type u_1) CategoryTheory.types.{u_1}
                                (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                              (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w
                                n)
                              (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                                  (Opposite.{1} SimplexCategory)
                                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                                    SimplexCategory.smallCategory)
                                  (Type u_1) CategoryTheory.types.{u_1}
                                  (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n)
                                  q)
                                (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w
                                  n)))
                            (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a
                              w n q)
                            h)))
                    (@CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (@DaggerModels.SimplicialCat.HomQuotient.hom.{u_1, u_1}
                        (DaggerAmalgamPresentation.free.{u_1} C B x b)
                        (DaggerAmalgamPresentation.relations.{u_1} C B x b)
                        (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                        (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
                      q q' α)
                    h))
              (@DaggerAmalgamSuccessor.familyON_degreeEquiv_map.{u_1} C B x b a w n q q' α
                h)))
          (@Eq.symm.{u_1 + 1}
            (@DaggerModels.SimplicialCat.HomQuotient.HomObj.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w))
            (@DaggerModels.SimplicialCat.HomQuotient.map.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q q' α
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
              (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
                (DaggerAmalgamPresentation.free.{u_1} C B x b)
                (DaggerAmalgamPresentation.relations.{u_1} C B x b) q
                (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
                (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
                (DaggerAmalgamPaddedClassification.decodeON.{u_1} C B x b q a w n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                      (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                        (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                      (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                        (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)))
                    (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a w n q)
                    h))))
            (@DaggerModels.SimplicialCat.HomQuotient.mk.{u_1, u_1}
              (DaggerAmalgamPresentation.free.{u_1} C B x b)
              (DaggerAmalgamPresentation.relations.{u_1} C B x b) q'
              (DaggerAmalgamPresentation.leftObj.{u_1} C B x b a)
              (DaggerAmalgamPresentation.rightObj.{u_1} C B x b w)
              (DaggerAmalgamPaddedClassification.decodeON.{u_1} C B x b q' a w n
                (@DaggerAmalgamRawNaturality.mapON.{u_1} C B x b q q' α a w n
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (Equiv.{u_1 + 1, u_1 + 1}
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                      (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                    (fun _x_1 =>
                      DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                    (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                      (Equiv.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                        (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                      (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                        (Opposite.{1} SimplexCategory)
                        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                          SimplexCategory.smallCategory)
                        (Type u_1) CategoryTheory.types.{u_1}
                        (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                      (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                      (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                        (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                          (Opposite.{1} SimplexCategory)
                          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                            SimplexCategory.smallCategory)
                          (Type u_1) CategoryTheory.types.{u_1}
                          (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                        (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)))
                    (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a w n q)
                    h))))
            (@DaggerAmalgamRawNaturality.map_mk_decodeON.{u_1} C B x b q q' α a w n
              (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
                (Equiv.{u_1 + 1, u_1 + 1}
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                  (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u_1) CategoryTheory.types.{u_1}
                  (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                (fun _x_1 => DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (Equiv.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                    (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n))
                  (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u_1) CategoryTheory.types.{u_1}
                    (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                  (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)
                  (@Equiv.instEquivLike.{u_1 + 1, u_1 + 1}
                    (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
                      (Opposite.{1} SimplexCategory)
                      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                        SimplexCategory.smallCategory)
                      (Type u_1) CategoryTheory.types.{u_1}
                      (DaggerAmalgamUnitBoundary.familyON.{u_1} C B x b a w n) q)
                    (DaggerAmalgamPaddedClassification.RawON.{u_1} C B x b q a w n)))
                (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u_1} C B x b a w n q) h))))

def DaggerAmalgamSuccessor.evaluationON :
  (C B : DaggerModels.SimplicialCat.{u, u}) →
    (x : C.Obj) →
      (b : B.Obj) →
        (a : C.Obj) →
          (w : B.Obj) →
            (n : Nat) →
              @Quiver.Hom.{u + 1, u + 1} _root_.SSet.{u}
                (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1} _root_.SSet.{u}
                  (@CategoryTheory.Category.toCategoryStruct.{u, u + 1} _root_.SSet.{u}
                    SSet.largeCategory.{u}))
                (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n)
                (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
                  (DaggerAmalgamPresentation.free.{u} C B x b)
                  (DaggerAmalgamPresentation.relations.{u} C B x b)
                  (DaggerAmalgamPresentation.leftObj.{u} C B x b a)
                  (DaggerAmalgamPresentation.rightObj.{u} C B x b w)) :=
  fun C B x b a w n =>
    @CategoryTheory.NatTrans.mk.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
      (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
        SimplexCategory.smallCategory)
      (Type u) CategoryTheory.types.{u}
      (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n)
      (@DaggerModels.SimplicialCat.HomQuotient.hom.{u, u}
        (DaggerAmalgamPresentation.free.{u} C B x b)
        (DaggerAmalgamPresentation.relations.{u} C B x b)
        (DaggerAmalgamPresentation.leftObj.{u} C B x b a)
        (DaggerAmalgamPresentation.rightObj.{u} C B x b w))
      (fun q h =>
        @DaggerModels.SimplicialCat.HomQuotient.mk.{u, u}
          (DaggerAmalgamPresentation.free.{u} C B x b)
          (DaggerAmalgamPresentation.relations.{u} C B x b) q
          (DaggerAmalgamPresentation.leftObj.{u} C B x b a)
          (DaggerAmalgamPresentation.rightObj.{u} C B x b w)
          (DaggerAmalgamPaddedClassification.decodeON.{u} C B x b q a w n
            (@DFunLike.coe.{u + 1, u + 1, u + 1}
              (Equiv.{u + 1, u + 1}
                (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q)
                (DaggerAmalgamPaddedClassification.RawON.{u} C B x b q a w n))
              (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                (Type u) CategoryTheory.types.{u}
                (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q)
              (fun _x_1 => DaggerAmalgamPaddedClassification.RawON.{u} C B x b q a w n)
              (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
                (Equiv.{u + 1, u + 1}
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q)
                  (DaggerAmalgamPaddedClassification.RawON.{u} C B x b q a w n))
                (@CategoryTheory.Functor.obj.{0, u, 0, u + 1} (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  (Type u) CategoryTheory.types.{u}
                  (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q)
                (DaggerAmalgamPaddedClassification.RawON.{u} C B x b q a w n)
                (@Equiv.instEquivLike.{u + 1, u + 1}
                  (@CategoryTheory.Functor.obj.{0, u, 0, u + 1}
                    (Opposite.{1} SimplexCategory)
                    (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                      SimplexCategory.smallCategory)
                    (Type u) CategoryTheory.types.{u}
                    (DaggerAmalgamUnitBoundary.familyON.{u} C B x b a w n) q)
                  (DaggerAmalgamPaddedClassification.RawON.{u} C B x b q a w n)))
              (DaggerAmalgamUnitBoundary.familyON_degreeEquiv.{u} C B x b a w n q) h)))
      (DaggerAmalgamSuccessor.evaluationON._proof_1.{u} C B x b a w n)

