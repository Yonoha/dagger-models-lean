/-!
Comparison roots for definitions not otherwise reached from theorem statements.
These reflexive statements are audit markers, not mathematical results of the
formalization. Comparator recursively compares the definitions occurring in
their types against the independently compiled reference environment.
This file is appended to both isolated modules; it is not part of the library.
-/

open CategoryTheory

namespace DaggerModels.ComparatorContracts

universe audit_u

theorem freeCofibration_definition {X Y : DaggerSSet.{audit_u}} (f : X ⟶ Y) :
    DaggerSSet.FreeCofibration f ↔ DaggerSSet.FreeCofibration f := Iff.rfl

theorem nonDegenerateEquiv_definition (X : DaggerSSet.{audit_u}) (n : ℕ) :
    X.nonDegenerateEquiv n = X.nonDegenerateEquiv n := rfl

theorem forget_definition : DaggerSSet.forget.{audit_u} = DaggerSSet.forget.{audit_u} := rfl

end DaggerModels.ComparatorContracts
