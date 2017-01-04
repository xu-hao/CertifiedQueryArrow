Require Import   Algebra.SetoidCat Algebra.Monoid.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Section NearSemiRing.

  Context
    {A : Type}
    {SA : Setoid A}.

  Class NearSemiRing : Type :=
    {
      one : A;
      zero : A;
      times : SA ~> SA ~~> SA;
      plus : SA ~> SA ~~> SA;
      times_left_unit : forall a, times @ one @ a == a;
      times_right_unit : forall a, times @ a @ one == a;
      times_associativity : forall a b c, times @ (times @ a @ b) @ c == times @ a @ (times @ b @ c);
      plus_left_unit : forall a, plus @ zero @ a == a;
      plus_right_unit : forall a, plus @ a @ zero == a;
      plus_associativity : forall a b c, plus @ (plus @ a @ b) @ c == plus @ a @ (plus @ b @ c);
      times_left_absorb : forall a, times @ zero @ a == zero;
      times_left_distributivity : forall a b c, times @ (plus @ a @ b) @ c == plus @ (times @ a @ c) @ (times @ b @ c)
    }.

End NearSemiRing.

