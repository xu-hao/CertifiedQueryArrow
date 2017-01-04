Require Import  Algebra.Utils Algebra.SetoidCat.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import Coq.Lists.List.

Open Scope type_scope.
Section Monoid.

  Context
    {A : Type}
    {SA : Setoid A}.

  Class Monoid : Type :=
    {
      mempty : A;
      mappend : SA ~> SA ~~> SA;
      left_unit_monoid: forall (a : A),
                       mappend @ mempty @ a == a;
      right_unit_monoid: forall (a : A),
                           mappend @ a @ mempty == a;
      associativity_monoid : forall (a b c : A),
                            mappend @ (mappend @ a @ b) @ c == mappend @ a @ (mappend @ b @ c)

    }.

End Monoid.

Class MonoidHomomorphism {A B: Type}
      {SA : Setoid A} {SB : Setoid B} {MA : @Monoid _ SA} {MB : @Monoid _ SB} (f : SA ~> SB) :=
  {
    monoid_homomorphism_mempty :  f @ mempty == mempty;
    monoid_homomorphism_mappend : forall a a2, f @ (mappend @ a @ a2) == mappend @ (f @ a) @ ( f @ a2)
  }.
