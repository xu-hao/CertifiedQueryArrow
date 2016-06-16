Require Import Algebra.SetoidCat.PairUtils Utils Algebra.SetoidCat Algebra.Functor Algebra.Applicative Algebra.Monoid SetoidUtils.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Section Alternative.
  Context
    {t : forall A, Setoid A -> Type}
    {tS : forall A (AS : Setoid A), Setoid (t A AS)}.

  Class Alternative : Type :=
    {
      empty : forall {A} {SA : Setoid A}, (t A _);
      append : forall {A} {AS : Setoid A}, tS _ AS ~> tS _ AS ~~> tS _ AS;
      left_unit_alt: forall A (SA : Setoid A)
                            (a : t A _),
                       append @ empty @ a == a;
      right_unit_alt: forall A (SA : Setoid A)
                             (a : t A _),
                        append @ a @ empty == a;
      associativity_alt : forall A (SA : Setoid A)
                                 (a b c : t A _),
                            append @ (append @ a @ b) @ c == append @ a @ (append @ b @ c)

    }.
End Alternative.

Notation "a <|> b" := (append @ a @ b) (at level 50, left associativity).

Section Instances.
  Context
    {t : forall A, Setoid A -> Type}
    {tS : forall A (AS : Setoid A), Setoid (t A AS)}
    {alt : @Alternative t tS}.
  Instance alternative_Monoid  A (AS : Setoid A) : @Monoid (t A _) (tS _ AS).
  Proof.
    exists (empty) (append).
    apply left_unit_alt.
    apply right_unit_alt.
    apply associativity_alt.
  Defined.
End Instances.


