Require Import Algebra.SetoidCat.PairUtils Algebra.Utils Algebra.SetoidCat Algebra.Functor Algebra.Applicative Algebra.Monoid SetoidUtils Algebra.Alternative.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Section Instance.
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
End Instance.
