
Require Import  Utils Algebra.SetoidCat Algebra.Monoid Algebra.Monad Algebra.SetoidUtils Algebra.SetoidCat.PairUtils Algebra.Functor Algebra.Applicative.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Open Scope type_scope.

Section Arr_Monoid.
  Context
    {A B : Type}
    {SA : Setoid A}
    {SB : Setoid B}
    {B_Monoid : @Monoid _ SB}.

  Definition arr_mempty : SA ~> SB := constS SA @ mempty.

  Definition arr_mappend : (SA ~~> SB) ~> (SA ~~> SB) ~~> (SA ~~> SB) :=
    comp3S @ pairingF @ (uncurryS @ mappend).

  Instance arr_Monoid : @Monoid _ (SA ~~> SB).
  Proof.
    exists (arr_mempty) (arr_mappend).
    intros. simpl. arrequiv. apply left_unit_monoid.
    intros. simpl. arrequiv. apply right_unit_monoid.
    intros. simpl. arrequiv. apply associativity_monoid.
  Defined.
End Arr_Monoid.




