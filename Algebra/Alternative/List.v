Require Import Algebra.Utils Algebra.SetoidCat Algebra.SetoidCat.PairUtils Algebra.Monad Algebra.Monoid Algebra.Traversable Algebra.FoldableFunctor Algebra.Functor Algebra.SetoidCat.SetoidUtils Algebra.Applicative Algebra.Alternative Tactics Algebra.SetoidCat.BoolUtils Algebra.Functor.Utils Algebra.Functor.Compose Algebra.Applicative.Compose Algebra.SetoidCat.ListUtils.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import Coq.Lists.List.

Import ListNotations.


Section Generic.
  Definition l A {AS : Setoid A} := list A.
  Instance lS {A} (AS : Setoid A) : Setoid (l A) := listS AS.



  Definition listEmpty {A} {AS : Setoid A} : l A := nil.
  Instance list_Alternative : @Alternative l (@lS).
  Proof.
    exists (@listEmpty) (@appS).
    intros. reflexivity.
    intros. induction a.
    reflexivity.
    simpl. constructor. reflexivity. auto.
    intros. induction a.
    reflexivity.
    simpl. constructor. reflexivity. auto.
  Defined.


End Generic.

