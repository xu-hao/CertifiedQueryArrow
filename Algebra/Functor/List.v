Require Import  Algebra.SetoidCat Algebra.Monad Algebra.Monoid Algebra.Traversable Algebra.FoldableFunctor Algebra.Functor SetoidUtils Algebra.Applicative Algebra.Alternative Tactics Algebra.SetoidCat.BoolUtils Algebra.Functor.Utils Algebra.Functor.Compose Algebra.Applicative.Compose Algebra.SetoidCat.ListUtils.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import Coq.Lists.List.

Import ListNotations.



Section Generic.
  Definition l A {AS : Setoid A} := list A.
  Instance lS {A} (AS : Setoid A) : Setoid (l A) := listS AS.

  Instance listFunctor : @Functor l (@lS).
  Proof.
    exists (@mapS).
    intros. simpl. arrequiv. induction a.
    reflexivity.
    simpl. constructor. reflexivity. auto.
    intros. simpl. arrequiv. induction a.
    reflexivity.
    simpl. constructor. reflexivity. auto.
  Defined.

  

End Generic.

