Require Import Algebra.Utils Algebra.SetoidCat Algebra.SetoidCat.PairUtils Algebra.Monad Algebra.Monoid Algebra.Traversable Algebra.FoldableFunctor Algebra.Functor SetoidUtils Algebra.Applicative Algebra.Alternative Tactics Algebra.SetoidCat.BoolUtils Algebra.Functor.Utils Algebra.SetoidCat.ListUtils Algebra.Monoid.Alternative Algebra.Alternative.List.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import Coq.Lists.List.

Import ListNotations.



Section Generic.
  Context
    {m mS}
    {mnd : @Monad m mS}.



  Definition l A {AS : Setoid A} := list A.
  Instance lS {A} (AS : Setoid A) : Setoid (l A) := listS AS.
  Existing Instance list_Alternative.

  Instance list_A_Monoid A AS : @Monoid (l A) (lS AS) := alternative_Monoid A AS.
  

End Generic.

