Require Import Algebra.Utils Algebra.SetoidCat Algebra.SetoidCat.PairUtils Algebra.Monad Algebra.Monoid Algebra.Traversable Algebra.FoldableFunctor Algebra.Functor SetoidUtils Algebra.Applicative Algebra.Alternative Tactics Algebra.SetoidCat.BoolUtils Algebra.Functor.Utils Algebra.SetoidCat.ListUtils Algebra.Functor.List.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import Coq.Lists.List.

Import ListNotations.



Section Generic.


  Definition l A {AS : Setoid A} := list A.
  Instance lS {A} (AS : Setoid A) : Setoid (l A) := listS AS.

  Existing Instance listFunctor.

  
  Definition list_fold A (AS : Setoid A) (A_monoid : @Monoid A AS) := @fold_rightS A A AS AS @ mappend @ mempty.
  
  Instance list_Foldable : @FoldableFunctor l (@lS) _.
  Proof.
    exists (list_fold).
    intros. simpl. destruct hom. induction a.
    simpl.  auto.
    simpl.  rewrite monoid_homomorphism_mappend. evalproper. auto.
  Defined.



End Generic.

