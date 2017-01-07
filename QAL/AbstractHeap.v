Require Import FSetInterface.
Require Import Tactics  Algebra.SetoidCat  Algebra.Monad Algebra.SetoidCat.PairUtils Algebra.SetoidCat.MaybeUtils Algebra.Monad.Maybe Algebra.Alternative Algebra.Functor Algebra.FoldableFunctor Algebra.Applicative Algebra.Monoid Algebra.SetoidCat.NatUtils Algebra.SetoidCat.BoolUtils Algebra.Monoid.PropUtils.

Require Import FMapWeakList  RelationClasses Relation_Definitions Morphisms SetoidClass.


Module Type AbstractHeap.
  Parameter t : Type.
  Parameter tS : Setoid t.
  Parameter l : forall A, (Setoid A) -> Type.
  Parameter lS : forall A (AS : Setoid A), Setoid (l A AS).
  Parameter l_Alternative : @Alternative l lS.
  Parameter l_Functor : @Functor l lS.
  Parameter l_Foldable : @FoldableFunctor l lS l_Functor.
  Parameter l_Applicative : @Applicative l lS l_Functor.

  Parameter isEmpty : tS ~> iff_setoid.
  Parameter disjoint : tS ~> tS ~~> iff_setoid.
  Parameter union : tS ~> tS ~~> tS.

  Notation "a ⊥ b" := (disjoint @ a @ b) (at level 15). 
  Notation "a ⋅ b" := (union @ a @ b) (at level 15). 
End AbstractHeap.  

