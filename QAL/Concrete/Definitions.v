Require Import FSetInterface.
Require Import Tactics Algebra.Utils SetoidUtils Algebra.SetoidCat  Algebra.Monad Algebra.SetoidCat.PairUtils Algebra.SetoidCat.MaybeUtils Algebra.Monad.Maybe Algebra.Alternative Algebra.Functor Algebra.FoldableFunctor Algebra.Applicative Algebra.Monoid Algebra.SetoidCat.NatUtils Algebra.SetoidCat.BoolUtils Algebra.Monoid.PropUtils.

Require Import FMapWeakList  RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import Coq.Structures.DecidableTypeEx.

Module Type PredType.
  Parameter pred : Type.
  Parameter predS : Setoid pred.
End PredType.

Module Type AddrType.
  Parameter addr : Type.
  Parameter addrS : Setoid addr.
End AddrType.

Module Type TypeType.
  Parameter type : Type. 
  Parameter typeS : Setoid type.
End TypeType.



