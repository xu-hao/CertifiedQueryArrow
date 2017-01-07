Require Import FSetInterface.
Require Import Tactics Algebra.Utils SetoidUtils Algebra.SetoidCat  Algebra.Monad Algebra.SetoidCat.PairUtils Algebra.SetoidCat.MaybeUtils Algebra.Monad.Maybe Algebra.Alternative Algebra.Functor Algebra.FoldableFunctor Algebra.Applicative Algebra.Monoid Algebra.SetoidCat.NatUtils Algebra.SetoidCat.BoolUtils Algebra.Monoid.PropUtils QAL.Definitions.

Require Import FMapWeakList  RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import Coq.Structures.DecidableTypeEx.

Module Type AbstractStore (VT : ValType).
  Parameter t : Type.
  Parameter tS : Setoid t.
  Parameter update : varS ~> VT.valS ~~> tS ~~> tS.
  Notation "store [ var ↦ val ]s " := (update @ var @ val @ store) (at level 11).
End AbstractStore.

