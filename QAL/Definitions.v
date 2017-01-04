Require Import FSetInterface.
Require Import Tactics Algebra.Utils SetoidUtils Algebra.SetoidCat  Algebra.Monad Algebra.SetoidCat.PairUtils Algebra.SetoidCat.MaybeUtils Algebra.Monad.Maybe Algebra.Alternative Algebra.Functor Algebra.FoldableFunctor Algebra.Applicative Algebra.Monoid Algebra.SetoidCat.NatUtils Algebra.SetoidCat.BoolUtils Algebra.Monoid.PropUtils.

Require Import FMapWeakList  RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import Coq.Structures.DecidableTypeEx.

Module FVarSet := FSetNat.

Module FValSet := FSetNat.

Definition var := nat.

Instance varS : Setoid var := natS.

Program Instance natSetSetoid : Setoid FSetNat.t :=
  {
    equiv := FSetNat.eq
  }.

Instance varSetS : Setoid FVarSet.t := natSetSetoid.


Module WSNotations (VT : WS).
  Notation "∅" := VT.empty.
  Notation "a ∩ b" := (VT.inter a b) (at level 11, left associativity).
  Notation "a ∪ b" := (VT.union a b) (at level 12, left associativity).
  Notation "﹛ a ﹜" := (VT.singleton a) (at level 10).
  Notation "a ∈ b" := (VT.In a b) (at level 15).
  Notation "a ∈? b" := (VT.mem a b) (at level 15).

End WSNotations.

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

Module Type ValType.
  Parameter val : Type.
  Parameter valS : Setoid val.
  Parameter storableS : valS ~> boolS.
  Parameter appVal : valS ~> valS ~~> maybeS valS.
  Axiom equiv_dec : forall val1 val2, {val1 == val2} + {~ val1 == val2}.
End ValType.


