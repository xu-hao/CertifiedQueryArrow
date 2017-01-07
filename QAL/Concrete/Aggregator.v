Require Import QAL.Assert Algebra.Utils Algebra.Monad SetoidUtils Algebra.SetoidCat.ListUtils Algebra.SetoidCat Algebra.Monad.StoreHeap Algebra.Monad.ContT Algebra.NearSemiRing Algebra.Monoid Tactics Expr QAL.Definitions Algebra.FoldableFunctor Algebra.SetoidCat.PairUtils Algebra.Functor Algebra.Alternative Algebra.SetoidCat.MaybeUtils Algebra.Monad.Maybe Algebra.Applicative Algebra.SetoidCat.BoolUtils Algebra.SetoidCat.UnitUtils Algebra.Monoid.BoolUtils Algebra.Monoid.Alternative Algebra.Alternative.List Algebra.Functor.List Algebra.FoldableFunctor.List Algebra.Monad.Utils QAL.Command QAL.Definitions QAL.AbstractHeap QAL.AbstractStore.

Require Import Coq.Lists.List PeanoNat RelationClasses Relation_Definitions Morphisms Coq.Program.Basics SetoidClass.

Section Aggregator.
  Context
    {type : Type}
    {pred : Type}
    {builtInExpr : Type}
    {builtInCommand : Type}.

  Inductive qalAggregator :=
  | cExists : qalAggregator
  | cNot : qalAggregator
  .

  Program Instance qalAggregatorS : Setoid qalAggregator.

End Aggregator.

Module QALAggregator (VT : ValType)
       (S : AbstractStore VT) (H : AbstractHeap) : Aggregator VT S H.
  Open Scope type_scope.
  Module TS := Types VT S H.
  Module CA := CommandAux VT S H.
  Import VT S H TS CA.

  Definition aggregator := qalAggregator.
  Instance aggregatorS : Setoid aggregator := qalAggregatorS.
      
  Fixpoint _freeVarsAggregator (agg : aggregator) (fv : FVarSet.t) :=
    match agg with
      | cNot  => fv
      | cExists  => fv
    end
  .

  Instance _freeVarsAggregator_Proper : Proper (equiv ==> equiv ==> equiv) _freeVarsAggregator.
  Proof.
    unfold Proper, respectful. intros. simpl in H. rewrite H. destruct y.
    * simpl. auto.  
    * simpl. auto. 
  Qed.

  Definition freeVarsAggregator := injF2 _freeVarsAggregator _.

  

  Section NegationGeneric.
    Context
      (a : H.l S.t _).
    Definition negationGeneric : state unit := stopNotNull @ a.
  End NegationGeneric.
  Instance negationGeneric_Proper : Proper (equiv ==> equiv) negationGeneric.
  Proof.
    solve_properS negationGeneric.
  Qed.
  
  Section ExistentialQuantificationGeneric.
    Context
      (a : H.l S.t _).
    Definition existentialQuantificationGeneric : state unit :=
      stopNull @ a.
  End ExistentialQuantificationGeneric.
  Instance existentialQuantificationGeneric_Proper : Proper (equiv ==> equiv) existentialQuantificationGeneric.
  Proof.
    solve_properS existentialQuantificationGeneric.
  Qed.

  

Fixpoint _interpretAggregator (agg : aggregator) (a : H.l S.t _)  : state unit :=
    match agg with
      | cNot =>
        negationGeneric a
      | cExists =>
        existentialQuantificationGeneric a
    end
  .



  Instance _interpretAggregator_Proper : Proper (equiv ==> equiv ==> equiv) _interpretAggregator.
  Proof.
    unfold Proper, respectful. intros. simpl in H. rewrite H. destruct y.
    * simpl. arrequiv. 
    * simpl. arrequiv.
  Qed.

  Definition interpretAggregator := injF2 _interpretAggregator _.

End QALAggregator.

