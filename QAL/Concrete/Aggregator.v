Require Import Algebra.Utils Algebra.Monad SetoidUtils Algebra.SetoidCat.ListUtils Algebra.SetoidCat Algebra.Monad.StoreHeap Algebra.Monad.ContT Algebra.NearSemiRing Algebra.Monoid Tactics Algebra.FoldableFunctor Algebra.SetoidCat.PairUtils Algebra.Functor Algebra.Alternative Algebra.SetoidCat.MaybeUtils Algebra.Monad.Maybe Algebra.Applicative Algebra.SetoidCat.BoolUtils Algebra.SetoidCat.UnitUtils Algebra.Monoid.BoolUtils Algebra.Monoid.Alternative Algebra.Alternative.List Algebra.Functor.List Algebra.FoldableFunctor.List Algebra.Monad.Utils QAL.Command QAL.Definitions QAL.AbstractHeap QAL.AbstractStore.

Require Import Coq.Lists.List PeanoNat RelationClasses Relation_Definitions Morphisms Coq.Program.Basics SetoidClass.

Section Aggregator.

  Inductive qalAggregator :=
  | cExists : qalAggregator
  | cNot : qalAggregator
  | cReturn : list var -> qalAggregator
  .

  Program Instance qalAggregatorS : Setoid qalAggregator.

End Aggregator.

Module QALAggregator (PT : PredType) (VT : ValType)
       (S : AbstractStore VT) (H : AbstractHeap PT VT) : Aggregator PT VT S H.
  Open Scope type_scope.
  Module TS := Types PT VT S H.
  Module CA := CommandAux PT VT S H.
  Import VT S H TS CA.

  Definition aggregator := qalAggregator.
  Instance aggregatorS : Setoid aggregator := qalAggregatorS.
      
  Fixpoint _freeVarsAggregator (agg : aggregator) (fv : FVarSet.t) :=
    match agg with
      | cNot  => fv
      | cExists  => fv
      | cReturn _ => fv 
    end
  .

  Instance _freeVarsAggregator_Proper : Proper (equiv ==> equiv ==> equiv) _freeVarsAggregator.
  Proof.
    unfold Proper, respectful. intros. simpl in H. rewrite H. destruct y.
    * simpl. auto.  
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

  Section ReturnGeneric.
    Context
      (vl : list var)
      (a : H.l S.t _).
    Definition _narrowStore (vl : list var) (s : S.t) : S.t :=
      fold_right (fun v s2 => match s [ v ]s with
                               | None => s2
                               | Some val => S.update @ v @ val @ s2
                            end) S.empty vl.

    Instance _narrowStore_Proper : Proper (equiv ==> equiv ==> equiv) _narrowStore.
    Proof.
      unfold Proper, respectful. intros. generalize H  x0 y0 H0 . clear H x0 y0 H0.
      apply list_ind_2 with (l1:=x) (l2:=y).
      - intros. simpl. reflexivity.
      - intros. inversion H0.
      - intros. inversion H0.
      - intros. inversion H0.
        simpl. matchequiv. evalproper. simpl in H8. rewritesr. apply H.  auto.  auto. apply H. auto. auto.
    Qed.

    Definition narrowStore := injF2 _narrowStore _.

    Definition returnGeneric : state unit :=
      branchStore @ (narrowStore @ vl <$> a).
  End ReturnGeneric.
  Instance returnGeneric_Proper : Proper (equiv ==> equiv ==> equiv) returnGeneric.
  Proof.
    solve_properS returnGeneric.
  Qed.
 

  Fixpoint _interpretAggregator (agg : aggregator) (a : H.l S.t _)  : state unit :=
    match agg with
      | cNot =>
        negationGeneric a
      | cExists =>
        existentialQuantificationGeneric a
      | cReturn vl => returnGeneric vl a
    end
  .

  Instance _interpretAggregator_Proper : Proper (equiv ==> equiv ==> equiv) _interpretAggregator.
  Proof.
    unfold Proper, respectful. intros. simpl in H. rewrite H. destruct y.
    * simpl. arrequiv. 
    * simpl. arrequiv.
    * simpl. arrequiv.
  Qed.

  Definition interpretAggregator := injF2 _interpretAggregator _.

End QALAggregator.

