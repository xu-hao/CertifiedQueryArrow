Require Import Tactics Utils Algebra.SetoidUtils Algebra.SetoidCat Algebra.ListUtils Algebra.Monad Algebra.PairUtils Algebra.Maybe Algebra.Functor Algebra.Applicative Definitions.

Require Import FMapWeakList List RelationClasses Relation_Definitions Morphisms SetoidClass.


Section Expr.
  Context
    {val : Type}
    {builtin : Type}.

  Inductive expr :=
  | valExpr : builtin -> expr
  | varExpr : var -> expr
  | appExpr : expr -> expr -> expr
  .

  Program Instance exprS : Setoid expr :=
    {
      equiv := eq
    }.


  Fixpoint exprFreeVars expr :=
    match expr with
      | valExpr _ => FVarSet.empty
      | varExpr var => FVarSet.singleton var
      | appExpr e1 e2 => FVarSet.union (exprFreeVars e1) (exprFreeVars e2)
    end
  .

End Expr.

Module Type BuiltInExpr (VT : ValType) (S : Store VT).
  Parameter builtInExpr : Type.
  Parameter builtInExprS : Setoid builtInExpr.
  Parameter interpretBuiltInExpr : builtInExprS ~> S.tS ~~> maybeS VT.valS.
End BuiltInExpr.

Module ExprModel (VT : ValType)   (S : Store VT) (B: BuiltInExpr VT S).
  Import VT S B.
  Definition expr := @expr builtInExpr.
  Instance exprS : Setoid expr := @exprS builtInExpr.
  Existing Instance maybe_Monad.
  Existing Instance monadFunctor.
  Existing Instance monad_Applicative.
  Fixpoint _exprEval (s : S.t ) (e : expr) : maybe val :=
    match e with
      | valExpr val => interpretBuiltInExpr @ val @ s
      | varExpr var => s [ var ]s
      | appExpr e1 e2 => appVal <$> _exprEval s e1 <*> _exprEval s e2 >>= idS
    end.
  
  Instance exprEval_Proper :  Proper (equiv ==> equiv ==> equiv) _exprEval.
  Proof.
    autounfold. intros. simpl in H0. rewrite H0. clear H0 x0. generalize H. clear H. induction y0. 
    - intros. simpl. rewrite H. reflexivity.
    - intros. simpl. equiv (x [v ]s) (y [v ]s). auto. 
    - intros. unfold _exprEval. fold _exprEval. evalproper. evalproper. evalproper. evalproper. evalproper. auto. auto. 
  Qed.
  
  Definition exprEval : S.tS ~> exprS ~~> optionS valS := injF2 _exprEval _.
  
  Definition _exprsEval s (es : list expr) : maybe (list val) :=  
     mapM @ (exprEval @ s) @ es.
  
  Instance exprsEval_Proper : Proper (equiv ==> equiv ==> equiv) _exprsEval.
  Proof.
    repeat autounfold. intros. generalize H0. clear H0. apply list_ind_2 with (l1 := x0) (l2 := y0).
    intros. constructor.
    intros. inversion H1.
    intros. inversion H1.
    intros. inversion H1. unfold _exprsEval in *.  rewrite H5. rewrite H7. rewrite H. reflexivity.
  Qed.
  
  Definition exprsEval : tS ~> listS exprS ~~> optionS (listS valS) := injF2 _exprsEval _.
  
  Notation "⟦ e ⟧expr" := (fun s => exprEval @ s @ e)(at level 20).
  Notation "⟦ es ⟧exprs" := (fun s => exprsEval @ s @ es) (at level 20).

  Definition exprEval' := flipS @ exprEval.

End ExprModel.
