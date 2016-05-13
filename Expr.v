Require Import Tactics Utils Algebra.SetoidUtils Algebra.SetoidCat Algebra.ListUtils Algebra.Monad Algebra.PairUtils Algebra.Maybe Algebra.Functor Algebra.Applicative Definitions.

Require Import FMapWeakList List RelationClasses Relation_Definitions Morphisms SetoidClass.


Section Expr.
  Context
    {val : Type}
    {builtin : Type}.

  Inductive expr :=
| valExpr : val -> expr
| varExpr : var -> expr
| appExpr : builtin -> list expr -> expr
  .

  Program Instance exprS : Setoid expr :=
    {
      equiv := eq
    }.

  Section ExprInductionPrinciple.
    Variables (p : expr -> Prop) (Q : list expr -> Prop).

    Hypothesis
      (pval : forall val, p (valExpr val))
      (pvar : forall var, p (varExpr var))
      (papp0 : Q List.nil)
      (papp1 : forall e, p e -> forall l, Q l -> Q (e :: l))
      (papp : forall builtin l, Q l -> p (appExpr builtin l)).
    
    Fixpoint expr_ind_2 e : p e :=
      match e as x return p x with
        | valExpr val => pval val
        | varExpr var => pvar var
        | appExpr builtin l =>
          papp builtin l ((fix dep_fold_right (l' : list expr) : Q l' :=
                             match l' as x return Q x with
                               | List.nil => papp0
                               | e :: es => papp1 e (expr_ind_2 e) es (dep_fold_right es)
                             end
                          ) l)
      end.
  End ExprInductionPrinciple.

  Fixpoint exprFreeVars expr :=
    match expr with
      | valExpr _ => FVarSet.empty
      | varExpr var => FVarSet.singleton var
      | appExpr builtin exprs =>  fold_right FVarSet.union FVarSet.empty (map exprFreeVars exprs)
    end
  .

End Expr.


Module Type BuiltInExpr (VT : ValType).
  Import VT.
  Parameter builtInExpr : Type.
  Parameter builtInExprS : Setoid builtInExpr.
  Parameter appBIE : builtInExprS ~> listS valS ~~> optionS valS.
End BuiltInExpr.
  
Module ExprModel (VT : ValType) (B : BuiltInExpr VT) (S : Store VT).
  Import VT S B.
  Definition expr := @expr val builtInExpr.
  Instance exprS : Setoid expr := @exprS val builtInExpr.
  Existing Instance maybe_Monad.
  Existing Instance monadFunctor.
  Existing Instance monad_Applicative.
  Fixpoint _exprEval (s : S.t ) (e : expr) : maybe val :=
    match e with
      | valExpr val => Some val 
      | varExpr var => s [ var ]s
      | appExpr b args =>
        match (
            fix _exprsEval (s : S.t) (l : list expr) : option (list val) :=
              match l with
                | List.nil => ret @ @nil val
                | e :: es => consS <$> _exprEval s e <*> _exprsEval s es
              end) s args with
          | None => None
          | Some l => appBIE @ b @ l
        end
    end.
  
  Definition exprEval : S.tS ~> exprS ~~> optionS valS.
    simple refine (
             injF2 _exprEval _).
    Lemma exprEval_1 :  Proper (equiv ==> equiv ==> equiv) _exprEval.
    Proof.
      autounfold. intros. simpl in H0. rewrite H0. clear H0 x0. generalize H. clear H. apply expr_ind_2 with (e:= y0) (Q:=fun es => allTrue (fun y0 => x == y -> _exprEval x y0 == _exprEval y y0) es).
      intros. simpl. reflexivity.
      intros. simpl. equiv (x [var ]s) (y [var ]s). auto. 
      compute. auto.
      intros. unfold allTrue. rewrite map_cons.  rewrite fold_right_cons. split.
      auto.
      auto.
      intros. unfold _exprEval. fold _exprEval. pose (_es:=(fix _exprsEval (s : t) (l0 : list expr) {struct l0} :
        option (list val) :=
        match l0 with
        | nil => ret @ @nil val
        | e :: es => consS <$> _exprEval s e <*> _exprsEval s es
        end)). fold _es. assert (_es x l == _es y l).  induction l.
      simpl. constructor. 
      unfold _es. fold _es. destruct H. rewrite (IHl H1). rewrite (H H0). reflexivity.
equiv (_es x l) (_es y l). simpl in H1. rewrite H1. reflexivity. 
    Qed.
    apply exprEval_1.  
  Defined.
  
  Definition _exprsEval s (es : list expr) : maybe (list val) :=  
     mapM @ (exprEval @ s) @ es.
  
  Definition exprsEval : tS ~> listS exprS ~~> optionS (listS valS).
    simple refine (    injF2 _exprsEval _).
    Lemma exprsEval_1 : Proper (equiv ==> equiv ==> equiv) _exprsEval.
    Proof.
      repeat autounfold. intros. generalize H0. clear H0. apply list_ind_2 with (l1 := x0) (l2 := y0).
      intros. constructor.
      intros. inversion H1.
      intros. inversion H1.
      intros. inversion H1. unfold _exprsEval in *.  rewrite H5. rewrite H7. rewrite H. reflexivity.    Qed.
    apply exprsEval_1.
  Defined.
  
  Notation "⟦ e ⟧expr" := (fun s => exprEval @ s @ e)(at level 20).
  Notation "⟦ es ⟧exprs" := (fun s => exprsEval @ s @ es) (at level 20).

  Definition exprEval' := flipS @ exprEval.

End ExprModel.
