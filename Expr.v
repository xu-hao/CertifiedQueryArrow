Require Import Tactics Utils Algebra.SetoidUtils Algebra.SetoidCat Algebra.ListUtils Algebra.Monad Algebra.PairUtils Algebra.Maybe Algebra.Functor Algebra.Applicative Definitions.

Require Import FMapWeakList List RelationClasses Relation_Definitions Morphisms SetoidClass.




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
        papp builtin l ((
               fix dep_fold_right (l' : list expr) : Q l' :=
                 match l' as x return Q x with
                   | List.nil => papp0
                   | e :: es => papp1 e (expr_ind_2 e) es (dep_fold_right es)
                 end
             ) l)
    end.
End ExprInductionPrinciple.

Section ExprRecursionPrincipleNonDep.
  Context {P : Type} {Q : Type}.

  Hypothesis
    (pval : val -> P)
    (pvar : var -> P)
    (papp0 : Q)
    (papp1 : expr -> P -> list expr -> Q -> Q)
    (papp : builtin -> list expr -> Q -> P).
  
    Fixpoint expr_rect_nondep_2 e : P :=
    match e with
      | valExpr val => pval val
      | varExpr var => pvar var
      | appExpr builtin l =>
        papp builtin l ((
               fix nondep_fold_right (l' : list expr) : Q :=
                 match l' with
                   | List.nil => papp0
                   | e :: es => papp1 e (expr_rect_nondep_2 e) es (nondep_fold_right es)
                 end
             ) l)
    end.

    Context {SP : Setoid P} {SQ : Setoid Q}.

    Definition expr_rect_nondep_2Proper  : exprS ~> SP.
      simple refine (injF expr_rect_nondep_2 _).
    Defined.
    
End ExprRecursionPrincipleNonDep.

(* Section ExprIterationPrincipleNonDep.
  Context {P : Type} {Q : Type}.


  Section Raw.
    Hypothesis
    (pval : val -> P)
    (pvar : var -> P)
    (papp0 : Q)
    (papp1 : P -> Q -> Q)
    (papp : builtin -> Q -> P).
  
    Fixpoint expr_itrt_nondep_2 (e : expr) : P :=
    match e with
      | valExpr val => pval val
      | varExpr var => pvar var
      | appExpr builtin l =>
        papp builtin ((
               fix nondep_fold_right (l' : list expr) : Q :=
                 match l' with
                   | List.nil => papp0
                   | e :: es => papp1  (expr_itrt_nondep_2 e)  (nondep_fold_right es)
                 end
             ) l)
    end.
  End Raw.
  
  Context {SP : Setoid P} {SQ : Setoid Q}.

  Definition expr_itrt_nondep_2Proper :
    (valS ~~> SP) ~>
    SP ~~>
    SQ ~~>
    (SP ~~> SQ ~~> SQ) ~~>
    (builtinS ~~> SQ ~~> SP) ~~>
    exprS ~~> SP.
      simple refine (injF expr_itrt_nondep_2 _).

      Lemma expr_itrt_nondep_2Proper_1 : properF expr_itrt_nondep_2.
      Proof.
        unfold properF. solve_proper.
      Qed.

      apply expr_itrt_nondep_2Proper_1.
                                           Defined.
    
    
End ExprIterationPrincipleNonDep. *)


Fixpoint exprFreeVars expr :=
  match expr with
    | valExpr _ => ∅
    | varExpr var => ﹛ var ﹜
    | appExpr builtin exprs =>  fold_right FSetNat.union ∅ (map exprFreeVars exprs)
  end
.



Module Type BuiltInExpr.
  Parameter app : builtinS ~> listS valS ~~> optionS valS.
End BuiltInExpr.
  
Module ExprModel (B : BuiltInExpr) (S : Store).
  Import S.
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
          | Some l => B.app @ b @ l
        end
    end.

  Lemma fold_right_cons : forall A B (f : A -> B -> B) (b : B) (a : A) (l : list A),
                            fold_right f b (a :: l) = f a (fold_right f b l).
  Proof.
    reflexivity.
  Qed.
  
  Definition exprEval : S.tS ~> exprS ~~> optionS valS.
    simple refine (
             injF2 _exprEval _).
    Lemma exprEval_1 :  Proper (equiv ==> equiv ==> equiv) _exprEval.
    Proof.
      repeat autounfold. intros. simpl in H0. rewrite H0. clear H0 x0. generalize H. clear H. apply expr_ind_2 with (e:= y0) (Q:=fun es => allTrue (fun y0 => x == y -> _exprEval x y0 == _exprEval y y0) es).
      intros. simpl. auto.
      intros. simpl. equiv (x [var ]s) (y [var ]s) H. auto. 
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
equiv (_es x l) (_es y l) H1. simpl in H1. rewrite H1. reflexivity. 
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
