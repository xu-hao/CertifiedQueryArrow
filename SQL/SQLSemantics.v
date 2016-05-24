Require Import Assert Command Definitions Algebra.Monoid Expr Algebra.SetoidCat Algebra.Maybe Tactics Algebra.ListUtils Algebra.Functor Algebra.Applicative Algebra.Alternative Algebra.FoldableFunctor Algebra.PairUtils Algebra.Maybe Algebra.Monad Algebra.Lens.Lens Utils SetoidUtils SQLStore SQLHeap SQL Lista Matrixp.
Require Import Coq.Structures.DecidableTypeEx List SetoidClass PeanoNat FMapWeakList Basics.

Existing Instance maybe_Monad.
Existing Instance monadFunctor.
Existing Instance monad_Applicative.

Existing Instance sqlVal_Pointed.

Module SQLBuiltInExpr (B : BuiltInExpr SQLTypeType SQLAddrType SQLPredType SQLValType SQLStore SQLHeap) <: BuiltInExpr SQLTypeType SQLAddrType SQLPredType SQLValType SQLStore SQLHeap.
  Definition builtInExpr := sqlExpr B.builtInExpr.
  Instance builtInExprS : Setoid builtInExpr := sqlExprS B.builtInExpr.
  Fixpoint sqlExprEval (s : store) (h : database) (e : builtInExpr) : option sqlVal :=
    match e with
      | sqlValExpr _ val => Some val
      | sqlVarExpr _ var => SQLStore.read @ var @ s 
      | sqlColExpr _ a colind =>
        match sqlExprEval s h a with
             | Some (vAddr (t, ri)) => cellGetter @ t @ ri @ colind @ h
             | _ => None
        end
      | sqlAppExpr _ builtin args =>
        match sequence (map (sqlExprEval s h) args) with
          | Some l => B.appBIE @ builtin @ l @ h @ s
          | None => None
        end
    end
  .
Ltac matchassertequiv := match goal with
            | |- _ (match ?a with _ => _ end) (match ?b with _ => _ end) => assert (a == b)
        end.
Ltac matchdestruct := match goal with
            | |- _ (match ?a with _ => _ end) (match ?b with _ => _ end) => destruct a, b
                      end.

Lemma sqlExprEval_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv)
                                 sqlExprEval.
    Proof.
      autounfold. intros. simpl in H1. rewrite H1.
      apply sqlExpr_ind_2 with (e:=y1) (Q:=fold_right (fun y1 p => sqlExprEval x x0 y1 == sqlExprEval y y0 y1 /\ p) True).
      - simpl. reflexivity.
      - intros. simpl. rewrite H. reflexivity.
      - intros. simpl. matchequiv. matchequiv. inversion H4. inversion H4. simpl in H4. inversion H4. destruct s0. matchequiv. destruct m, m0. simpl in H5. simpl. matchassertequiv. rewrite H5. reflexivity.  matchdestruct.  simpl in H7. rewrite H7. reflexivity. inversion H7. inversion H7. reflexivity. 
      - simpl.  auto.
      - intros. split.
        + rewritesr.
        + auto.
      - intros. unfold sqlExprEval.  fold sqlExprEval. matchassertequiv.
        + induction l.
          * simpl. reflexivity.
          * rewrite map_cons. rewrite map_cons.
            rewrite sequence_cons. rewrite sequence_cons. destruct H2. rewrite IHl. rewrite H2. reflexivity. apply H3.
        + matchequiv. simpl in H3. rewrite H, H0, H3. reflexivity.
    Qed.
    
  Definition appBIE : builtInExprS ~> listS sqlValS ~~> SQLHeap.tS ~~> SQLStore.tS ~~> maybeS sqlValS.
    refine (injF4 (fun e _ h s => sqlExprEval s h e) _).
    Lemma sqlExprEval_1 : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv)
                                 (fun (e : builtInExpr) (_ : list sqlVal) h (s : store) => sqlExprEval s h e).
    Proof.
      autounfold. intros. simpl in H. rewrite H.
      apply sqlExpr_ind_2 with (e:=y) (Q:=fold_right (fun y p => sqlExprEval x2 x1 y == sqlExprEval y2 y1 y /\ p) True).
      - simpl. reflexivity.
      - intros. simpl. rewrite H2. reflexivity.
      - intros. simpl. matchequiv. matchequiv.  inversion H5. inversion H5. simpl in H3. inversion H3. destruct s0. matchassertequiv. rewritesr. matchdestruct. destruct m, m0. simpl. simpl in H6. matchassertequiv. rewrite H6. reflexivity. matchdestruct. simpl in H8. rewrite H8. reflexivity. inversion H8. inversion H8. reflexivity. inversion H6. inversion H6. reflexivity. 
      - simpl.  auto.
      - intros. split.
        + rewritesr.
        + auto.
      - intros. unfold sqlExprEval.  fold sqlExprEval. matchassertequiv.
        + induction l.
          * simpl. reflexivity.
          * rewrite map_cons. rewrite map_cons.
            rewrite sequence_cons. rewrite sequence_cons. destruct H3. rewrite IHl. rewrite H3. reflexivity. apply H4.
        + matchequiv. simpl in H4. rewrite H1, H2, H4. reflexivity.
    Qed.
    apply sqlExprEval_1.
  Defined.
  
End SQLBuiltInExpr.

Module SQLBuiltInFormula (BIE : BuiltInExpr SQLTypeType SQLAddrType SQLPredType SQLValType SQLStore SQLHeap) (BIF : BuiltInFormula SQLTypeType SQLAddrType SQLPredType SQLValType SQLStore SQLHeap) <: BuiltInFormula SQLTypeType SQLAddrType SQLPredType SQLValType SQLStore SQLHeap.
  Module SQLBIE := SQLBuiltInExpr BIE.
  Definition builtInFormula := sqlFormula BIE.builtInExpr BIF.builtInFormula.
  Instance builtInFormulaS : Setoid builtInFormula := sqlFormulaS BIE.builtInExpr BIF.builtInFormula.
  Definition storeToRow (rets : list (sqlExpr BIE.builtInExpr)) (s : store) (h : database) : maybe row :=
    listaConsS <$> (sequence (map (fun (e : sqlExpr BIE.builtInExpr) =>
                                       SQLBIE.sqlExprEval s h e
                   ) rets)) .

  
    Fixpoint sqlFormEval (s : store) (m : database) (form: builtInFormula) : list SQLStore.t :=
      match form with
        | sqlBuiltInFormula _ _ builtin args =>
          match sequenceS @ (mapS @ (cycle3S @ SQLBIE.appBIE @ nil @ s) @ args) with
            | Some l => BIF.appBIF @ builtin @ l @ m @ s
            | None => nil
          end
        | sqlAnd _ _ form1 form2 =>
          concat (map (fun s => sqlFormEval s m form2) (sqlFormEval s m form1))
        | sqlOr _ _ form1 form2 =>
          sqlFormEval s m form1 ++ sqlFormEval s m form2
        | sqlNot _ _ form1 =>
          if null (sqlFormEval s m form1) then
            s :: nil
          else
            nil
        | sqlExists _ _ sql =>
          if null (sqlReduce s m sql) then
            nil
          else
            s :: nil
      end
    with
    sqlReduce (s : store) (m : database) (sql1 : sql BIE.builtInExpr BIF.builtInFormula) : list row :=
      match sql1 with
        | sqlQuery _ _ rets tabs form =>
          
          let ss := fold_left
            storesProd
            (map (fun tab : sqlTableExpr BIE.builtInExpr BIF.builtInFormula * var =>
                    let (te, var) := tab in
                    map (fun r => SQLStore.update @ var @ (vRow r) @ SQLStore.emptyStore) (map listOfLista (sqlTableExprEval s m te))) tabs) 
            (s :: List.nil) in
          let filtered := concat (map (fun s => sqlFormEval s m form) ss) in 
          list_filter'  (map (storeToRow rets) filtered)
      end
    with
    sqlTableExprEval (s : store) (m : database) (te : sqlTableExpr BIE.builtInExpr BIF.builtInFormula) : list row :=
      match te with
        | sqlTable _ _ tab => match (nth_error m tab) with
                            | Some tab => lista_filter' (rows @ tab)
                            | None => nil
                          end
        | sqlSelect _ _ sql1 => sqlReduce s m sql1
      end
    .

    Existing Instance sqlTableExprS.

    Instance vRow_Proper : Proper (equiv ==> equiv) vRow.
    Proof.
      autounfold. intros. simpl in *. rewrite H. 
    Instance sqlFormEval_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) sqlFormEval.
    Proof.
      autounfold. intros. generalize x y H H1. clear x y H H1.
      refine (sqlFormula_ind_2 _ _
      (fun x1 y1 => forall x y : store,
   x == y -> x1 == y1 -> sqlFormEval x x0 x1 == sqlFormEval y y0 y1)
      (fun q1 q2 => forall x y : store,
                         x == y -> @equiv (sql _ _) (sqlS _ _) q1 q2 -> sqlReduce x x0 q1 == sqlReduce y y0 q2)
      (fun tel1 tel2 => forall x y : store,
                             x == y -> tel1 == tel2 -> fold_right and True (list_zipWith_not_proper (fun vt1 vt2 =>
                                                                                             match vt1, vt2 with
                                                                                               | (te1, v1), (te2, v2) => sqlTableExprEval x x0 te1 == sqlTableExprEval y y0 te2
                                                                                             end
                                                                                          ) tel1 tel2))
      (fun te1 te2 =>
            forall x y : store,
              x == y -> te1 == te2 -> sqlTableExprEval x x0 te1 == sqlTableExprEval y y0 te2)
      _ _ _ _ _
      _ _ _ _ _
      _ _ _ _ _
      _ _ _ _ _
      _ _ _ _ _
      _
      _ _ _ _
      _ _ _ _
      x1 y1).
      - intros.  unfold sqlFormEval.  inversion H1. matchequiv. simpl in H2. rewrite H, H0, H2. reflexivity.
      - intros.  inversion H1.
      - intros. inversion H1.
      - intros. inversion H1.
      - intros. inversion H1.
      - intros. inversion H1.
      - intros. inversion H3. unfold sqlFormEval.  fold sqlFormEval. apply concat_Proper.  apply map_Proper. 
        + autounfold. intros. rewrite <- H6 at 1. apply H1. auto. auto.
        + rewrite <- H5 at 1. apply H. auto. auto.
      - intros.  inversion H1.
      - intros.  inversion H1.
      - intros.  inversion H1.
      - intros.  inversion H1.
      - intros.  inversion H1.
      - intros. inversion H3. unfold sqlFormEval.  fold sqlFormEval. apply app_Proper.  
        + rewrite <- H5 at 1. apply H. auto. auto.
        + rewrite <- H6 at 1. apply H1. auto. auto.
      - intros.  inversion H1.
      - intros.  inversion H1.
      - intros.  inversion H1.
      - intros.  inversion H1.
      - intros.  inversion H1.
      - intros.  inversion H2. unfold sqlFormEval.  fold sqlFormEval.
        assert (null (sqlFormEval x2 x0 a) == null (sqlFormEval y y0 a)). apply null_Proper.  
        rewrite <- H4 at 1. apply H. auto. auto. destruct (null (sqlFormEval x2 x0 a) ), (null (sqlFormEval y y0 a) ).
        + rewritesr.
        + inversion H3.
        + inversion H3.
        + reflexivity.
      - intros. inversion H1.
      - intros. inversion H1.
      - intros. inversion H1.
      - intros. inversion H1.
      - intros. inversion H1.
      - intros. inversion H2. Opaque equiv. simpl.  Transparent equiv.
        match goal with
          | |- (if ?a then _ else _) == (if ?b then _ else _) => assert (a == b)
        end.
        apply null_Proper.  
        rewrite <- H4 at 1. apply H. apply H1. rewrite H4.  reflexivity.
        match goal with
          | |- (if ?a then _ else _) == (if ?b then _ else _) => destruct a, b
        end.
        + reflexivity.  
        + inversion H3.
        + inversion H3.
        + rewritesr. 
      - intros. inversion H3. Opaque equiv. simpl.  Transparent equiv.
        apply list_filter'_Proper. apply map_Proper.
        + autounfold. intros. unfold storeToRow. evalproper. apply sequence_Proper. apply map_Proper.
          * autounfold. intros. 
            match goal with
              | |- match ?a with _ => _ end == match ?b with _ => _ end => assert (a== b)
            end.
            apply SQLBIE.sqlExprEval_Proper. auto. auto.
            match goal with
              | |- match ?a with _ => _ end == match ?b with _ => _ end => destruct a, b
            end.
            {
              simpl in H9. all_cases.  inversion H9. inversion H9. inversion H9. inversion H9.
            }
            {
              inversion H9.
            }
            {
              inversion H9.
            }
            reflexivity.
          * reflexivity.
        + apply concat_Proper.  apply map_Proper.
          * autounfold. intros. rewrite <- H7 at 1. apply H1. auto. auto.
          * apply fold_left_Proper.
            {
              autounfold. intros. unfold storesProd. apply concat_Proper. apply map_Proper.
              {
                autounfold. intros. apply map_Proper.
                {
                  autounfold. intros. unfold storeProd. apply lista_zipWith_Proper. auto. auto.
                }
                {
                  auto.
                }
              }
              {
                auto.
              }
            }
            {
              clear H. refine (map_Proper (fun tab : sqlTableExpr BIE.builtInExpr BIF.builtInFormula * var =>
      let (te, var) := tab in
      map
        (fun r : list sqlVal =>
         listaCons (option sqlVal) (lista_update0 var nil (Some (vRow r))))
        (map listOfLista (sqlTableExprEval x x0 te))) (fun tab : sqlTableExpr BIE.builtInExpr BIF.builtInFormula * var =>
      let (te, var) := tab in
      map
        (fun r : list sqlVal =>
         listaCons (option sqlVal) (lista_update0 var nil (Some (vRow r))))
        (map listOfLista (sqlTableExprEval y y0 te))) _ tel2 tel2 _).
              {
                autounfold. intros. repeat rewrite let_intro. apply map_Proper. autounfold. intros. apply listaCons_Proper. apply lista_update0_Proper. 
                apply (@snd_Proper (sqlTableExpr BIE.builtInExpr BIF.builtInFormula) _ equiv _). auto. reflexivity. apply Some_Proper. apply vRow_Proper. rewrite H. unfold equiv in H.  simpl in H. 
            rewrite H4, H8.

            matchequiv. rewritesr. reflexivity. simpl. fold fold_left. _cons.
      - intros. inversion H1.
      - intros. inversion H1.
      - intros. inversion H1.
      - intros. inversion H1.
      - intros. inversion H1.

    Definition appBIF : sqlFormulaS ~> listS sqlValS ~~> databaseS ~~> storeS ~~> listS storeS :=
  constS _ @ (constS _ @ (constS _ @ constS _ @ nil)).
End SQLBuiltInFormula.
      
Module SQLModel .
  (* SQL as builtInFormula and builtInCommand *)
  


    
End SQLModel.
