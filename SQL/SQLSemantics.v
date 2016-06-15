Require Import Assert Command Definitions Algebra.Monoid Expr Algebra.SetoidCat Algebra.Maybe Tactics Algebra.ListUtils Algebra.Functor Algebra.Applicative Algebra.Alternative Algebra.FoldableFunctor Algebra.PairUtils Algebra.Maybe Algebra.Monad Algebra.Lens.Lens Utils SetoidUtils SQLStore SQLHeap SQL Lista Matrixp Pointed.
Require Import Coq.Structures.DecidableTypeEx List SetoidClass PeanoNat FMapWeakList Basics.

Existing Instance maybe_Monad.
Existing Instance monadFunctor.
Existing Instance monad_Applicative.

Existing Instance sqlVal_Pointed.

Definition _fromMaybe {A} {AS: Setoid A} {AP : Pointed A} (a : maybe A) := 
  match a with
    | None => point
    | Some a => a
  end
.

Instance _fromMaybe_Proper A AS AP : Proper (equiv ==> equiv) (@_fromMaybe A AS AP).
Proof.
  autounfold. intros. unfold _fromMaybe. matchequiv. auto. 
Qed.

Definition fromMaybe { A AS AP} := injF (@_fromMaybe A AS AP)  _.

Instance fromMaybe_Pointed A AS AP : PointedFunction (@fromMaybe A AS AP).
Proof.
  split. reflexivity.
Qed.

Module SQLAsBuiltInExpr (B : BuiltInExpr SQLValType SQLStore) <: BuiltInExpr SQLValType SQLStore.
  Definition builtInExpr := sqlExpr B.builtInExpr.
  Instance builtInExprS : Setoid builtInExpr := sqlExprS B.builtInExpr.
  Fixpoint col (n : nat) (row : sqlVal) : option sqlVal :=
    match row with
      | vRow a b =>
        match n with
          | O => Some a
          | S n1 => col n1 b
        end
      | _ => None
    end
  .
  
  Fixpoint sqlExprEval (s : store) (e : builtInExpr) : option sqlVal :=
    match e with
      | sqlValExpr _ val => B.interpretBuiltInExpr @ val @ s
      | sqlVarExpr _ var => SQLStore.read @ var @ s 
      | sqlColExpr _ a colind =>
        match sqlExprEval s a with
             | Some (vRow a b) => col colind (vRow a b) 
             | _ => None
        end
      | sqlAppExpr _ e1 e2 =>
        SQLValType.appVal <$> sqlExprEval s e1 <*> sqlExprEval s e2 >>= idS
    end
  .
Ltac matchassertequiv := match goal with
            | |- _ (match ?a with _ => _ end) (match ?b with _ => _ end) => assert (a == b)
        end.
Ltac matchdestruct := match goal with
            | |- _ (match ?a with _ => _ end) (match ?b with _ => _ end) => destruct a, b
                      end.

Instance sqlExprEval_Proper : Proper (equiv ==> equiv ==> equiv)
                                 sqlExprEval.
    Proof.
      autounfold. intros. simpl in H0. rewrite H0. clear x0 H0.
      induction y0.
      - simpl. rewrite H. reflexivity.
      - intros. simpl. rewrite H. reflexivity.
      - intros. unfold sqlExprEval. fold sqlExprEval. evalproper. evalproper. evalproper. evalproper. evalproper. auto. auto. 
      - simpl. matchequiv. simpl in H0. rewrite H0. reflexivity. 
    Qed.
    
    Definition interpretBuiltInExpr : builtInExprS ~> SQLStore.tS ~~> maybeS sqlValS := flipS @ (injF2 sqlExprEval _).
    
End SQLAsBuiltInExpr.

(* builtInFormula *)
Module Type SQLBuiltInFormula.
  Parameter builtInCommand : Type.
  Parameter builtInCommandS : Setoid builtInCommand.
  Parameter appSQLBuiltInFormula : builtInCommandS ~> sqlValS ~~> sqlValS ~~> maybeS unitS.
End SQLBuiltInFormula.

(* SQL as builtInCommand *)
Module SQLAsBuiltInCommand (B : BuiltInExpr SQLValType SQLStore ) (BIC : SQLBuiltInFormula ) <: BuiltInCommand SQLTypeType SQLAddrType SQLPredType SQLValType SQLStore SQLHeap.
  Module SQLB := SQLAsBuiltInExpr B.
  Definition builtInFormula := sqlFormula B.builtInExpr BIC.builtInCommand.
  Instance builtInFormulaS : Setoid builtInFormula := sqlFormulaS B.builtInExpr BIC.builtInCommand.
  Definition builtInCommand := sqlStmt B.builtInExpr BIC.builtInCommand.
  Instance builtInCommandS : Setoid builtInCommand := sqlStmtS B.builtInExpr BIC.builtInCommand.

  Instance storeProd_Proper : Proper (equiv ==> equiv ==> equiv) storeProd.
  Proof.
    solve_properS storeProd.
  Qed.

  Definition storeProdS := injF2 storeProd _.
  
  Definition restrictStore (rets : list (sqlExpr B.builtInExpr * var)) (s : store) : maybe store :=
    fold_rightS @ storeProdS @ SQLStore.emptyStore
                <$> (sequence (map (fun (e : sqlExpr B.builtInExpr * var) =>
                                      SQLStore.update @ (snd e)
                                                      <$> (SQLB.sqlExprEval s (fst e))
                                                      <*> pure @ SQLStore.emptyStore 
                   ) rets)) .
  
  Definition getTableRows (m : database) (tab : nat) : lista (maybe row) := 
    match (nth_error m tab) with
      | Some tab => rows @ tab
      | None => listaCons _ nil
    end
  .

  Definition sqlTableExprEval (m : database) (tab : nat)  : list row :=  lista_filter' (getTableRows m tab).

  Definition listaToVRow (la : lista sqlVal) :=
    match la with
      | listaCons _ l => fold_right (fun a l =>
                                       match a with
                                         | vNil =>
                                           match l with
                                             | vNil => vNil
                                             | _ => vRow a l
                                           end
                                         | _ => vRow a l
                                       end) vNil l
    end
  .

  Instance listaToVRow_Proper : Proper (equiv ==> equiv) listaToVRow.
  Proof.
    autounfold. intros. destruct x,y. generalize H. clear H. apply list_ind_2 with (l1:=l) (l2:=l0).
    - intros. reflexivity.
    - intros. inversion H0. simpl in H1. rewrite H1. unfold listaToVRow.  rewrite fold_right_cons. fold (listaToVRow (listaCons _ b)).      rewrite <- H.  simpl. reflexivity. auto. 
    - intros. inversion H0. simpl in H1. rewrite H1. unfold listaToVRow.  rewrite fold_right_cons. fold (listaToVRow (listaCons _ b)).      rewrite H.  simpl. reflexivity. auto. 
    - intros. unfold listaToVRow. rewrite fold_right_cons. rewrite fold_right_cons. fold (listaToVRow (listaCons _ b)). fold (listaToVRow (listaCons _ d)).  inversion H0. rewrite H.  clear H. destruct a, c. 
      inversion H1. reflexivity.
      inversion H1.
      inversion H1.
      inversion H1.
      inversion H1.
      inversion H1.
      inversion H1. reflexivity.
      inversion H1.
      inversion H1.
      inversion H1.
      inversion H1. 
      inversion H1.
      reflexivity. 
      inversion H1.
      inversion H1.
      inversion H1.
      inversion H1.
      inversion H1.
      inversion H1. reflexivity.
      inversion H1.
      inversion H1.
      inversion H1.
      inversion H1.
      inversion H1.
      rewrite H1. reflexivity.
      auto.
  Qed.

  Definition _sqlValToStorableVal (a : maybe sqlVal) := 
    match a with
      | None => None
      | Some a => if SQLValType.storable a then Some a else None
    end
  .


  Instance _sqlValToStorableVal_Proper : Proper (equiv ==> equiv) _sqlValToStorableVal.
  Proof.
    autounfold. intros. unfold _sqlValToStorableVal. matchequiv. simpl in *. rewrite H. reflexivity.
  Qed.

  Definition sqlValToStorableVal := injF _sqlValToStorableVal _.

  Instance sqlValToStorableVal_Pointed : PointedFunction sqlValToStorableVal.
  Proof.
    split. reflexivity.
  Qed.

  Definition _storeToRow (s : store) : row :=
    lista_mapS fromMaybe @ (lista_mapS sqlValToStorableVal @ s)
  .

  Instance _storeToRow_Proper : Proper (equiv ==> equiv) _storeToRow.
  Proof.
    autounfold. intros.  destruct x,y. unfold _storeToRow.  rewritesr.
  Qed.  

  Definition storeToRow := injF _storeToRow _.

  Definition _rowStore (var1 : var) (r : row) := SQLStore.update @ var1 @ (listaToVRow r) @ SQLStore.emptyStore.

  Instance _rowStore_Proper : Proper (equiv ==> equiv ==> equiv) _rowStore.
  Proof.
    solve_properS _rowStore.
  Qed.

  Definition rowStore := injF2 _rowStore _.
  
  Definition rowsToStores (var1 : var) (rows : list row) := mapS @ (rowStore @ var1) @ rows.
  
  Fixpoint sqlFormEval (s : store) (m : database) (form: builtInFormula) : list SQLStore.t :=
    match form with
      | sqlBuiltIn _ _ builtin e1 e2 =>
        match SQLB.interpretBuiltInExpr @ e1 @ s, SQLB.interpretBuiltInExpr @ e2 @ s with
          | Some v1, Some v2 =>
            match BIC.appSQLBuiltInFormula @ builtin @ v1 @ v2 with
              | Some _ => s :: nil
              | _ => nil
            end
          | _, _ => nil
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
  sqlReduce (s : store) (m : database) (sql1 : sql B.builtInExpr BIC.builtInCommand) : list store :=
    match sql1 with
      | sqlQuery _ _ rets tabs form =>        
        let ss := fold_left
                    storesProd
                    (map (fun tab : nat * var =>
                            let (te, var) := tab in
                            rowsToStores var (sqlTableExprEval m te)) tabs) 
                    (s :: List.nil) in
        let filtered := concat (map (fun s => sqlFormEval s m form) ss) in 
        list_filter'  (map (restrictStore rets) filtered)
    end
  .

  Instance vRow_Proper : Proper (equiv ==> equiv ==> equiv) vRow.
  Proof.
    solve_proper. 
  Qed.

  Existing Instance sqlS.
  Instance sqlFormEval_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) sqlFormEval.
  Proof.
    autounfold. intros. generalize x y H H1. clear x y H H1.
    refine (sqlFormula_ind_2 B.builtInExpr BIC.builtInCommand (fun x1 y1=>forall x y : store,
   x == y -> x1 == y1 -> sqlFormEval x x0 x1 == sqlFormEval y y0 y1) (fun x1 y1=>forall x y : store,
   x == y -> x1 == y1 -> sqlReduce x x0 x1 == sqlReduce y y0 y1) 
      _ _ _ _ _
      _ _ _ _ _
      _ _ _ _ _
      _ _ _ _ _
      _ _ _ _ _
      _
      x1 y1).
    - intros.  unfold sqlFormEval.  inversion H1. matchequiv. matchequiv. matchequiv. rewrite H.  reflexivity. 
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
      - intros. inversion H2. clear H2. Opaque equiv. simpl. Transparent equiv.
        apply list_filter'_Proper. apply map_Proper.
        + autounfold. intros. unfold storeToRow. evalproper. apply sequence_Proper. apply map_Proper.
          * autounfold. intros. evalproper. rewritesr. 
          * reflexivity.
        + apply concat_Proper.  apply map_Proper.
          * autounfold. intros. rewrite <- H6 at 1. apply H. auto. auto.
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
              clear H. apply map_Proper;[|reflexivity]. autounfold. intros. destruct x2, y2. destruct H. apply map_Proper.
              {
                autounfold. intros. apply listaCons_Proper. apply lista_update0_Proper. auto. reflexivity. apply Some_Proper. apply listaToVRow_Proper. auto.
              }
              {
                unfold sqlTableExprEval. apply lista_filter'_Proper. unfold getTableRows. matchequiv. simpl in H3. rewrite H3. reflexivity.
              }
            }
            {
              rewritesr.
            }
  Qed.

  Instance restrictStore_Proper : Proper (equiv ==> equiv ==> equiv) restrictStore.
  Proof.
    autounfold. intros.  unfold restrictStore. evalproper. apply sequence_Proper.  apply map_Proper. autounfold. intros. rewrite H0, H1. reflexivity. auto.
  Qed.
  
  Instance storesProd_Proper : Proper (equiv ==> equiv ==> equiv) storesProd.
  Proof.
    autounfold. intros.  unfold storesProd. apply concat_Proper.  apply map_Proper. autounfold. intros. apply map_Proper. autounfold. intros. apply storeProd_Proper. auto. auto. auto. auto. 
  Qed.
  
  Instance rowsToStores_Proper : Proper (equiv ==> equiv ==> equiv) rowsToStores.
  Proof.
    autounfold. intros.  unfold rowsToStores. rewritesr. 
  Qed.

  Instance getTableRows_Proper : Proper (equiv ==> equiv ==> equiv) getTableRows.
  Proof.
    autounfold. intros.  unfold getTableRows. matchequiv. simpl in H1. rewrite H1. reflexivity. 
  Qed.

  Instance sqlTableExprEval_Proper : Proper (equiv ==> equiv ==> equiv) sqlTableExprEval.
  Proof.
    autounfold. intros. unfold sqlTableExprEval. apply lista_filter'_Proper. apply getTableRows_Proper. auto. auto.
  Qed.
  
  Instance sqlReduce_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) sqlReduce.
  Proof.
    autounfold. intros. destruct x1, y1. rewrite H1. clear H1. Opaque equiv. simpl. Transparent equiv. apply list_filter'_Proper. apply map_Proper. autounfold. intros. apply restrictStore_Proper. reflexivity. auto. apply concat_Proper. apply map_Proper. autounfold. intros. apply sqlFormEval_Proper. auto. auto. reflexivity. apply fold_left_Proper. autounfold. intros. apply storesProd_Proper. auto. auto. apply map_Proper. autounfold. intros. destruct x1, y1. destruct H1.  apply rowsToStores_Proper. auto. apply sqlTableExprEval_Proper. auto. auto. reflexivity. constructor.  auto. reflexivity.
  Qed.
  
  Definition insertRows (table : nat) (rows : list row) (m : database) : maybe database := rowsSetter @ table <$> (lista_mergeS <$> rowsGetter @ table @ m <*> pure @ rows) <*> pure @ m.

  Definition deleteRow (table : nat) (ri : nat) (m : database) : maybe database := rowsSetter @ table <$> (lista_deleteS @ ri <$> rowsGetter @ table @ m) <*> pure @ m.

  Definition updateRowS  : natS ~> natS ~~> natS ~~> sqlValS ~~> databaseS ~~> databaseS := cellSetter.

  Definition _interpretBuiltInCommand0 (comm : builtInCommand) (m : database) (s : store) : database * list store :=
    match comm with
      | sqlQueryStmt _ _ sql => (m, sqlReduce s m sql)
      | sqlInsertStmt _ _ table sql =>
        match sql with
          | sqlQuery _ _ rets _ _ =>
            let cols := map snd rets in
            let stores := sqlReduce s m sql in
            let rows := mapS @ storeToRow @ stores in
            match insertRows table rows m with
              | None => (m, nil)
              | Some m' => (m', s :: nil)
            end
        end
      | sqlDeleteStmt _ _ table var1 form =>
        let rows := getTableRows m table in
        let storesi := mapS @ (idS *** rowStore @ var1) @ (lista_filter_indexS' @ rows) in
        let m' := fold_right (fun ris m' =>
                                match ris with
                                  | (i, s) =>
                                    match sqlFormEval s m' form with
                                      | nil => m'
                                      | _ =>
                                        match deleteRow table i m' with
                                          | None => m'
                                          | Some m'' => m''
                                        end
                                    end
                                end) m storesi in
        (m', s::nil)
      | sqlUpdateStmt _ _ table var1 updates form =>
        let rows := getTableRows m table in
        let storesi := mapS @ (idS *** rowStore @ var1) @ (lista_filter_indexS' @ rows) in
        let m' := fold_right (fun ris m' =>
                                match ris with
                                  | (i, s) =>
                                    match sqlFormEval s m' form with
                                      | nil => m'
                                      | _ =>
                                        fold_right (fun update m'' =>
                                               match update with
                                                 | (c, e) =>
                                                   match SQLB.sqlExprEval s e with
                                                     | None => m''
                                                     | Some val => updateRowS @ table @ i @ c @ val @ m''
                                                   end
                                               end) m' updates
                                    end
                                end) m storesi in
        (m', s::nil)
    end
  .

  Instance _interpretBuiltInCommand0_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _interpretBuiltInCommand0.
  Proof.
    autounfold. intros. unfold _interpretBuiltInCommand0.  destruct x, y.
    - split. auto. simpl in H. inversion H. apply sqlReduce_Proper. auto. auto. reflexivity.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H. destruct s0. assertequiv. unfold insertRows. rewritesr. matchequiv. simpl in H2. split. auto. constructor. auto. reflexivity. split. auto. reflexivity. 
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H. split. apply fold_right_Proper. autounfold. intros. destruct x, y. destruct H2. matchequiv. auto. apply fold_right_Proper. autounfold. intros. destruct x, y. destruct H10. assertequiv. apply SQLB.sqlExprEval_Proper. auto. auto. matchequiv. simpl in H13. rewritesr. auto. auto. reflexivity. auto. rewritesr. rewritesr. 
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H. split. apply fold_right_Proper. autounfold. intros. destruct x, y. destruct H2. matchequiv. auto. assertequiv. unfold deleteRow. rewritesr. matchequiv. simpl in H9. auto. auto. auto. rewritesr. rewritesr. 
  Qed.
  
  Definition interpretBuiltInCommand0 : builtInCommandS ~> databaseS ~~> storeS ~~> databaseS ~*~ listS storeS :=
    injF3 _interpretBuiltInCommand0 _.

  Module TS := Types SQLTypeType SQLAddrType SQLPredType SQLValType SQLStore SQLHeap.

  Existing Instance list_Foldable.
  Existing Instance StoreHeap.sh_Alternative.
  Existing Instance TS.state_Monad.
  Existing Instance alternative_Monoid.
  Existing Instance monad_Applicative.
  
  Definition _branchStores (ss : list store) : TS.state unit := fold @ (mapS @ StoreHeap.putStore @ ss).
  Instance _branchStores_Proper : Proper (equiv ==> equiv) _branchStores.
  Proof.
    solve_properS _branchStores.
  Qed.

  Definition branchStores := injF _branchStores _.

  Definition _interpretBuiltInCommand (comm : builtInCommand) : TS.state unit.
    refine (
    (interpretBuiltInCommand0
      @ comm
      <$> StoreHeap.getHeap
      <*> StoreHeap.getStore) >>= injF (fun mss => match mss with
                                                       | (m, ss) =>
                                                         StoreHeap.putHeap @ m >>
                                                                           branchStores @ ss
                                                   end) _).
    apply TS.state_Monad. 
    Lemma _interpretBuiltInCommand_1 : Proper (equiv ==> equiv)
     (fun mss : SQLHeap.t * list store =>
        let (m, ss) := mss in StoreHeap.putHeap @ m >> branchStores @ ss).
    Proof.
      autounfold. intros. destruct x,y.  destruct H. rewritesr.
    Qed.
    apply _interpretBuiltInCommand_1.
  Defined.
  
  Instance _interpretBuiltInCommand_Proper : Proper (equiv ==> equiv) _interpretBuiltInCommand.
  Proof.
    autounfold. intros. rewritesr. 
  Qed.

  Definition interpretBuiltInCommand : builtInCommandS ~> TS.stateS unitS :=
    injF _interpretBuiltInCommand _.

  Fixpoint sqlExprFreeVars (e : sqlExpr B.builtInExpr) :=
    match e with
      | sqlValExpr _ _ => FVarSet.empty
      | sqlVarExpr _ v => FVarSet.singleton v
      | sqlColExpr _ v _ => sqlExprFreeVars v
      | sqlAppExpr _ e1 e2 => FVarSet.union (sqlExprFreeVars e1) (sqlExprFreeVars e2)
    end
  .
  
  Fixpoint freeVars (comm : builtInFormula) :=
    match comm with
      | sqlBuiltIn _ _ builtin e1 e2 =>
        FVarSet.union (sqlExprFreeVars  e1) (sqlExprFreeVars  e2)
      | sqlAnd _ _ form1 form2 =>
        FVarSet.union (freeVars form1) (freeVars form2)
      | sqlOr _ _ form1 form2 =>
        FVarSet.union (freeVars form1) (freeVars form2)
      | sqlNot _ _ form1 =>
        freeVars form1
      | sqlExists _ _ sql =>
        sqlFreeVars sql
    end
  with
  sqlFreeVars (s : sql B.builtInExpr BIC.builtInCommand) :=
    match s with
      | sqlQuery _ _ _ _ s1 => freeVars s1
    end
  .

  Instance freeVars_Proper : Proper (equiv ==> equiv) freeVars.
  Proof.
    solve_properS freeVars.
  Qed.

  Definition _freeVarsBuiltInCommand (comm : builtInCommand) :=
    match comm with
      | sqlQueryStmt _ _ (sqlQuery _ _ _ _ form) =>
        freeVars form
      | sqlInsertStmt _ _ _ sql =>
        sqlFreeVars sql
      | sqlUpdateStmt _ _ _ _ _ form =>
        freeVars form
      | sqlDeleteStmt _ _ _ _ form =>
        freeVars form
    end
  .

  Definition freeVarsBuiltInCommand := injF _freeVarsBuiltInCommand _.
End SQLAsBuiltInCommand.
      
  


    
