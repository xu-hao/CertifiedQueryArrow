Require Import Assert Utils Algebra.Monad Algebra.SetoidUtils Algebra.ListUtils Algebra.SetoidCat Algebra.StoreHeap Algebra.ContT Algebra.Store Algebra.NearSemiRing Algebra.Monoid Tactics Expr Definitions Algebra.MonoidUtils Algebra.FoldableFunctor Algebra.PairUtils Algebra.Functor Algebra.Alternative Algebra.Maybe Algebra.Applicative.

Require Import List PeanoNat RelationClasses Relation_Definitions Morphisms Coq.Program.Basics SetoidClass.

Definition  commutative {A} {SA : Setoid A} {nsr : @NearSemiRing _ SA} (a b : A ) := times @ a @ b == times @ b @ a.


  
Inductive formula :=
| formFilter : expr -> pred -> expr -> formula
| formBuiltInFilter : builtin -> list expr -> formula
| formLookupBySubject : expr -> pred -> var -> formula
| formLookupByObject : var -> pred -> expr -> formula
| formLookupByPred : var -> pred -> var -> formula
| formAnd : formula -> formula -> formula
| formOr : formula -> formula -> formula
| formExists : var -> formula -> formula
| formNot : formula -> formula
| formTrue : formula
.

Notation "a ∧ b" := (formAnd a b) (left associativity, at level 81).
Notation "a ∨ b" := (formOr a b) (left associativity, at level 82).
Notation "∃ a : b" := (formExists a b) (at level 83).
Notation "¬ a" := (formNot a) (at level 80).
Notation "⊤" := (formTrue) (at level 80).

Program Instance formulaS : Setoid formula.

Inductive command :=
| classical : formula -> command
| cNewAddr : var -> command
| cLookupBySubject : expr -> pred -> var -> command
| cLookupByObject : var -> pred -> expr -> command
| cLookupByPred : var -> pred -> var -> command
| mutate : expr -> pred -> expr -> command
| cDelete : expr -> command
| seq : command -> command -> command
| choice : command -> command -> command
| one : command
| zero : command
.

Program Instance commandS : Setoid command.

Fixpoint formFreeVars form :=
  match form with
    | formFilter expr pred expr2 => exprFreeVars expr ∪ exprFreeVars expr2
    | formBuiltInFilter builtin exprs => fold_right FSetNat.union ∅ (map exprFreeVars exprs)
    | formLookupBySubject  expr pred var => exprFreeVars expr ∪ ﹛ var ﹜
    | formLookupByObject  var pred expr => ﹛ var ﹜ ∪ exprFreeVars expr
    | formLookupByPred  var pred var2 => ﹛ var ﹜ ∪ ﹛ var2 ﹜
    | formNot form => formFreeVars form
    | formExists v form => FSetNat.diff (formFreeVars form) (﹛ v ﹜)
    | comm ∧ comm2 => formFreeVars comm ∪ formFreeVars comm2
    | comm ∨ comm2 => formFreeVars comm ∪ formFreeVars comm2
    | formTrue => ∅
  end
.

Fixpoint cFreeVars comm :=
  match comm with
    | classical form => formFreeVars form
    | cNewAddr var  => ﹛ var ﹜
    | cLookupBySubject expr pred var => exprFreeVars expr ∪ ﹛ var ﹜
    | cLookupByObject var pred expr => ﹛ var ﹜ ∪ exprFreeVars expr
    | cLookupByPred var pred var2 => ﹛ var ﹜ ∪ ﹛ var2 ﹜
    | mutate expr pred expr2 => exprFreeVars expr ∪ exprFreeVars expr2
    | cDelete expr => exprFreeVars expr
    | seq comm comm2 => cFreeVars comm ∪ cFreeVars comm2
    | choice comm comm2 => cFreeVars comm ∪ cFreeVars comm2
    | one => ∅
    | zero => ∅
  end
.

Notation "𝟏" := (one) (at level 82).
Notation "𝟎" := (zero) (at level 82).
Notation "a ⊗ b" := (seq a b) (left associativity, at level 86).
Notation "a ⊕ b" := (choice a b) (left associativity, at level 87).




Module Semantics (B : BuiltInExpr) (BP : BuiltInPred) (S : Store) (H : Heap).
  Open Scope type_scope.
  Module EM := ExprModel B S.
  Import EM S H.

      
  Definition state A {AS : Setoid A} := @sh _ H.tS _ S.tS _ (lS) _ (lS _ S.tS) _ AS.

  Instance stateS {A} (AS : Setoid A) : Setoid (state A) := @shS _ H.tS _ S.tS _ (lS) _ (lS _ S.tS) _ AS.

  Instance state_Monad : @Monad (@state) (@stateS) := sh_Monad .

  Set Printing Implicit.

  Existing Instance alternative_Monoid.
  Existing Instance list_Alternative.
  Existing Instance sh_Alternative.
  Existing Instance listFunctor.
  Existing Instance list_Foldable.

  Definition stop {A} {AS : Setoid A}: state A := mempty.

  Definition choice {A} {AS : Setoid A}: H.lS _ (stateS AS) ~> stateS AS := fold.

(*  Existing Instance sh_Monad.
  Existing Instance store_Monad.*)

  Definition stopNone {A} {AS : Setoid A} :
    optionS AS ~> stateS AS.
    simple refine (injF (fun (a : option A) =>
                     match a with
                       | Some a' => ret @ a'
                       | None => stop
                     end) _).
    exact (@stateS).
    exact state_Monad.
    Lemma stopNone_1 : forall {A} {AS : Setoid A}, @Proper (option A -> @state A AS)
     (equiv  ==>
      equiv )
     (fun a : option A =>
      match a with
      | Some a' => ret @ a'
      | None => stop
      end).
    Proof.
      autounfold. intros. matchequiv H. simpl in H. rewritesr.
    Qed.
    apply stopNone_1.
  Defined.
  
  Definition stopFalse : boolS ~> stateS unitS.
    simple refine (injF (fun b : bool => if b then ret @ tt else stop) _).
  Defined.

  Definition evalExpr : exprS ~> stateS valS.
    simple refine (injF (fun expr1 => 
    getStore >>= ret ∘ (exprEval' @ expr1) >>= stopNone) _).
  Defined.
  
  



  Section LookupBySPOGeneric.
    Context (expr1 : expr) (pred1 : pred) (expr2 :expr).

    Definition lookupBySPOGeneric  : state unit :=
      (H.lookupBySPO
        <$> evalExpr @ expr1
        <*> pure @ pred1
        <*> evalExpr @ expr2
        <*> getHeap) >>= stopFalse.
  End LookupBySPOGeneric.

  
  Instance lookupBySPOGeneric_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) lookupBySPOGeneric.
  Proof.
    solve_proper.
  Qed.
  
  Definition updateStore (var1 : var) : valS ~> stateS unitS.
    refine (injF (fun val1 =>  
    
                    S.update @ var1 @ val1 <$> getStore >>= putStore) _).
  Defined.
  
  
  Section LookupBySubjectGeneric.
    Context
      (expr1 : expr) (pred1 : pred) (var1 : var).

    Definition lookupBySubjectGeneric  : state unit :=
      (H.lookupBySubject
         <$> evalExpr @ expr1
         <*> pure @ pred1
         <*> getHeap) >>= stopNone >>= updateStore var1
      .
  End LookupBySubjectGeneric.
  Instance lookupBySubjectGeneric_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) lookupBySubjectGeneric.
  Proof.
    solve_proper.    
  Qed.


  Definition branch (var1 : var) : H.lS _ valS ~> stateS unitS :=
    choice ∘ fmap @ (updateStore var1).
  

  Section LookupByObjectGeneric.
    Context
      (var1 : var) (pred1 : pred) (expr1 : expr).
    Definition lookupByObjectGeneric : state unit :=
      (H.lookupByObject
         @ pred1
         <$> evalExpr @ expr1
         <*> getHeap) >>= branch var1.
  End LookupByObjectGeneric.

  Instance lookupByObjectGeneric_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) lookupByObjectGeneric.
  Proof.
    solve_proper. 
  Qed.

  Definition branch2 (var1 var2 : var) : H.lS _ (valS ~*~ valS) ~> stateS unitS.
    refine (choice ∘ fmap @ (injF (fun val1 => updateStore var1 @ (fst val1) >> updateStore var2 @ (snd val1)) _)).
    Lemma branch2_1 : forall var1 var2, Proper (equiv ==> equiv)
                                           (fun val1 : val * val =>
                                              
                                              (updateStore var1 @ fst val1) >> (updateStore var2 @ snd val1)).
    Proof.
      intros. solve_proper.
    Qed.
    apply branch2_1.
  Defined.
  
  Section LookupByPredGeneric.
    Context
      (var1 : var) (pred1 : pred) (var2 : var).
    Definition lookupByPredGeneric : state unit :=
      ret @ (var1 =? var2) >>= stopFalse
          >> (H.lookupByPred @ pred1
                <$> getHeap) >>= branch2 var1 var2
  .
  End LookupByPredGeneric.
  Instance lookupByPredGeneric_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) lookupByPredGeneric.
  Proof.
    solve_proper.
  Qed.

(*  Definition retList (s : S.t) : projT1 (store0 H.St (listS S.St)) := ret @ (s :: nil). *)

  Existing Instance H.func.
  Existing Instance H.app.
  Definition retCont : unitS ~> @storeHeapS _ H.tS _ S.tS _ H.lS _ unitS.
    simple refine (injF3 (fun _ (h' : H.t) (s' : S.t) => (h', pure @ ((s', tt)::nil))) _).
    
  Definition run : stateS unitS  ~> stateS (lS _ S.tS).
    simple refine (injF4 (fun a c h s => a @ cont @ h @ s) _).
    Lemma run_1 : properF (fun s0 : S.t => retList s0).
    Proof.
      
      repeat autounfold. intros. simpl. arrequiv. split. constructor. auto. constructor. reflexivity.
    Qed.
    apply run_1.
  Defined.

  Instance run_Proper : Proper (equiv==> equiv) run.
  Proof.
    autounfold.  unfold run. intros. rewritesr.
  Qed.

(*  Definition listCase (a b : state S.t) : listS S.St ~> stateS S.St.
    simple refine (injF(fun l => if null l then
                                 a
                               else
                                 b) _).
    Lemma listCase_1 : forall  (a b : state S.t), properF (fun l : list S.t => if null l then a else b).
    Proof.
       unfold properF. intros. solve_proper. 
    Qed.
    apply listCase_1.
  Defined.

  Instance listCase_Proper : Proper (equiv ==> equiv ==> equiv) listCase.
  Proof.
    autounfold.  unfold listCase. intros. simpl. arrequiv.  destruct (null a). rewritesr. rewritesr.
  Qed.*)

  Section BuiltInFilterGeneric.
    Context
      (builtin : builtin) (args : list expr).
    Definition builtInFilterGeneric : state unit :=
      (BP.app @ builtin <$> mapM @ evalExpr @ args) >>= stopNone >>= stopFalse.
  End BuiltInFilterGeneric.
  Instance builtInFilterGeneric_Proper : Proper (equiv ==> equiv ==> equiv) builtInFilterGeneric.
  Proof.
    autounfold.    intros. unfold builtInFilterGeneric. rewritesr. 
  Qed.

  Section NegationGeneric.
    Context
      (a : state unit).
    Definition negationGeneric : state unit.
    simple refine (injF (fun s => run (a @ s) >>= listCase (ret @ s) stop) _).
    Lemma negationGeneric_1 : properF (fun s : S.t => bind @ run (a @ s) @ listCase (ret @ s) stop).
    Proof.
      unfold properF. solve_proper.
    Qed.
    apply negationGeneric_1.
    Defined.
  End NegationGeneric.
  Instance negationGeneric_Proper : Proper (equiv ==> equiv) negationGeneric.
  Proof.
    autounfold. intros. unfold negationGeneric. arrequiv. simpl_let. rewritesr. 
  Qed.
  
  Section ExistentialQuantificationGeneric.
    Context
      (a : S.St ~> stateS S.St) (v : var).
    Definition existentialQuantificationGeneric : S.St ~> stateS S.St.
    simple refine (injF (fun s => run (a @ (S.delete @ s @ v)) >>= listCase stop (ret @ s)) _).
Lemma existentialQuantificationGeneric_1 : properF (fun s => run (a @ (S.delete @ s @ v)) >>= listCase stop (ret @ s)).
Proof.
  unfold properF. solve_proper.
Qed.
apply existentialQuantificationGeneric_1.
Defined.
  End ExistentialQuantificationGeneric.
  Instance existentialQuantificationGeneric_Proper : Proper (equiv ==> equiv ==> equiv) existentialQuantificationGeneric.
  Proof.
    autounfold. intros. unfold existentialQuantificationGeneric. arrequiv. simpl_let. rewritesr.
  Qed.
  Section ClassicalGeneric.
    Context
      (a : S.St ~> stateS S.St).
    Definition classicalGeneric : S.St ~> stateS S.St.
    simple refine (injF (fun s => run (a @ s) >>= listCase stop (ret @ s)) _).
Lemma classicalGeneric_1 : properF (fun s => run (a @ s) >>= listCase stop (ret @ s)).
Proof.
  unfold properF. solve_proper.
Qed.
apply classicalGeneric_1.
Defined.
  End ClassicalGeneric.
  Instance classicalGeneric_Proper : Proper (equiv ==> equiv) classicalGeneric.
  Proof.
    autounfold. intros. unfold classicalGeneric. arrequiv. simpl_let. rewritesr.
  Qed.
  
Fixpoint _formReduce (form : formula) {struct form}: S.St ~> stateS S.St :=
   
    match form with
      | formFilter expr pred expr2  =>
        lookupBySPOGeneric expr pred expr2
      | formBuiltInFilter builtin args =>
        builtInFilterGeneric builtin args
      | formLookupBySubject  expr pred var =>
        lookupBySubjectGeneric   expr pred var
      | formLookupByObject var pred expr =>
        lookupByObjectGeneric  var pred expr 
      | formLookupByPred var pred var2 =>
        lookupByPredGeneric var pred var2
      | form0 ∧ form1 => 
        sh_plus @ (_formReduce form0) @ (_formReduce form1)
      | form0 ∨ form1 => 
        sh_times @ (_formReduce form0) @ (_formReduce form1)
      | ¬ form =>
        negationGeneric (_formReduce form)
      | ∃ v : form =>
        existentialQuantificationGeneric (_formReduce form)   v      
      | ⊤ => sh_one
    end.
  
Definition formReduce : formulaS ~> S.St ~~> stateS S.St.
  refine (injF (fun form => _formReduce form) _).
  Lemma formReduce_1 : properF (fun form : formula => _formReduce form).
  Proof.
    unfold properF. solve_proper.
  Qed.
  apply formReduce_1.
Defined.



Section MutateGeneric.
  Context
    (expr1 : expr) (pred0 : pred) (expr2 : expr).
  Definition mutateGeneric : S.St ~> stateS S.St.
    simple refine (injF (fun s => match ⟦ expr1 ⟧expr s with
          | Some addr =>
            match ⟦ expr2 ⟧expr s with
              | Some val =>
                lift @ get >>=
                     injF (fun h => lift @ (put @ ( h [ addr , pred0 ↦ val ] ))) _ >> ret @ s
              | None => stop
            end
          | None => stop
                                  end) _).
    Lemma mutateGeneric_1 : forall addr val,  properF (fun h : t => lift @ (put @ h [addr, pred0 ↦ val] )).
    Proof.
      unfold properF. intros. solve_proper.
    Qed.
    apply mutateGeneric_1.
    Lemma mutateGeneric_2 : forall pr, properF
     (fun s : S.t =>
      match (⟦ expr1 ⟧expr) s with
      | Some addr =>
          match (⟦ expr2 ⟧expr) s with
          | Some val =>
              andThen @
              (bind @ (lift @ get) @
               injF (fun h : t => lift @ (put @ h [addr, pred0 ↦ val] ))
                 (pr addr val)) @
              (ret @ s)
              
          | None => stop
          end
      | None => stop
      end)
.
    Proof.
      repeat autounfold. intros. matchequiv H. matchequiv H. evalproper. evalproper. evalproper. arrequiv. rewritesr. rewritesr. 
    Qed.
apply mutateGeneric_2.
  Defined.
End MutateGeneric.
Instance mutateGeneric_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) mutateGeneric.
Proof.
  solve_proper.
Qed.

Section NewAddrGeneric.
  Context
    (var1 : var).
  Definition newAddrGeneric : S.St ~> stateS S.St.
    simple refine (injF (fun s =>
                    lift @ get >>= injF (fun h => let (h', addr) := H.newAddr @ h in lift @ (put @ h') >> ret @ (s [ var1 ↦ addr ]s) ) _) _).
    Lemma newAddrGeneric_1 : forall s, properF
                                         (fun h : t => let (h', addr) := newAddr @ h in lift @ (put @ h') >> ret @ s [var1 ↦ addr ]s).
    Proof.
      repeat autounfold. intros. simpl_let. arrequiv.
    Qed.
    apply newAddrGeneric_1.
    Lemma newAddrGeneric_2 : forall pr, properF
     (fun s : S.t =>
      bind @ (lift @ get) @
      injF
        (fun h : t => let (h', addr) := newAddr @ h in lift @ (put @ h') >> ret @ s [var1 ↦ addr ]s)
        (pr s)).
    Proof.
      repeat autounfold. intros. simpl_let. arrequiv. destruct (newAddr @ a0). simpl. rewritesr.
    Qed.
    apply newAddrGeneric_2.
  Defined.
End NewAddrGeneric.
Instance newAddrGeneric_Proper : Proper (equiv ==> equiv) newAddrGeneric.
Proof.
  solve_proper.
Qed.

Section DeleteGeneric.
  Context
    (expr1 : expr).
  Definition deleteGeneric : S.St ~> stateS S.St.
    simple refine (injF (fun s =>          match ⟦ expr1 ⟧expr s with
          | Some val =>
            lift @ get >>= injF (fun h => if val ∈? (H.dom @ h) then
              lift @ (put @ (H.delete @ h @ val)) >> ret @ s
            else
              stop) _
          | None => stop
        end

                 ) _).
    Lemma deleteGeneric_1 : forall s val, properF
     (fun h : t =>
      if val ∈? (dom @ h)
      then andThen @ (lift @ (put @ (delete @ h @ val))) @ (ret @ s)
      else stop).
    Proof.
      repeat autounfold. intros. rewrite H.  destruct (val ∈? (dom @ y)). rewritesr. reflexivity.
    Qed.
    apply deleteGeneric_1.
    Lemma deleteGeneric_2 : forall pr, properF
     (fun s : S.t =>
      match (⟦ expr1 ⟧expr) s with
      | Some val =>
          bind @ (lift @ get) @
          injF
            (fun h : t =>
             if val ∈? (dom @ h)
             then andThen @ (lift @ (put @ (delete @ h @ val))) @ (ret @ s)
             else stop) (pr s val)
      | None => stop
      end).
    Proof.
      repeat autounfold. intros. matchequiv H. evalproper. unfold equiv, exp, arrSetoid, arrEquiv. intros. normalize. rewrite H0. destruct (v0 ∈? (dom @ a)). rewritesr. reflexivity. 
    Qed.
    apply deleteGeneric_2.
  Defined.
End DeleteGeneric.

Fixpoint _reduce (comm : command)  : S.St ~> stateS S.St :=
    match comm with
      | cLookupBySubject  expr pred var =>
        lookupBySubjectGeneric expr pred var
      | cLookupByObject var  pred expr =>
        lookupByObjectGeneric var  pred expr
      | cLookupByPred  var pred var2 =>
        lookupByPredGeneric var pred var2
      | form0 ⊗ form1 =>
          sh_times @ (_reduce form0) @ (_reduce form1)
      | form0 ⊕ form1 =>
        sh_plus @ (_reduce form0) @ (_reduce form1)
      | mutate expr pred0 expr2 =>
        mutateGeneric expr pred0 expr2
      | cNewAddr var =>
        newAddrGeneric var
      | cDelete expr =>
        deleteGeneric expr
      | 𝟏 => sh_one
      | 𝟎 => sh_zero
      | classical form =>
        classicalGeneric (formReduce @ form)
    end
  .



   

Definition reduce : commandS ~> S.St ~~> stateS S.St.
refine (injF (fun comm => _reduce comm) _).

Lemma reduce_1 : properF (fun comm : command => _reduce comm).
Proof.
  unfold properF. solve_proper.
Qed.
apply reduce_1.
Defined.


  (*
  Lemma form_store_non_interference_1 :
    forall v c s h,
      ~ (v ∈ formFreeVars c) ->
      let s's := formReduce c s h in
      allTrue (fun s' => s [ v ]s = s' [ v ]s) s's.
  Proof.
    intros. generalize dependent h. generalize dependent s. induction c.
    * all_cases.
    * all_cases.
    * all_cases. not_in v v0. rewrite (read_update_diff_var). auto.
    * all_cases. induction (H.lookupByObject h p n).
      + constructor.
      + split.
        - not_in v v0. repeat rewrite (read_update_diff_var). reflexivity.
        - apply IHl.
    * all_cases. induction (H.lookupByPred h p).
      + constructor.
      + split.
        - not_in v v0. not_in v v1. destruct a. repeat rewrite (read_update_diff_var). reflexivity.
        - apply IHl.
    * intros. simpl in s's. not_in_2 v (formFreeVars c1).
      assert (allTrue (fun s' => s [v ]s = s' [v ]s) (formReduce c1 s h)). apply (IHc1 H0 s h). clear IHc1. induction (formReduce c1 s h).
      + simpl in s's. constructor.
      + simpl in s's. unfold s's. unfold allTrue. rewrite map_app. apply and_app. destruct H1. split.
        - clear H0. not_in_2 v (formFreeVars c2). rewrite H1. apply (IHc2 H0 a h).
        - apply IHl. apply H2.
    * intros. simpl in s's. unfold s's. unfold allTrue. rewrite map_app. rewrite and_app. split.
      + not_in_2 v (formFreeVars c1). apply IHc1. auto.
      + not_in_2 v (formFreeVars c2). apply IHc2. auto.
    * intros. destruct (Nat.eq_dec v0 v).
      + rewrite <- e in *. simpl in s's. clear IHc e H v. induction (formReduce c (S.delete s v0) h).
        - constructor.
        - split.
          destruct (s[v0]s).
            rewrite read_update. reflexivity.
            rewrite read_delete. reflexivity.
          apply IHl.
      + simpl in H. not_in_2 v (formFreeVars c). unfold s's. simpl. assert (allTrue (fun s' => (S.delete s v0) [v ]s = s' [v ]s) (formReduce c (S.delete s v0) h)). apply IHc. apply H0. clear IHc H0 s's H. induction (formReduce c (S.delete s v0) h).
        - constructor.
        - destruct H1. rewrite read_delete_diff_var in H. split.
          destruct (s[v0]s).
            rewrite read_update_diff_var. assumption.
            rewrite read_delete_diff_var. assumption.
          apply IHl. apply H0.
    * intros. unfold s's. clear s's. simpl. destruct (null (formReduce c s h)).
      + compute. auto.
      + constructor.
    * intros. unfold s's. clear s's. compute. auto.
  Qed.
*)

 Definition non_inter_exprs s v val l := allTrue (fun e => EM.exprEval @ s @ e == EM.exprEval @  (s [v ↦ val ]s) @ e) l.

 Lemma expr_store_non_interference_2 :
    forall e s v val,
      ~ (v ∈ exprFreeVars e) ->
      EM.exprEval @ s @ e == EM.exprEval @ (s [v ↦ val]s) @ e.
  Proof.
    intros. apply expr_ind_2 with (p:=fun e=>EM.exprEval @ s @ e == EM.exprEval @ (s [v ↦ val ]s) @ e) (Q:=non_inter_exprs s v val).
    * intros. simpl. auto.
    * intros. unfold exprEval, _exprEval. normalize. rewrite read_update_diff_var. reflexivity. 
    * constructor.
    * intros. unfold non_inter_exprs in *. unfold allTrue in *. split.
      + assumption.
      + assumption.
    * intros. unfold exprEval, _exprEval.  normalize.
      match goal with
        | |- match ?a with _ => _ end == match ?b with _ => _ end => assert (a == b)
      end.
      + induction l.
        - simpl.        auto.
        - destruct H0. evalproper. evalproper. evalproper. auto. auto. 
      + match goal with
          | |- match ?a with _ => _ end == match ?b with _ => _ end => equiv a b H1
        end.
        simpl in H1. rewrite H1. reflexivity.
  Qed.

  Lemma lookupBySubject_store_non_interference_2 :
  forall v val expr pred var pr,
    v <> var ->
    ~ (v ∈ exprFreeVars expr) ->
    commutative ( lookupBySubjectGeneric expr pred var) ( injF (fun s => ret @ (s [v ↦ val]s) ) pr ).
Proof.
  intros. unfold commutative, lookupBySubjectGeneric. simpl times. unfold sh_times, compM, _compM. normalize. arrequiv. assert (_exprEval a expr == _exprEval (a [v ↦ val ]s) expr). rewrite (expr_store_non_interference_2 expr a v val H0). reflexivity. clear H0. equiv  (_exprEval a expr) (_exprEval (a [v ↦ val ]s) expr) H1. normalize. equiv (a1 [v0, pred]) (a1 [ v1, pred]) H1. normalize. rewrite (update_update_diff_var). rewritesr. 
Qed.
Lemma mapProper_cons :
    forall A B (SA : Setoid A) (SB : Setoid B) (f : SA ~> SB) (a : A) (l : list A), mapProper @ f @ (a :: l) = (f @ a) :: (mapProper @ f @ l).
  Proof.
    auto.
  Qed. 
  
  Lemma choice_cons : forall a l, choice (a :: l) = mappend @ (ret @ a) @ (choice l).
  Proof.
    auto.
  Qed.


Lemma lookupByObject_store_non_interference_2 :
  forall v val var pred expr pr,
    v <> var ->
    ~ (v ∈ exprFreeVars expr) ->
    commutative ( lookupByObjectGeneric var pred expr ) ( injF (fun s => ret @ s [v ↦ val]s ) pr ).
Proof.
  intros. unfold commutative, lookupByObjectGeneric. simpl times. unfold sh_times, compM, _compM. normalize.  simpl_equiv.  rewrite left_unit. simpl_equiv. 
  assert (exprEval @ a @ expr == exprEval @ (a [v ↦ val ]s) @ expr). rewrite (expr_store_non_interference_2 expr a v val H0). reflexivity. clear H0.
  equiv  (exprEval @ a @ expr) (exprEval @ (a [v ↦ val ]s) @ expr) H1. rewrites. clear H1 H0 v0. simpl_equiv.
  simpl bind. unfold contT_bindE. normalize. simpl lift. unfold store_bind, get, store_get. normalize. repeat rewrite let_intro.  normalize. simpl (fst _). simpl (snd _). repeat rewrite let_intro. normalize. simpl (fst _). simpl (snd _).  
  generalize (lookupByObject @ a1 @ pred @ v1). intros.  generalize a1. induction l.
  intros. simpl. split. constructor. reflexivity.
  generalize IHl. clear IHl.
  repeat rewrite mapProper_cons. repeat rewrite choice_cons. intros.  simpl. simpl_let. 
  rewrite (update_update_diff_var).  rewrite IHl.  simpl. split. reflexivity. reflexivity. 
Qed.

Lemma lookupByPred_store_non_interference_2 :
  forall v val var1 pred var2 pr,
    v <> var1 ->
    v <> var2 ->
    commutative (lookupByPredGeneric var1 pred var2) (injF (fun s => ret @ s [v ↦ val]s ) pr).
Proof.
  intros. unfold commutative, lookupByPredGeneric. simpl times. unfold sh_times, compM, _compM. normalize.  simpl_equiv.   rewrite left_unit. simpl_equiv. destruct (_ =? _).
  simpl. arrequiv. split. constructor. reflexivity.
  simpl_equiv.
  simpl bind. unfold contT_bindE. normalize. simpl lift. unfold store_bind, get, store_get. normalize. repeat rewrite let_intro.  normalize. simpl (fst _). simpl (snd _). repeat rewrite let_intro. normalize. simpl (fst _). simpl (snd _).  
  generalize (lookupByPred @ a1 @ pred). intros.  generalize a1. induction l.
  intros. simpl. split. constructor. reflexivity.
  generalize IHl. clear IHl.
  repeat rewrite mapProper_cons. repeat rewrite choice_cons. intros.  simpl. simpl_let.
  repeat rewrite (update_update_diff_var _ _ v _).
  rewrite IHl. simpl. split. reflexivity. reflexivity. 
Qed.

Lemma builtInFilter_store_non_interference_2 :
  forall v val builtin args pr,
    commutative  (builtInFilterGeneric builtin args) (injF (fun s => ret @ s [ v ↦ val]s ) pr) .
Proof. 
  intros. unfold commutative, lookupByPredGeneric. simpl times. unfold sh_times, compM, _compM. normalize. arrequiv. assert (_exprsEval a args == _exprsEval (a [v ↦ val ]s) args). induction args.
  reflexivity.
  unfold _exprsEval in *. fold consProper. rewrite mapM_cons.   simpl in *.  IHargs. 
Qed.

Lemma form_store_non_interference_2 :
    forall v c s h val,
      ~ (v ∈ formFreeVars c) ->
      map (fun s => s [v ↦ val ]s) (formReduce c s h) ≍ss formReduce c (s [ v ↦ val]s) h.
  Proof.
    intros. generalize dependent h. generalize dependent s. induction c.
    * intros.  simpl. unfold lookupSPOGeneric. not_in_2 v (exprFreeVars e). rewrite (expr_store_non_interference_2 e s v val H0). clear H0. not_in_2 v (exprFreeVars e0). rewrite (expr_store_non_interference_2 e0 s v val H0). clear H0. all_cases.
    * intros. simpl. assert (sequence (map (fun e : expr => (⟦ e ⟧expr) s) l) = sequence (map (fun e : expr => (⟦ e ⟧expr) (s [v ↦ val ]s)) l)).
      + induction l.
        - auto.
        - simpl. simpl in H. not_in_2 v (formFreeVars (formBuiltInFilter b l)). rewrite (IHl H0). clear H0. not_in_2 v (exprFreeVars a). setoid_rewrite (expr_store_non_interference_2 a s v val H0). all_cases.
      + rewrite H0. all_cases.
    * intros. simpl.  apply lookupBySubject_store_non_interference_2.  not_in v v0. auto. not_in_2 v (exprFreeVars e). auto.
    * intros. simpl. apply lookupByObject_store_non_interference_2. not_in v v0. auto. not_in_2 v (exprFreeVars e). auto.
    * intros. simpl. apply lookupByPred_store_non_interference_2. not_in v v0. auto. not_in v v1. auto.
    * intros. simpl in *. not_in_2 v (formFreeVars c1). setoid_rewrite <- (IHc1 H0). clear H0. rewrite map_map. induction (formReduce c1 s h).
        - simpl. reflexivity.
        - simpl. rewrite map_app. not_in_2 v (formFreeVars c2). rewrite <- (IHc2 H0). rewrite IHl. reflexivity.
    * intros. simpl. rewrite map_app. not_in_2 v (formFreeVars c1). rewrite <- (IHc1 H0). clear H0. not_in_2 v (formFreeVars c2). rewrite <- (IHc2 H0). reflexivity.
    * intros. simpl. rewrite map_map.  destruct (Nat.eq_dec v0 v).
      + rewrite <- e in *. clear e. setoid_rewrite (delete_update). induction (formReduce c (S.delete s v0) h).
        - simpl. reflexivity.
        - simpl. rewrite IHl. rewrite (read_update). destruct (s[v0]s).
                rewrite (S.update_update). reflexivity.
                rewrite (S.update_delete). reflexivity.
      + assert (Proper (eq_store ==> eq_store) (fun s' : S.t =>
          match (s [v ↦ val ]s) [v0 ]s with
          | Some val0 => s' [v0 ↦ val0 ]s
          | None => S.delete s' v0
          end)).
        - unfold Proper, respectful. intros. all_cases. setoid_rewrite H0. reflexivity. setoid_rewrite H0. reflexivity.
        - setoid_rewrite delete_update_diff_var. not_in_2 v (formFreeVars c). setoid_rewrite <- (IHc H1). clear H0 H1 H. rewrite map_map. induction (formReduce c (S.delete s v0) h).
          simpl. reflexivity.
          simpl. rewrite IHl. rewrite read_update_diff_var. destruct (s[v0]s).
            rewrite update_update_diff_var. reflexivity.
            rewrite delete_update_diff_var. reflexivity.
    * intros. simpl in *. rewrite <- (IHc H). destruct (formReduce c s h).
        + reflexivity.
        + reflexivity.
    * reflexivity.
  Qed.


  Ltac pair_eq ra rb a b := let H := fresh "H" in assert (liftPairR ra rb a b) as H; [ auto | destruct a; destruct b; destruct H].


  Definition nonInterference f v  := forall (s : S.t) (h : H.t) val,
    map (fun s => s [v ↦ val ]s) (fst (f s h)) ≍ss fst (f (s [ v ↦ val]s) h) /\
      snd (f s h) ≍ snd (f (s [ v ↦ val]s) h).

  Lemma comm_store_non_interference_2 :
    forall v c ret,
      ~ (v ∈ cFreeVars c) ->
      Proper (eq_store ==> eq_heap ==> liftPairR eq_stores eq_heap) ret ->
      nonInterference ret v ->
      nonInterference (fun s h => reduce c s h ret)  v.
   Proof.
     unfold nonInterference. intros. generalize dependent h. generalize dependent s. induction c.
     * intros.  not_in_2 v (formFreeVars f). simpl. rewrite <- (form_store_non_interference_2 _ _ _ _ _ H2). clear H2 H. destruct (H1 s h val). split.
       + all_cases.
       + all_cases.
     *  intros. not_in v v0. simpl. destruct (newAddr h). setoid_rewrite S.update_update_diff_var. apply (H1 (s [v0 ↦ v1 ]s) t0 val).
     * intros. simpl. split.
       + simpl. rewrite <- lookupBySubject_store_non_interference_2. not_in_2 v (exprFreeVars e). rewrite <- (expr_store_non_interference_2 _ _ _ _ H2). clear H2. destruct  (⟦ e ⟧expr s).  destruct (h [v1, p]). unfold concatMapM.  simpl. simpl_let. setoid_rewrite (update_update_diff_var _ _ v0 _). destruct (H1 (s [v0 ↦ v2 ]s) h val). split.
       rewrite map_app. apply app_Proper. auto. simpl. auto.
       auto.
       simpl.   split. reflexivity. reflexivity.
       simpl.  split. reflexivity.  reflexivity.
     * intros. simpl.  unfold lookupByObjectGeneric. not_in_2 v (exprFreeVars e). rewrite <- (expr_store_non_interference_2 _ _ _ _ H2). clear H2. not_in v v0. destruct ( (⟦ e ⟧expr) s). unfold concatMapM in *. generalize (H.lookupByObject h p v1). intro. generalize h. induction l.
        + intros. simpl. split. reflexivity. reflexivity.
        + intros. simpl. simpl_let. destruct (IHl (snd (ret0 ((s [v ↦ a ]s)) h0))). split.
          - rewrite map_app. apply app_Proper.
            destruct (H1 (s [v0 ↦ a ]s) h0 val). rewrite (update_update_diff_var _ _ v0 _). auto.
            simpl_let_2 H3. auto. reflexivity.
       +  simpl. reflexivity.
     * split.
       + simpl. unfold lookupByPredGeneric. not_in v v0. not_in v v1. clear H. all_cases. induction (H.lookupByPred h p).
         - auto.
         - elim_true. destruct a. repeat rewrite (update_update_diff_var _ _ v _). auto.
       + simpl. reflexivity.
     * split.
       + simpl. not_in_2 v (exprFreeVars e). rewrite <- (expr_store_non_interference_2 _ _ _ _ H0). clear H0. not_in_2 v (exprFreeVars e0). rewrite <- (expr_store_non_interference_2 _ _ _ _ H0). clear H0.  clear H. all_cases.
       + simpl. not_in_2 v (exprFreeVars e). rewrite <- (expr_store_non_interference_2 _ _ _ _ H0). clear H0. not_in_2 v (exprFreeVars e0). rewrite <- (expr_store_non_interference_2 _ _ _ _ H0). clear H0.  clear H. all_cases.
     * split.
       + simpl. not_in_2 v (exprFreeVars e). rewrite <- (expr_store_non_interference_2 _ _ _ _ H0). clear H H0.  all_cases.
       + simpl. not_in_2 v (exprFreeVars e). rewrite <- (expr_store_non_interference_2 _ _ _ _ H0). clear H H0.  all_cases.
     * split.
       + simpl. repeat rewrite let_intro. not_in_2 v (cFreeVars c1). destruct (IHc1 H0 s h). rewrite <- H1. rewrite <- H2. destruct (reduce c1 s h). simpl. clear H0 IHc1 H1 H2. generalize dependent t0. induction l.
         - reflexivity.
         - intros. simpl. not_in_2 v (cFreeVars c2). destruct (IHc2 H0 a t0). repeat rewrite let_intro. rewrite <- H1. rewrite <- H2. clear H0 IHc2 H1 H2. destruct (reduce c2 a t0). simpl in *. rewrite map_app. rewrite IHl. reflexivity.
       + simpl. repeat rewrite let_intro. not_in_2 v (cFreeVars c1). destruct (IHc1 H0 s h). setoid_rewrite <- H1. setoid_rewrite <- H2. destruct (reduce c1 s h). simpl. clear H0 IHc1 H1 H2. generalize dependent t0. induction l.
         - reflexivity.
         - intros. simpl. not_in_2 v (cFreeVars c2). destruct (IHc2 H0 a t0). repeat rewrite let_intro. setoid_rewrite <- H1.  setoid_rewrite <- H2. clear H0 IHc2 H1 H2. destruct (reduce c2 a t0). simpl in *. apply IHl.
     * split.
       + simpl. repeat rewrite let_intro. not_in_2 v (cFreeVars c1). destruct (IHc1 H0 s h). rewrite <- H2. rewrite <- H1. clear IHc1 H0 H1 H2. destruct (reduce c1 s h). simpl. rewrite map_app.  not_in_2 v (cFreeVars c2). destruct (IHc2 H0 s t0). rewrite <- H1. reflexivity.
       + simpl. repeat rewrite let_intro. not_in_2 v (cFreeVars c1). destruct (IHc1 H0 s h). rewrite <- H2. rewrite <- H1. clear IHc1 H0 H1 H2. destruct (reduce c1 s h). simpl. not_in_2 v (cFreeVars c2). destruct (IHc2 H0 s t0). rewrite <- H2. reflexivity.
     * intros. simpl. split. reflexivity. reflexivity.
     * intros. simpl. split. reflexivity. reflexivity.
   Qed.


End Semantics.

(* example *)

Module Examples (B : BuiltInExpr) (BP : BuiltInPred) (S : Store) (H : Heap).
  Module EM := ExprModel B S.
  Module SEM := Semantics B BP S H.
  Import S H EM SEM.
  Definition sequence : addr :=  0.
  Definition SEQUENCE : pred := 0.
  Definition curr : var := 1.

  Definition plus : builtin := 0.
  Notation "a .+ b" := (appExpr plus (List.cons a (List.cons b List.nil))) (at level 25, left associativity).
  Notation "? a" := (varExpr a) (at level 20).
  Notation "@ a" := (valExpr a) (at level 20).

  Definition incProg := cLookupBySubject (@ sequence) SEQUENCE curr ⊗
                                     mutate (@ sequence) SEQUENCE (? curr .+ @ 1).
  Notation "∅s" := S.empty.

  Notation "∅h" := H.empty.
  Open Scope nat_scope.

  Axiom builtin_plus : forall x y, B.app plus (x :: y :: List.nil) = Some (x + y).


  Lemma reduce_incProg :
    forall s h n,
        reduce incProg (s[ curr ↦ n ]s) ( h [ sequence,SEQUENCE ↦ n ]) ≍ssh
        ( s [ curr ↦ n ]s :: List.nil,  h [ sequence,SEQUENCE ↦ n + 1]).
  Proof.
    intros. simpl. unfold lookupBySubjectGeneric. unfold EM.exprEval. rewrite (lookup_update).  unfold mapM.  rewrite (read_update_diff_var). rewrite read_update. rewrite (builtin_plus).  simpl. split.
    * setoid_rewrite S.update_update. reflexivity.
    * rewrite update_update. reflexivity.
  Qed.

  Definition sem_eq c1 c2 := forall s h, reduce c1 s h  ≍ssh reduce c2 s h.
  Notation "a ≌ b" := (sem_eq a b) (at level 99).
  Lemma app_nil : forall A (l : list A), l ++ nil = l.
  Proof.
    induction l. auto. simpl. rewrite IHl. auto.
  Qed.

  Instance sem_eq_Reflexive : Reflexive sem_eq.
  Proof.
    unfold Reflexive, sem_eq. intros. reflexivity.
  Qed.

  Instance sem_eq_Transitive : Transitive sem_eq.
  Proof.
    unfold Transitive, sem_eq. intros. transitivity (reduce y s h). auto. auto.
  Qed.

  Instance sem_eq_Symmetric : Symmetric sem_eq.
  Proof.
    unfold Symmetric, sem_eq. intros. symmetry. auto.
  Qed.

  Program Instance seq_eq_Equivalence : Equivalence sem_eq.
  Instance seq_Proper : Proper (sem_eq ==> sem_eq ==> sem_eq) seq.
  Proof.
    unfold Proper, respectful, sem_eq. intros. simpl. simpl_let. split.
    * rewrite H. destruct (reduce y s h). simpl.  generalize dependent t0. induction l.
      + simpl. intros.  reflexivity.
      + simpl. intros. simpl_let. rewrite H0. rewrite IHl. reflexivity.
    * rewrite H. destruct (reduce y s h). simpl.  generalize dependent t0. induction l.
      + simpl. intros.  reflexivity.
      + simpl. intros. simpl_let. rewrite H0. rewrite IHl. reflexivity.
  Qed.

  Instance choice_Proper : Proper (sem_eq ==> sem_eq ==> sem_eq) choice.
  Proof.
    unfold Proper, respectful, sem_eq. intros. simpl. simpl_let. split.
    * rewrite H. destruct (reduce y s h). simpl. rewrite H0. reflexivity.
    * rewrite H. destruct (reduce y s h). simpl. rewrite H0. reflexivity.
  Qed.


    Lemma seq_associative :
    forall c c2 c3, c ⊗c2 ⊗c3  ≌ c ⊗(c2 ⊗c3).
  Proof.
    unfold sem_eq. intros. simpl.    destruct (reduce c s h). simpl_let. split.
    * generalize t0. induction l.
      + reflexivity.
      + intros. simpl. simpl_let. rewrite <- IHl. clear IHl. destruct (reduce c2 a t1). simpl. repeat rewrite mapM_app. simpl_let. rewrite concat_app. unfold mapM. simpl. generalize t2. induction l0.
        - reflexivity.
        - intros. simpl. simpl_let. rewrite <- IHl0.
    Lemma near_semiring_0:
    forall c, 𝟏 ⊗ c ≌ c.
  Proof.
    unfold sem_eq. induction c.
    * all_cases.
    * all_cases.
    * all_cases.
    * simpl. intros. split. rewrite app_nil. reflexivity.  reflexivity.
    * simpl. intros. split. rewrite app_nil. reflexivity.  reflexivity.
    * all_cases.
    * all_cases.
    * simpl in *. intros.  repeat rewrite let_intro. simpl. split. rewrite app_nil. reflexivity.  reflexivity.
    * simpl in *.   intros. repeat rewrite let_intro. simpl. split. rewrite app_nil. reflexivity. reflexivity.
    * all_cases.
    * all_cases.
  Qed.

  Lemma near_semiring_1:
    forall c, c ⊗𝟏  ≌ c.
  Proof.
    unfold sem_eq. induction c.
    * all_cases.
    * all_cases.
    * all_cases.
    * simpl.  intros. induction (lookupByObjectGeneric s h v p e).
      + simpl. split. reflexivity.  reflexivity.
      + simpl. repeat rewrite let_intro in *. simpl in *. destruct IHl. split. rewrite H. reflexivity. auto.
    * simpl.  intros. induction (lookupByPredGeneric s h v p v0).
      + simpl. split. reflexivity.  reflexivity.
      + simpl. repeat rewrite let_intro in *. simpl in *. destruct IHl. split. rewrite H. reflexivity.    auto.
    * all_cases.
    * all_cases.
    * simpl in *.  intros. repeat rewrite let_intro. simpl. split. specialize (IHc1 s h). destruct (reduce c1 s h). repeat rewrite let_intro in IHc1. simpl in IHc1. destruct IHc1. simpl. generalize dependent t0. induction l.
      + simpl. auto.
      + intros. simpl. specialize (IHc2 a t0). destruct (reduce c2 a t0). repeat rewrite let_intro in IHc2. simpl in IHc2. destruct IHc2. repeat rewrite let_intro. simpl. rewrite <- (IHl t1). rewrite app_nil. all_cases.
    * all_cases.
    * all_cases.
    * all_cases.
    * all_cases.
    * all_cases.
    * all_cases.
    * all_cases.
    * all_cases.
    * all_cases.
    * all_cases.
    * all_cases.




End Examples.
