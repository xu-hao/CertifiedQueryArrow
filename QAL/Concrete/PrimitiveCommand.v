Require Import QAL.Assert Algebra.Utils Algebra.Monad SetoidUtils Algebra.SetoidCat.ListUtils Algebra.SetoidCat Algebra.Monad.StoreHeap Algebra.Monad.ContT Algebra.NearSemiRing Algebra.Monoid Tactics QAL.Definitions Algebra.FoldableFunctor Algebra.SetoidCat.PairUtils Algebra.Functor Algebra.Alternative Algebra.SetoidCat.MaybeUtils Algebra.Monad.Maybe Algebra.Applicative Algebra.SetoidCat.BoolUtils Algebra.SetoidCat.UnitUtils Algebra.Monoid.BoolUtils Algebra.Monoid.Alternative Algebra.Alternative.List Algebra.Functor.List Algebra.FoldableFunctor.List Algebra.Monad.Utils QAL.Concrete.Definitions QAL.AbstractStore QAL.AbstractHeap QAL.Command Algebra.Traversable.List Algebra.Functor.Monad Algebra.Applicative.Monad.

Require Import Coq.Lists.List PeanoNat RelationClasses Relation_Definitions Morphisms Coq.Program.Basics SetoidClass.

Section PrimitiveCommand.
  Context
    {literal : Type}
    {pred : Type}
  .
  
  Inductive term :=
  | termVar : var -> term
  | termVal : literal -> term
  .

  Program Instance termS : Setoid term.

  Import FSetNatNotations. 

  Definition _termFreeVars (t : term) : FVarSet.t :=
    match t with
        | termVal _ => ∅
        | termVar v => ﹛ v ﹜ 
    end
  .
  
  Instance _termFreeVars_Proper : Proper (equiv ==> equiv) _termFreeVars.
  Proof.
    solve_proper.
  Qed.

  Definition termFreeVars := injF _termFreeVars _.

  Inductive qalPrimitiveCommand :=
  | pcInsert : pred -> list term -> qalPrimitiveCommand
  | pcDelete : pred -> list term -> qalPrimitiveCommand
  | pcInsertProp : pred -> list term -> list term -> qalPrimitiveCommand
  | pcDeleteProp : pred -> list term -> list term -> qalPrimitiveCommand
  | pcAtomic : pred -> list term -> qalPrimitiveCommand
  .

  Program Instance qalPrimitiveCommandS : Setoid qalPrimitiveCommand.

  Definition tlFreeVars (tl : list term) :=
            fold_right (fun t  fv =>
                      (termFreeVars @ t) ∪ fv) ∅ tl
  .

  Definition _qalPrimitiveCommandFreeVars (pc : qalPrimitiveCommand) : FVarSet.t :=
    match pc with
      | pcInsert _ tl => tlFreeVars tl
      | pcDelete _ tl => tlFreeVars tl
      | pcInsertProp _ ktl ptl => tlFreeVars ktl ∪ tlFreeVars ptl
      | pcDeleteProp _ ktl ptl => tlFreeVars ktl ∪ tlFreeVars ptl
      | pcAtomic _ tl => tlFreeVars tl
    end
  .
  
  Instance _qalPrimitiveCommandFreeVars_Proper : Proper (equiv ==> equiv) _qalPrimitiveCommandFreeVars.
   Proof.
    solve_proper.
  Qed.

  Definition qalPrimitiveCommandFreeVars := injF _qalPrimitiveCommandFreeVars _.
  
End PrimitiveCommand.

Module Type Literal (VT : ValType).
  Import VT.
  Parameter literal : Type.
  Parameter literalS : Setoid literal.
  Parameter interpretLiteral : literalS ~> valS.
End Literal.

Module QALPrimitiveCommand (PT : PredType) (VT : ValType)
       (L : Literal VT) (S : AbstractStore VT) (H : AbstractHeap PT VT) : PrimitiveCommand PT VT S H.
  Open Scope type_scope.
  Module TS := Types PT VT S H.
  Module CA := CommandAux PT VT S H.
  Import PT VT L S H TS CA.

  Definition freeVarsPrimitiveCommand := @qalPrimitiveCommandFreeVars literal pred.

  Definition qalTerm := @term literal.
  Instance qalTermS : Setoid qalTerm := @termS literal.

  Instance argumentVal_Proper : Proper (equiv ==> equiv) (argumentVal val).
  Proof.
    unfold Proper, respectful. intros. auto. 
  Qed.
  
  Definition argumentValS := injF (argumentVal val) _.
  Definition _evalTerm (t : term) : state (argument val) :=
    match t with
      | termVal l => ret @ (argumentValS @ (interpretLiteral @ l))
      | termVar v => getStore >>= ret ∘ (caseMaybeS @ argumentValS @ argumentVar val v) ∘ (S.read @ v)  
    end
  .

  Instance _evalTerm_Proper : Proper (equiv ==> equiv) _evalTerm.
  Proof.
    solve_proper.
  Qed.

  Definition evalTerm := injF _evalTerm _.

  Existing Instance sh_Monad.
  Existing Instance monadFunctor.
  Existing Instance monad_Applicative.
  Definition evalTermList : listS (@termS literal) ~> stateS (listS (argumentS _ valS)) := mapM @ evalTerm.

  Definition _evalTermVal (t : term) : state ( val) :=
    match t with
      | termVal l => ret @ (interpretLiteral @ l)
      | termVar v => getStore >>= ret ∘ (S.read @ v) >>= stopNone  
    end
  .

  Instance _evalTermVal_Proper : Proper (equiv ==> equiv) _evalTermVal.
  Proof.
    solve_proper.
  Qed.

  Definition evalTermVal := injF _evalTermVal _.

  Definition evalTermListVal : listS (@termS literal) ~> stateS (listS valS) := mapM @ evalTermVal.

(*  (* update var in store *)
  Definition updateVar (var1 : var) : valS ~> stateS unitS.
    refine (injF (fun val1 =>  
    
                    updateStore @ (S.update @ var1 @ val1)) _).
    Lemma updateVar_1 : forall var1, Proper (equiv ==> equiv)
                                            (fun val1 : val => updateStore @ (S.update @ var1 @ val1)).
    Proof.
      intros. solve_proper.
    Qed.
    apply updateVar_1.
  Defined.

  Definition updateVar2 (var1 : var) : H.tS ~*~ valS ~> stateS unitS.
    simple refine (injF (fun ha : H.t * val  => let (h', addr) := ha in putHeap @ h' >> updateVar var1 @ addr) _).
    intros. apply stateS.
    exact state_Monad.
    Lemma updateVar2_1 : forall var1, Proper (equiv  ==> equiv)
     (fun ha : t * val =>
      let (h', addr) := ha in
      andThen @ (putHeap @ h') @ (updateVar var1 @ addr)).
    Proof.
      autounfold. intros. rewrites. destruct x,y. destruct H. rewritesr.
    Qed.
    apply updateVar2_1.    
  Defined.
  *)
(*  Definition branch (var1 : var) : H.lS _ addrS ~> stateS unitS :=
    choice ∘ fmap @ (updateVar var1 ∘ addrToVal) .
  
  Definition branch2 (var1 var2 : var) : H.lS _ (addrS ~*~ valS) ~> stateS unitS.
    refine (choice ∘ fmap @ (injF (fun val1 => updateVar var1 @ (addrToVal @ (fst val1)) >> updateVar var2 @ (snd val1)) _)).
    Lemma branch2_1 : forall var1 var2, Proper (equiv ==> equiv)
                                           (fun val1 : addr * val =>
                                              
                                              (updateVar var1 @ (addrToVal @ (fst val1))) >> (updateVar var2 @ snd val1)).
    Proof.
      intros. solve_proper.
    Qed.
    apply branch2_1.
  Defined.
  *)


  Definition updateStore2 : listS (varS ~*~ valS) ~> S.tS ~~> S.tS :=
    flipS @ (fold_rightS @ (uncurryS @ S.update)).
  
  Definition _unionWithCurrStore (s : list (var * val)) : state unit :=
    updateStore @ (updateStore2 @ s).

  Instance _unionWithCurrStore_Proper : Proper (equiv ==> equiv) _unionWithCurrStore.
  Proof.
    solve_properS _unionWithCurrStore.
  Qed.
  
  Definition unionWithCurrStore : listS (varS ~*~ valS) ~> stateS unitS := injF _unionWithCurrStore _.

  Definition _lookupAtom (p : pred) (tl : list (@term literal)) : state (H.l (list (var * val)) _) :=
    (H.lookup @ p)
        <$> (evalTermList @ tl)
        <*> getHeap.

  Instance _lookupAtom_Proper : Proper (equiv ==> equiv ==> equiv) _lookupAtom.
  Proof.
    solve_properS _lookupAtom.
  Qed.
  Definition lookupAtom := injF2 _lookupAtom _.

  Section LookupGeneric.
    Context (p : pred) (tl : list (@term literal)).

    Definition lookupGeneric : state unit :=
      lookupAtom @ p @ tl >>= branchVal >>= unionWithCurrStore.
  End LookupGeneric.
  Instance lookupGeneric_Proper : Proper (equiv ==> equiv ==> equiv) lookupGeneric.
  Proof.
    solve_properS lookupGeneric.    
  Qed.

  
  Section InsertGeneric.
    Context
      (p : pred) (tl : list (@term literal)).

    Definition insertGeneric : state unit :=
      (H.insert @ p
         <$> (evalTermListVal @ tl)
         <*> getHeap) >>= stopNone >>= putHeap.
  End InsertGeneric.
  Instance insertGeneric_Proper : Proper (equiv ==> equiv ==> equiv) insertGeneric.
  Proof.
    solve_properS insertGeneric.
  Qed.

  Section DeleteGeneric.
    Context
      (p : pred) (tl : list (@term literal)).

    Definition deleteGeneric : state unit :=
      (H.delete @ p
         <$> evalTermListVal @ tl 
         <*> getHeap) >>= stopNone >>= putHeap.
  End DeleteGeneric.

  Instance DeleteGeneric_Proper : Proper (equiv ==> equiv ==> equiv) deleteGeneric.
  Proof.
    solve_properS deleteGeneric.
  Qed.

  Section InsertPropGeneric.
    Context
      (p : pred) (ktl ptl : list (@term literal)).

    Definition insertPropGeneric : state unit :=
      (H.insertProp @ p
         <$> (evalTermListVal @ ktl)
         <*> (evalTermListVal @ ptl)
         <*> getHeap) >>= stopNone >>= putHeap.
  End InsertPropGeneric.
  Instance insertPropGeneric_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) insertPropGeneric.
  Proof.
    solve_properS insertPropGeneric.
  Qed.

  Section DeletePropGeneric.
    Context
      (p : pred) (ktl ptl : list (@term literal)).

    Definition deletePropGeneric : state unit :=
      (H.deleteProp @ p
         <$> (evalTermListVal @ ktl)
         <*> (evalTermListVal @ ptl)
         <*> getHeap) >>= stopNone >>= putHeap.
  End DeletePropGeneric.

  Instance DeletePropGeneric_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) deletePropGeneric.
  Proof.
    solve_properS deletePropGeneric.
  Qed.

Fixpoint _reduce (pc : qalPrimitiveCommand)  : state unit :=
    match pc with
      | pcInsert pred tl =>
        insertGeneric pred tl
      | pcDelete pred tl =>
        deleteGeneric pred tl
      | pcInsertProp pred ktl ptl =>
        insertPropGeneric pred ktl ptl
      | pcDeleteProp pred ktl ptl =>
        deletePropGeneric pred ktl ptl
      | pcAtomic pred tl =>
        lookupGeneric pred tl
    end
  .

  Definition reduce : (@qalPrimitiveCommandS literal pred ) ~> stateS unitS := injF _reduce _.
  Definition primitiveCommand := @qalPrimitiveCommand literal pred.
  Definition primitiveCommandS := @qalPrimitiveCommandS literal pred.
  Definition interpretPrimitiveCommand := reduce.
End QALPrimitiveCommand.


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
(*
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
*)


(* example *)

(* Module Examples (B : BuiltInExpr) (BP : BuiltInPred) (S : Store) (H : Heap).
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

  




End Examples. *)
