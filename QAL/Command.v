Require Import Algebra.Assert Algebra.Utils Algebra.Monad SetoidUtils Algebra.SetoidCat.ListUtils Algebra.SetoidCat Algebra.Monad.StoreHeap Algebra.Monad.ContT Algebra.NearSemiRing Algebra.Monoid Tactics Expr Definitions Algebra.FoldableFunctor Algebra.SetoidCat.PairUtils Algebra.Functor Algebra.Alternative Algebra.SetoidCat.MaybeUtils Algebra.Monad.Maybe Algebra.Applicative Algebra.SetoidCat.BoolUtils Algebra.SetoidCat.UnitUtils Algebra.Monoid.BoolUtils Algebra.Monoid.Alternative Algebra.Alternative.List Algebra.Functor.List Algebra.FoldableFunctor.List Algebra.Monad.Utils.

Require Import Coq.Lists.List PeanoNat RelationClasses Relation_Definitions Morphisms Coq.Program.Basics SetoidClass.

Definition  commutative {A} {SA : Setoid A} {nsr : @NearSemiRing _ SA} (a b : A ) := times @ a @ b == times @ b @ a.

Section Command.
  Context
    {primitiveCommand : Type}
    {aggregator : Type}.

  Inductive command :=
  | cPrimitive : primitiveCommand -> command
  | cSeq : command -> command -> command
  | cChoice : command -> command -> command
  | cOne : command
  | cZero : command
  | cAggregate : aggregator -> command -> command
  .

  Program Instance commandS : Setoid command.

End Command.

Notation "𝟏" := (cOne) (at level 82).
Notation "𝟎" := (cZero) (at level 82).
(* Notation "∃ b" := (cExists b) (at level 83).
Notation "¬ a" := (cNot a) (at level 80). *)
Notation "a ⊗ b" := (cSeq a b) (left associativity, at level 86).
Notation "a ⊕ b" := (cChoice a b) (left associativity, at level 87).

Module Type AbstractStore.
  Parameter t : Type.
  Parameter tS : Setoid t.
End AbstractStore.

Module Type AbstractHeap.
  Parameter t : Type.
  Parameter tS : Setoid t.
  Parameter l : forall A, (Setoid A) -> Type.
  Parameter lS : forall A (AS : Setoid A), Setoid (l A AS).
  Parameter l_Alternative : @Alternative l lS.
  Parameter l_Functor : @Functor l lS.
  Parameter l_Foldable : @FoldableFunctor l lS l_Functor.
  Parameter l_Applicative : @Applicative l lS l_Functor.
End AbstractHeap.  

Module Types (S : AbstractStore) (H : AbstractHeap).
  Definition state A {AS : Setoid A} : Type := @sh _ H.tS _ S.tS _ (H.lS) _ unitS _ AS.

  Instance stateS {A} (AS : Setoid A) : Setoid (state A) := @shS _ H.tS _ S.tS _ (H.lS) _ unitS _ AS.
  Instance state_Monad : @Monad (@state) (@stateS) := sh_Monad.
End Types.

Module Type PrimitiveCommand (S : AbstractStore) (H : AbstractHeap).
  Module TS := Types S H.
  Import TS.
  Parameter primitiveCommand : Type.
  Parameter primitiveCommandS : Setoid primitiveCommand.
  Parameter freeVarsPrimitiveCommand : primitiveCommandS ~> varSetS.
  Parameter interpretPrimitiveCommand : primitiveCommandS ~> stateS unitS.
End PrimitiveCommand.

Module Type Aggregator (S : AbstractStore) (H : AbstractHeap).
  Module TS := Types S H.
  Import TS.
  Parameter aggregator : Type.
  Parameter aggregatorS : Setoid aggregator.
  Parameter freeVarsAggregator : aggregatorS ~> varSetS ~~> varSetS.
  Parameter interpretAggregator : aggregatorS ~> H.lS _ S.tS ~~> stateS unitS.
End Aggregator.

Module CommandModel (S : AbstractStore) (H : AbstractHeap) 
       (PC : PrimitiveCommand S H) (AGG: Aggregator S H).
  Open Scope type_scope.
  Module TS := Types S H.
  Import S H PC AGG TS.
  Definition command := @command primitiveCommand aggregator.
  Instance commandS : Setoid command := @commandS primitiveCommand aggregator.
      
  Fixpoint cFreeVars (comm : command) :=
    match comm with
      | cPrimitive pc => freeVarsPrimitiveCommand @ pc
      | cSeq comm comm2 => cFreeVars comm ∪ cFreeVars comm2
      | cChoice comm comm2 => cFreeVars comm ∪ cFreeVars comm2
      | cOne => ∅
      | cZero => ∅
      | cAggregate agg form => freeVarsAggregator @ agg @ cFreeVars form
    end
  .


  Definition stateStoreHeapS := @storeHeapS _ H.tS _ S.tS _ (lS) _ unitS.

  Definition runState {A B} {AS : Setoid A} {BS : Setoid B} : stateS AS ~> (AS ~~> stateStoreHeapS) ~~> stateStoreHeapS := runSh. 

  Existing Instance alternative_Monoid.
  Existing Instance l_Alternative.
  Existing Instance sh_Alternative.
  Existing Instance l_Functor.
  Existing Instance l_Foldable.

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
      autounfold. intros. matchequiv. simpl in H. rewritesr.
    Qed.
    apply stopNone_1.
  Defined.
  
  Definition stopFalse : boolS ~> stateS unitS.
    simple refine (injF (fun b : bool => if b then ret @ tt else stop) _).
  Defined.

  Existing Instance bool_and_Monoid.

  Definition null_l {A} {AS : Setoid A} : H.lS _ AS ~> boolS.
    simple refine (injF (fun l => fold @ (constS _ @ false <$> l)) _).
    exact boolS.
    apply H.lS.
    exact H.l_Functor.
    exact H.l_Foldable.
    exact bool_and_Monoid.
    apply H.lS.
    exact H.l_Functor.
    Lemma null_l_1 : forall A AS, Proper (equiv ==> equiv)
     (fun l0 : l A AS =>
      fold @
            (constS _ @ false <$> l0)).
    Proof.
      intros. solve_proper.
    Qed.
    apply null_l_1.
  Defined.

  Definition notNull_l {A} {AS : Setoid A} : H.lS _ AS ~> boolS := negbS ∘ null_l .

  Definition stopNotNull {A} {AS : Setoid A} : H.lS _ AS ~> stateS unitS.
    simple refine (injF (fun l => if null_l @ l then ret @ tt else stop) _).
    intros. apply stateS.
    exact state_Monad.
    Lemma stopNotNull_1 : forall A AS, @Proper (l A AS -> @state unit unitS)
     (@equiv (l A AS) (lS A AS) ==>
      @equiv (@state unit unitS) (@stateS unit unitS))
     (fun l0 : l A AS =>
      if @null_l A AS @ l0
      then
       @ret state (fun (A0 : Type) (AS0 : Setoid A0) => @stateS A0 AS0)
         state_Monad unit unitS @ tt
      else @stop unit unitS).
    Proof.
      intros. solve_proper.
    Qed.
    apply stopNotNull_1.
  Defined.

  Definition stopNull {A} {AS : Setoid A} : H.lS _ AS ~> stateS unitS.
    simple refine (injF (fun l => if notNull_l @ l then ret @ tt else stop) _).
    intros. apply stateS.
    exact state_Monad.
    Lemma stopNull_1 : forall A AS, Proper (equiv ==> equiv)
     (fun l0 : l A AS =>
      if notNull_l @ l0
      then
       @ret state (fun (A0 : Type) (AS0 : Setoid A0) => @stateS A0 AS0)
         state_Monad unit unitS @ tt
      else @stop unit unitS).
    Proof.
      intros. solve_proper.
    Qed.
    apply stopNull_1.
  Defined.
  
  Definition branchStore : H.lS _ S.tS ~> stateS unitS :=
    choice ∘ (fmap @ putStore).

  (* we define a run function that retrives all stores *)
  Definition _retCont : S.tS ~> H.lS _ (S.tS ~*~ unitS).
    simple refine (injF (fun (s' : S.t) => pure @ (s', tt) : H.l (S.t * unit) (S.tS ~*~ unitS)) _).
    apply H.lS.
    apply H.l_Functor.
    apply H.l_Applicative.
    Lemma _retCont_1 : @Proper (S.t -> l (S.t * unit) (S.tS ~*~ unitS))
     (@equiv S.t S.tS ==>
      @equiv (l (S.t * unit) (S.tS ~*~ unitS))
        (lS (S.t * unit) (S.tS ~*~ unitS)))
     (fun s' : S.t =>
      @pure l lS H.l_Functor H.l_Applicative (S.t * unit) (S.tS ~*~ unitS) @ (s', tt)
      :
        l (S.t * unit) (S.tS ~*~ unitS)).
    Proof.
      solve_proper.
    Qed.
    apply _retCont_1.
  Defined.
  
  Definition retCont : unitS ~> stateStoreHeapS :=
    constS unitS @ (curryS @ (idS *** _retCont)).

 

  Definition extractStores : stateS unitS ~> H.tS ~~> S.tS ~~> H.tS ~*~ H.lS _ S.tS.
    simple refine (injF3 (fun a h s => (idS *** fmap @ fstS) @ (runSh @ a @ retCont @ h @ s)) _).
    apply H.tS.
    apply H.lS.
    apply H.l_Functor.
    Lemma extractStores_1 : Proper (equiv ==> equiv ==> equiv ==> equiv)
     (fun (a : (unitS ~~> storeHeapS unitS) ~> storeHeapS unitS) 
        (h : t) (s : S.t) =>
      (idS *** fmap @ fstS) @ (runSh @ a @ retCont @ h @ s)).
    Proof.
      solve_proper.
    Qed.
    apply extractStores_1.
  Defined.
  
  Definition run : stateS unitS  ~> stateS (H.lS _ S.tS).
    simple refine (injF4 (fun (a : state unit) (c : H.lS _ S.tS ~> stateStoreHeapS) (h : H.t) (s : S.t) => let (h', r) := (extractStores @ a @ h @ s) in c @ r @ h' @ s) _).
    Lemma run_1 : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv)
     (fun (a : state unit) (c : lS S.t S.tS ~> stateStoreHeapS) 
        (h : t) (s : S.t) =>
      let (h', r) := extractStores @ a @ h @ s in c @ r @ h' @ s).
    Proof.
      repeat autounfold. intros. simpl_let. simpl_let. rewritesr. 
    Qed.
    apply run_1.
  Defined.


  Section PrimitiveCommandGeneric.
    Context
      (pc : primitiveCommand).
    Definition primitiveCommandGeneric : state unit :=
      (interpretPrimitiveCommand
         @ pc).
  End PrimitiveCommandGeneric.
  Instance primitiveCommand_Proper : Proper (equiv ==> equiv) primitiveCommandGeneric.
  Proof.
    solve_properS primitiveCommandGeneric.
  Qed.

  Section AggregateGeneric.
    Context
      (agg : aggregator)
      (a : state unit).
    Definition aggregateGeneric : state unit := run @ a >>= interpretAggregator @ agg.
  End AggregateGeneric.
  Instance aggregateGeneric_Proper : Proper (equiv ==> equiv ==> equiv) aggregateGeneric.
  Proof.
    solve_properS aggregateGeneric.
  Qed.
  

  
  Existing Instance sh_NearSemiRing.

Fixpoint _reduce (comm : command)  : state unit :=
    match comm with
      | cPrimitive pc  =>
        primitiveCommandGeneric pc
      | form0 ⊗ form1 =>
          times @ (_reduce form0) @ (_reduce form1)
      | form0 ⊕ form1 =>
        plus @ (_reduce form0) @ (_reduce form1)
      | 𝟏 => one
      | 𝟎 => zero
      | cAggregate agg form =>
        aggregateGeneric agg (_reduce form)
    end
  .



   

  Definition reduce : commandS ~> stateS unitS.
    refine (injF _reduce _).

  Defined.


End CommandModel.

Module SemanticEquivalence 
       (S : AbstractStore) (H : AbstractHeap) (PC : PrimitiveCommand S H)
       (AGG : Aggregator S H).
  Module CM := CommandModel S H PC AGG.
  Import S H PC AGG CM.
  Definition sem_eq c1 c2 := reduce @ c1  == reduce @ c2.
  
  Notation "a ≌ b" := (sem_eq a b) (at level 99).

  Instance sem_eq_Reflexive : Reflexive sem_eq.
  Proof.
    unfold Reflexive, sem_eq. intros. reflexivity.
  Qed.

  Instance sem_eq_Transitive : Transitive sem_eq.
  Proof.
    unfold Transitive, sem_eq. intros. transitivity (reduce @ y). auto. auto.
  Qed.

  Instance sem_eq_Symmetric : Symmetric sem_eq.
  Proof.
    unfold Symmetric, sem_eq. intros. symmetry. auto.
  Qed.

  Program Instance seq_eq_Equivalence : Equivalence sem_eq.

  Instance semEqS : Setoid command :=
    {
      equiv := sem_eq
    }
  .

  Instance cSeq_Proper : Proper (sem_eq ==> sem_eq ==> sem_eq) cSeq.
  Proof.
    unfold Proper, respectful, sem_eq. intros. unfold reduce, _reduce. normalize. fold _reduce. rewritesr. 
  Qed.

  Definition cSeqS : semEqS ~> semEqS ~~> semEqS := injF2 cSeq _.

  Instance cChoice_Proper : Proper (sem_eq ==> sem_eq ==> sem_eq) cChoice.
  Proof.
    unfold Proper, respectful, sem_eq. intros. unfold reduce, _reduce. normalize. fold _reduce. rewritesr. 
  Qed.

  Definition cChoiceS : semEqS ~> semEqS ~~> semEqS := injF2 cChoice _.

  Instance semEq_NearSemiRing : @NearSemiRing command semEqS.
  Proof.
    exists (cOne) (cZero) (cSeqS) (cChoiceS).
    intros. simpl equiv. unfold sem_eq, reduce, _reduce. normalize. fold _reduce. apply times_left_unit.
    intros. simpl equiv. unfold sem_eq, reduce, _reduce. normalize. fold _reduce. apply times_right_unit.
    intros. simpl equiv. unfold sem_eq, reduce, _reduce. normalize. fold _reduce. apply times_associativity.
    intros. simpl equiv. unfold sem_eq, reduce, _reduce. normalize. fold _reduce. apply plus_left_unit.
    intros. simpl equiv. unfold sem_eq, reduce, _reduce. normalize. fold _reduce. apply plus_right_unit.
    intros. simpl equiv. unfold sem_eq, reduce, _reduce. normalize. fold _reduce. apply plus_associativity.
    intros. simpl equiv. unfold sem_eq, reduce, _reduce. normalize. fold _reduce. apply times_left_absorb.
    intros. simpl equiv. unfold sem_eq, reduce, _reduce. normalize. fold _reduce. apply times_left_distributivity.
  Defined.

End SemanticEquivalence.


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
