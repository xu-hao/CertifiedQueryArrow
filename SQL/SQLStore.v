Require Import Assert Command Definitions Algebra.Monoid Expr Algebra.SetoidCat Algebra.Maybe Tactics Algebra.ListUtils Algebra.Functor Algebra.Applicative Algebra.Alternative Algebra.FoldableFunctor Algebra.PairUtils Algebra.Maybe Algebra.Monad Algebra.Lens.Lens Utils SetoidUtils SQL Lista GenUtils Pointed.
Require Import Coq.Structures.DecidableTypeEx List SetoidClass PeanoNat FMapWeakList Basics.

Module SQLStore <: Store SQLValType.
  
  Definition t := store.
  Instance tS : Setoid t := storeS.

  Import SQLValType.
  Existing Instance maybe_Pointed.

  Definition read : varS ~> storeS ~~> maybeS valS := lista_nthS.

  Definition update : varS ~> valS ~~> storeS ~~> storeS.
    refine (injF3 (fun var1 val1 s => lista_updateS @ var1 @ s @ (Some val1)) _).
    Lemma update_1 : Proper (equiv ==> equiv ==> equiv ==> equiv)
     (fun (var1 : nat) (val1 : sqlVal) (s : lista (option sqlVal)) =>
      lista_updateS @ var1 @ s @ Some val1).
    Proof.
      autounfold. intros. rewritesr.  
    Qed.
    apply update_1.
  Defined.
  
  Definition delete : varS ~> storeS ~~> storeS.
    refine (injF2 (fun var1 s => lista_updateS @ var1 @ s @ None) _).
    Lemma delete_1 : Proper (equiv ==> equiv ==> equiv)
     (fun (var1 : nat) (s : lista (option sqlVal)) =>
      lista_updateS @ var1 @ s @ None).
    Proof.
      autounfold. intros. rewritesr. 
    Qed.
    apply delete_1.
  Defined.

  Definition emptyStore : store := listaCons _ nil.

  Lemma eq_store : forall s1 s2, (forall v, read @ v @ s1 == read @ v @ s2) -> s1 == s2.
  Proof.
    intros. simpl. destruct s1, s2. simpl in *. generalize H. clear H. apply list_ind_2 with (l1:=l) (l2:=l0).
    - intros.  simpl.  auto.
    - intros. pose (H0 0). simpl. split.
      + destruct a. tauto. reflexivity.
      + apply H. intros. pose (H0 (S v)). simpl in m0. destruct v.  simpl. auto. simpl. auto.
    - intros. pose (H0 0). simpl. split.
      + destruct a. tauto. reflexivity.
      + apply H. intros. pose (H0 (S v)). simpl in m0. destruct v.  simpl. auto. simpl. auto.
    - intros. split.
      + specialize (H0 0). auto.
      + apply H. intros. specialize (H0 (S v)). auto.
  Qed.
  
  Lemma read_update :
    forall s var val,
      read @ var @ (update @ var @ val @ s) == Some val.
  Proof.
    intros. simpl. rewrite lista_nth_lista_update. reflexivity.
  Qed.

  Lemma delete_update :
    forall s var val,
      delete @ var @ (update @ var @ val @ s) == delete @ var @ s.
  Proof.
    intros. simpl. rewrite lista_update_lista_update. reflexivity. 
  Qed.

  Lemma update_delete :
    forall s var1 val1,
       update @ var1 @ val1 @ (delete @ var1 @ s) == update @ var1 @ val1 @ s.
  Proof.
    intros. simpl. rewrite lista_update_lista_update. reflexivity. 
  Qed.
  
  Lemma update_update :
    forall s var2 val1 val2,
      update @ var2 @  val2 @ (update @ var2 @ val1 @ s) == update @ var2 @ val2 @ s.
  Proof.
    intros. simpl. rewrite lista_update_lista_update. reflexivity. 
  Qed.
  
  Lemma read_update_diff_var :
    forall s var1 var2 val1,
      var1 <> var2 ->
      read @ var2 @ (update @ var1 @ val1 @ s) == read @ var2 @ s.
  Proof.
    intros. simpl. rewrite lista_nth_lista_update_diff_index.  reflexivity. auto. 
  Qed.
  
  
  
  Lemma read_delete_diff_var :
    forall s var1 var2,
      var1 <> var2 ->
      read @ var2 @ (delete @ var1 @ s) == read @ var2 @ s.
  Proof.
    intros. simpl. rewrite lista_nth_lista_update_diff_index.  reflexivity. auto. 
  Qed.

  Lemma update_update_diff_var :
    forall s var1 var2 val1 val2,
      var1 <> var2 ->
      update @ var2 @ val2 @ (update @ var1 @ val1 @ s) == update @ var1 @ val1 @ (update @ var2
                                                                  @ val2 @ s).
  Proof.
    intros. simpl.  rewrite lista_update_lista_update_diff_index. reflexivity. auto. 
  Qed.

  Lemma delete_update_diff_var :
    forall s var1 var2 val1,
      var1 <> var2 ->
      delete @ var2 @ (update @ var1 @ val1 @ s) == update @ var1 @ val1 @ (delete @ var2 @ s).
  Proof.
    intros. simpl.  rewrite lista_update_lista_update_diff_index. reflexivity.  auto. 
  Qed.
    
  Lemma read_delete :
    forall s var,
      read @ var @ (delete @ var @ s) == None.
  Proof.
    intros. simpl. rewrite lista_nth_lista_update. reflexivity. 
  Qed.

  Lemma read_empty:
    forall var,
      read @ var @ emptyStore == None.
  Proof.
    intros. simpl. destruct var. reflexivity. reflexivity.
  Qed.

End SQLStore.
