Require Import Definitions Algebra.Monoid Expr Algebra.SetoidCat Algebra.Maybe Tactics Algebra.ListUtils Algebra.Functor Algebra.Applicative Algebra.Alternative Algebra.FoldableFunctor Algebra.PairUtils Algebra.Maybe Algebra.Monad Algebra.Lens.Lens Algebra.Lens.MaybeLens ListLens Utils SetoidUtils SQL Pointed SQLUtils Lista Matrixp.
Require Import Coq.Structures.DecidableTypeEx List SetoidClass PeanoNat FMapWeakList Basics Coq.Arith.Compare_dec Coq.Arith.Le.

Definition insertRow (table : nat) (h : database) : database :=
  caseMaybeS
    @ (cycle24S @ maybeRowSetter @ table @ (SomeS @ (lista_repeatS @ point)) @ h
                ∘ lista_findaS maybe_row_equiv_dec)
    @ h
    @ (rowsGetter @ table @ h).


Instance insertRow_Proper : Proper (equiv ==> equiv ==> equiv) insertRow.
Proof.
  solve_properS insertRow.
Qed.

Definition insertRowS : natS ~> databaseS ~~> databaseS := injF2 insertRow _.

Definition deleteRow table rowid (h : database) : database :=
  caseMaybeS
    @ (constS _ @ (maybeRowSetter @ table @ rowid @ None @ h))
    @ h
    @ (rowsGetter @ table @ h).

Instance deleteRow_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) deleteRow.
Proof.
  solve_properS deleteRow.
Qed.

Definition deleteRowS : natS ~> natS ~~> databaseS ~~> databaseS := injF3 deleteRow _.

Definition newRowId table (h : database) : option nat :=
  caseMaybeS 
    @ (SomeS ∘ lista_findaS maybe_row_equiv_dec)
    @ None
    @ (rowsGetter @ table @ h).

Instance newRowId_Proper : Proper (equiv ==> equiv ==> equiv) newRowId.
Proof.
  solve_properS newRowId.
Qed.

Definition newRowIdS : natS ~> databaseS ~~> maybeS natS := injF2 newRowId _.

Open Scope nat_scope.

Definition addrToTableS := @fstS nat nat _ _.  

Definition addrToRowS := @sndS nat nat _ _. 

Definition predToTableS : sqlPredS ~> natS := @fstS nat nat _ _.

Definition predToColS : sqlPredS ~> natS := @sndS nat nat _ _.

Import SQLValType.


Definition getNewAddr (type1 : sqlType) (h : database) :  maybe sqlAddr.
  refine (newRowIdS @ type1 @ h >>= injF (fun rowid => ret @ (type1, rowid)) _).
Defined.

Definition noneFalse : boolS ~> maybeS unitS :=
  injF (fun b : bool => if b then ret @ tt else None) _.

Definition fromMaybeS {A} {AS : Setoid A} : AS ~> maybeS AS ~~> AS.
  simple refine (injF2 (fun a b => match b with
                                     | Some b' => b'
                                     | None => a
                                   end) _).
  Lemma fromMaybeS_1 : forall {A} {AS : Setoid A}, Proper (equiv ==> equiv ==> equiv)
     (fun (a : A) (b : option A) =>
      match b with
      | Some b' => b'
      | None => a
      end).
  Proof.
    autounfold. intros. matchequiv. auto. auto.
  Qed.
  apply fromMaybeS_1.
Defined.


Definition eqbS := injF2 Nat.eqb _.

Definition checkAddrPred addr pred1 :=
  noneFalse @ (eqbS
     @ (addrToTableS @ addr)
     @ (predToTableS @ pred1) ).

Instance checkAddrPred_Proper : Proper (equiv ==> equiv ==> equiv) checkAddrPred.
Proof.
  solve_properS checkAddrPred.
Qed.

Definition checkAddrPredS := injF2 checkAddrPred _.

Definition _newAddr (type1 : sqlType) h :=
  pairS
    @ (insertRowS @ type1 @ h)
    <$> (getNewAddr type1 h).

Definition newAddr : sqlTypeS ~> databaseS ~~> maybeS (databaseS ~*~ sqlAddrS).
  simple refine (injF2 _newAddr _).
  Lemma newAddr_1 : Proper (equiv ==> equiv ==> equiv) _newAddr.
  Proof.
    autounfold. intros. unfold _newAddr, getNewAddr. evalproper. rewritesr. bindproper. rewritesr. auto. 
  Qed.
  apply newAddr_1.
Defined.

Definition _filterVal val1 val2  :=
  if SQLValType.equiv_dec val1 val2 then true else false.

Instance _filterVal_Proper : Proper (equiv ==> equiv ==> equiv) _filterVal.
Proof.
  autounfold. intros. unfold _filterVal. rewrite H, H0. destruct (equiv_dec y y0). reflexivity. reflexivity. 
Qed.

Definition filterVal := injF2 _filterVal _.

Definition _filterSomeVal val1 :=
  caseMaybeS
    @ (filterVal @ val1)
    @ (false).

Instance _filterSomeVal_Proper : Proper (equiv ==> equiv) _filterSomeVal.
Proof.
  solve_properS _filterSomeVal. 
Qed.

Definition filterSomeVal := injF _filterSomeVal _.

Definition _filterByCol ci val1 row  :=
  match nth_error row ci with
    | Some n => filterVal @  n @ val1
    | _ => false
  end.

Instance _filterByCol_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _filterByCol.
Proof.
  autounfold. intros. unfold _filterByCol. matchequiv. rewritesr. 
Qed.

Definition filterByCol := injF3 _filterByCol _.


(*
  Definition _filterNone {A} {AS : Setoid A} (val1 : maybe A)  :=
    match val1 with
      | Some n => true
      | None => false
    end.

  Instance _filterNone_Proper A AS : Proper (equiv ==> equiv) (@_filterNone A AS).
  Proof.
    autounfold. intros. unfold _filterNone. matchequiv. 
  Qed.

  Definition filterNone {A AS} := injF (@_filterNone A AS) _.
 *)

Definition getAddr : natS ~> natS ~~> sqlAddrS  :=pairS.


Module SQLTypeType <: TypeType.
  Definition type := sqlType.
  Instance typeS : Setoid type := sqlTypeS.
End SQLTypeType.

Module SQLPredType <: PredType.
  Definition pred := sqlPred.
  Instance predS : Setoid pred := sqlPredS.
End SQLPredType.

Module SQLAddrType <: AddrType.
  Definition addr := sqlAddr.
  Instance addrS : Setoid addr := sqlAddrS.
End SQLAddrType.

Module SQLHeap <: Heap SQLTypeType SQLAddrType SQLPredType SQLValType.
  
  Definition t := database.
  Program Instance tS : Setoid t.

  Definition _delete addr h : t := deleteRowS
                                    @ (addrToTableS @ addr)
                                    @ (addrToRowS @ addr)
                                    @ h.

  
  Instance _delete_Proper : Proper (equiv ==> equiv ==> equiv) _delete.
  Proof.
    solve_properS _delete.
  Qed.

  Definition delete : sqlAddrS ~> tS ~~>  tS := injF2 _delete _.

  Definition _read addr pred1 h : maybe sqlVal :=
    checkAddrPredS @ addr @ pred1 >>
                  (cellGetter
                     @ (addrToTableS @ addr)
                     @ (addrToRowS @ addr)
                     @ (predToColS @ pred1)
                     @ h).

  Instance _read_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _read.                     
  Proof.
    solve_properS _read.
  Qed.

  Definition read := injF3 _read _.

  Definition _update addr pred1 val1 h :  database :=
    caseMaybeS
      @ idS
      @ h
      @ (checkAddrPredS @ addr @ pred1 >>
                  ret @ (cellSetter
                     @ (addrToTableS @ addr)
                     @ (addrToRowS @ addr)
                     @ (predToColS @ pred1)
                     @ val1 
                     @ h)).
  
  Instance _update_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv) _update.
  Proof.
    solve_properS _update.
  Qed.
  
  Definition update := injF4 _update _.
  
  Definition emptyH : database := nil.
  Definition union : tS ~> tS ~~> tS := unionDatabases.

  Definition _allocated addr h : Prop :=
    caseMaybeS
      @ (caseMaybeS
           @ (constS _ @ True)
           @ False)
      @ False
      @ (maybeRowGetter
           @ (addrToTableS @ addr)
           @ (addrToRowS @ addr)
           @ h).

  Instance _allocated_Proper : Proper (equiv ==> equiv==>equiv) _allocated.
  Proof.
    solve_properS _allocated.
  Qed.

  Definition allocated := injF2 _allocated _.

  Definition l A (AS : Setoid A) := list A.
  Instance lS A (AS : Setoid A) : Setoid (l A AS) := listS AS.
  Instance func : @Functor l lS := listFunctor.
  Instance alt : @Alternative l lS := list_Alternative.
  Instance foldable : @FoldableFunctor l lS func := list_Foldable.
  Instance app : @Applicative l lS func := list_Applicative.

  Definition _lookupByObject pred1 val1 h : list sqlVal :=
    let t := predToTableS @ pred1 in
    caseMaybeS
      @ (mapS @ (vAddrS ∘ getAddr @ t) ∘ lista_filter_indexS @ (filterSomeVal @ val1))
      @ nil
      @ (colGetter @ t @ (predToColS @ pred1) @ h).

  Instance _lookupByObject_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _lookupByObject.
  Proof.
    solve_properS _lookupByObject.
  Qed.

  Definition lookupByObject   : sqlPredS ~> sqlValS ~~> tS ~~> lS _ sqlValS := injF3 _lookupByObject _.
  
  Definition _lookupByPred pred1 h : list (sqlVal * sqlVal) :=
    let t := predToTableS @ pred1 in
    caseMaybeS
      @ (mapS @ ((vAddrS ∘ getAddr @ t) *** idS) ∘ lista_filter_indexS')
      @ nil                  
      @ (colGetter @ t @ (predToColS @ pred1) @ h).

  Instance _lookupByPred_Proper : Proper (equiv ==> equiv ==> equiv) _lookupByPred.
  Proof.
    solve_properS _lookupByPred.
  Qed.

  Definition lookupByPred   : sqlPredS ~> tS ~~> lS _ (sqlValS ~*~ sqlValS) := injF2 _lookupByPred _.
  Definition _readType addr h : maybe sqlType :=
     caseMaybeS
      @ (caseMaybeS
           @ (constS _ @ Some (addrToTableS @ addr))
           @ None)
      @ None
      @ (maybeRowGetter
           @ (addrToTableS @ addr)
           @ (addrToRowS @ addr)
           @ h).

  Instance _readType_Proper : Proper (equiv ==> equiv ==> equiv) _readType.
  Proof.
    solve_properS _readType.
  Qed.

  Definition readType :
    sqlAddrS ~> databaseS ~~> maybeS sqlTypeS := injF2 _readType _.
  
  Definition _predOfType pred1 type1 (h : database) :=
    type1 == predToTableS @ pred1 /\ ltMaybeS @ (predToColS @ pred1) @ (widthGetter @ type1 @ h).

  Instance _predOfType_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _predOfType.
  Proof.
    solve_properS _predOfType.
  Qed.

  Definition predOfType :
    sqlPredS ~> sqlTypeS ~~> databaseS ~~> iff_setoid := injF3 _predOfType _.
  
  Definition _typeOfHeap type1 (h : database) :=
    type1 < length h.

  Instance _typeOfHeap_Proper : Proper (equiv ==> equiv ==> equiv) _typeOfHeap.
  Proof.
    solve_properS _typeOfHeap.
  Qed.

  Definition typeOfHeap : sqlTypeS  ~> databaseS ~~> iff_setoid := injF2 _typeOfHeap _.    
             
  Notation "heap [ val , pred ]" := (read @ val @ pred @ heap) (at level 11).
  Notation "heap [ val , pred  ↦  val2 ]  " := (update @ val @ pred @ val2 @ heap) (at level 11).

  Definition extractAddr := extractAddrS.
  Definition addrToVal := vAddrS.
  Require Import Coq.Arith.Minus.
  

(* Lemma _read_cons_1 :
    forall addr pred1 table1 h ,
      pred1 < _width table1 ->
      addrToTable addr (table1 :: h) = 0 ->
      _read0 addr pred1 (table1 :: h) == tableCellGetter (addrToRow addr (table1 :: h)) pred1 @ table1.
  Proof.
    intros. unfold _read0.
    assert (checkAddrPred addr pred1 (table1 :: h) == Some tt).
    {
      unfold checkAddrPred, addrToTableS. normalize. rewrite H0. unfold predToTableS. normalize. unfold _predToTable. destruct table1. simpl (0+n). destruct (lt_dec pred1 n). simpl. auto.
      tauto. 
    }
    rewrite H1. unfold addrToTableS. normalize. rewrite H0. unfold predToColS.    normalize. destruct table1. unfold _predToTable. simpl (0 + _).  destruct (lt_dec pred1 n).
    - assert (forall A (AS : Setoid A) (x : A), Some x == ret @ x).
    {
      reflexivity.
    }
    rewrite H2. unfold andThen, compM.  normalizecomp. unfold constS. normalize. rewrite associativity. rewrite left_unit. normalize. simpl  (sndS <$> Some (0, pred1 - 0)). rewrite <- (minus_n_O pred1). unfold addrToRowS. normalize. generalize (addrToRow addr (matrixpCons nat n l0 :: h)). intros.
    simpl fmap. unfold monad_fmap. normalizecomp. unfold ap. unfold comp2S. normalize. rewrite uncurry_fmap_prod. rewrite fmap_eval.
    assert (forall A (AS : Setoid A) (x : A), Some x == ret @ x).
    {
      reflexivity.
    }
    rewrite H3. rewrite left_unit. normalize. 
    assert (forall A (AS : Setoid A) (x : A), (ret @ x : maybe A) == pure @ x).
    {
      reflexivity.
    }
    rewrite H4. rewrite ap_pure. rewrite fmap_pure. rewrite <- cellGetter_comp. rewrite <- H4.  normalize_monad.
    simpl (tableGetter @ 0 @ (matrixpCons nat n l0 :: h)). rewrite H3.
    match goal with
      | |- ret @ ?a >>= ?f == _ =>
        rewrite (left_unit _ _ _ _ a f)
    end. normalize.
    match goal with
      | |- ?a >>= ?f == _ =>
        rewrite (right_unit_equiv _ _ _ a f)
    end.
    reflexivity. simpl. arrequiv.
    
  - tauto.
    Grab Existential Variables.
    solve_proper.
  Qed.
  *)

  Lemma widthGetter_cons : forall n a l, widthGetter @ (S n) @ (a :: l) = widthGetter @ n @ l.
  Proof.
    intros. simpl. unfold _nthTraversal, _nthTraversal'. f_equal. simpl. matchequiv. rewrite ConstIso'_iso. f_equal. rewrite ConstIso'_iso. f_equal.
  Qed.

  Lemma maybeRowGetter_cons : forall n r a l, maybeRowGetter @ (S n) @ r @ (a :: l) = maybeRowGetter @ n @ r @ l.
  Proof.
    intros. simpl. unfold _nthTraversal, _nthTraversal'. f_equal. simpl. matchequiv. rewrite ConstIso'_iso. f_equal. rewrite ConstIso'_iso. f_equal.
  Qed.

  Lemma read_cons : forall n n2 r c a l, read @ (S n, r) @ (S n2, c) @ (a :: l) == read @ (n, r) @ (n2, c) @ l.
  Proof.
    intros. Opaque equiv.  simpl. unfold _read. rewrite <- cellGetter_comp. unfold tableGetter, _tableGetter. normalize. unfold previewS. normalizecomp. unfold preS, pre, viewS, view. normalizecomp. simpl (addrToTableS @ _). pose (nthTraversal_cons_S_Const _ _ n a l0 _ _ _ (pre0 @ ConstIsoS (maybeS tableS) (maybeS tableS))) as e. rewrite e. clear e. simpl (addrToRowS @ _).  simpl (predToColS @ _).  rewrite <- cellGetter_comp. reflexivity. Transparent equiv.
  Qed.

  Require Import Coq.Arith.Lt.
  
  Lemma eq_heap0 :
    forall (h1 h2 : t) ,
      (forall t, typeOfHeap @ t @ h1 <-> typeOfHeap @ t @ h2) ->
      (forall p t, predOfType @ p @ t @ h1 <-> predOfType @ p @ t @ h2) ->
      (forall v, allocated @ v @ h1 == allocated @ v @ h2) ->
      (forall v p, read @ v @ p @ h1 == read @ v @ p @ h2) ->
      h1 == h2.
  Proof.
    
    intros. generalize H H0 H1 H2. clear H H0 H1 H2. apply list_ind_2 with (l1:=h1)(l2:=h2).
    -    reflexivity.
    - intros. destruct (H0 0). simpl in H5. unfold _typeOfHeap in H5. simpl in H5. assert (0 < S(length b)). apply lt_O_Sn. pose (H5 H6) as e. inversion e.
    - intros. destruct (H0 0). simpl in H4. unfold _typeOfHeap in H4. simpl in H4. assert (0 < S(length b)). apply lt_O_Sn. pose (H4 H6) as e. inversion e.
    - intros. constructor.
      + clear H. destruct a, c. destruct (lt_eq_lt_dec n n0) as [[l2 | e] | ?].
        * destruct n0. inversion l2. specialize (H1 (0, n0) 0). destruct H1 as [H1 H4]. clear H1 H0 H2 H3. compute in H4. assert (0 = 0 /\ S n0 <= S n0) as e. auto. specialize (H4 e). destruct H4. pose (nat_int _ _ l2) as e0. contradiction. 
        * rewrite e in *. clear n e H0 H1. split. auto. destruct l0, l1. unfold _rows. generalize H2 H3. clear H2 H3. apply list_ind_2 with (l1:=l0) (l2:=l1).
          {
            intros. destruct o, o0.
            {
              clear H2. simpl. destruct l2, l3.  simpl. specialize (H3 (0, 0)). Opaque equiv. simpl in H3.  unfold _read in H3. simpl in H3.  Transparent equiv.
              split. apply equiv_lista. intros. specialize (H3 (0, ci)). simpl in H3.  auto. auto.
            }
            {
              clear H3. specialize (H2 (0,0)). compute in H2. tauto.
            }
            {
              clear H3. specialize (H2 (0,0)). compute in H2. tauto.
            }
            {
              simpl.  auto.
            }
          }
          {
            intros. split.
            {
              clear H. destruct o, o0. apply equiv_nth_equiv_lista_truncate.
              {
                reflexivity.
              }
              {
                intros. 
                clear H2.  simpl. specialize (H3 (0, 1 + length b0) (0, ci)).
                Opaque equiv lista_nth length plus map lista_truncate.
                compute in H3.
                Transparent equiv lista_nth length plus map lista_truncate.
                rewrite map_cons in H3.
                rewrite lista_nth_ge_length in H3.
                rewrite lista_nth_ge_length in H3.
                simpl in H3.
                rewrite eq_lista_nth_lista_truncate_lt_lista_nth in H3.
                rewrite eq_lista_nth_lista_truncate_lt_lista_nth in H3.  auto. auto. auto. simpl. rewrite length_map. constructor.
                rewrite length_map. apply Nat.le_0_l.
              }
              {
                clear H3. specialize (H2 (0, 1 + length b0)). destruct H2.  clear H0. simpl in H. unfold _allocated in H. Opaque lista_nth. simpl in H.  rewrite lista_nth_ge_length in H. rewrite lista_nth_ge_length in H.  simpl in H. tauto. simpl. rewrite length_map. auto. apply Nat.le_0_l.
                
              }
              {
                clear H3. specialize (H2 (0, 1 + length b0)). destruct H2.  clear H. simpl in H0. unfold _allocated in H0. Opaque lista_nth. simpl in H0.  rewrite lista_nth_ge_length in H0. rewrite lista_nth_ge_length in H0.  simpl in H0. tauto. apply Nat.le_0_l. simpl. rewrite length_map. auto. 
              }
              {
                reflexivity.
              }
            }
            { 
              split.
              {
                clear H. destruct a, o. apply equiv_nth_equiv_lista_truncate.
                {
                  reflexivity.
                }
                {
                  intros. 
                  clear H2.  simpl. specialize (H3 (0,0) (0, ci)).
                  Opaque equiv lista_nth length plus map lista_truncate.
                  compute in H3.
                  Transparent equiv lista_nth length plus map lista_truncate.
                  rewrite map_cons in H3.
                  simpl in H3.
                  rewrite eq_lista_nth_lista_truncate_lt_lista_nth in H3.
                  rewrite eq_lista_nth_lista_truncate_lt_lista_nth in H3.  auto. auto. auto. 
                }
                {
                  clear H3. specialize (H2 (0, 0)). destruct H2.  clear H. simpl in H0. unfold _allocated in H0. simpl in H0.  tauto.                   
                }
                {
                  clear H3. specialize (H2 (0, 0)). destruct H2.  clear H0. simpl in H. unfold _allocated in H. simpl in H.  tauto. 
                }
                {
                  reflexivity.
                }
              }
              {
                apply H.
                {
                  intros. destruct v. destruct n.
                  {
                    specialize (H2 (0, S n1)). simpl in H2. unfold _allocated in H2. simpl in H2. simpl. unfold _allocated. simpl. destruct n1. exact H2. exact H2.
                  }
                  {
                    specialize (H2 (S n, n1)). simpl in H2. unfold _allocated in H2. simpl in H2. unfold _nthTraversal, _nthTraversal' in H2. simpl in H2. simpl. unfold _allocated. simpl. unfold _nthTraversal, _nthTraversal'. simpl.  exact H2. 
                  }
                }
                {
                  clear H H2. intros. destruct v. destruct n.
                  {
                    specialize (H3 (0, S n1) p). simpl in H3. unfold _read in H3. simpl in H3. simpl. unfold _read. simpl. destruct n1. exact H3. exact H3.
                  }
                  {
                    specialize (H3 (S n, n1) p). simpl in H3. unfold _read in H3. simpl in H3.  unfold _nthTraversal, _nthTraversal' in H3. simpl in H3. simpl. unfold _read. simpl.  unfold _nthTraversal, _nthTraversal'. simpl. exact H3.                     
                  }
                }
              }
            }
          }
          {
            intros. split.
            {
              clear H. destruct a, o0. apply equiv_nth_equiv_lista_truncate.
              {
                reflexivity.
              }
              {
                intros. 
                clear H2.  simpl. specialize (H3 (0, 0) (0, ci)).
                simpl in H3.
                rewrite eq_lista_nth_lista_truncate_lt_lista_nth in H3.
                rewrite eq_lista_nth_lista_truncate_lt_lista_nth in H3.  auto. auto. auto. 
              }
              {
                clear H3. specialize (H2 (0, 0)). destruct H2.  clear H0. simpl in H. unfold _allocated in H.  simpl in H.  tauto.                 
              }
              {
                clear H3. specialize (H2 (0,0)). destruct H2.  clear H. simpl in H0. unfold _allocated in H0. simpl in H0. tauto. 
              }
              {
                reflexivity.
              }
            }
            {
              apply H.
              {
                intros. destruct v. destruct n.
                {
                  specialize (H2 (0, S n1)). simpl in H2. unfold _allocated in H2. simpl in H2. simpl. unfold _allocated. simpl. destruct n1. exact H2. exact H2.
                }
                {
                  specialize (H2 (S n, n1)). simpl in H2. unfold _allocated in H2. simpl in H2. unfold _nthTraversal, _nthTraversal' in H2. simpl in H2. simpl. unfold _allocated. simpl. unfold _nthTraversal, _nthTraversal'. simpl.  exact H2. 
                }
              }
              {
                clear H H2. intros. destruct v. destruct n.
                {
                  specialize (H3 (0, S n1) p). simpl in H3. unfold _read in H3. simpl in H3. simpl. unfold _read. simpl. destruct n1. exact H3. exact H3.
                }
                {
                  specialize (H3 (S n, n1) p). simpl in H3. unfold _read in H3. simpl in H3.  unfold _nthTraversal, _nthTraversal' in H3. simpl in H3. simpl. unfold _read. simpl.  unfold _nthTraversal, _nthTraversal'. simpl. exact H3. 
                    
                }
              }
            }
          }
          {
            intros. split.
            {
              clear H. destruct a, c. apply equiv_nth_equiv_lista_truncate.
              {
                reflexivity.
              }
              {
                intros. 
                clear H2.  simpl. specialize (H3 (0, 0) (0, ci)).
                simpl in H3.
                rewrite eq_lista_nth_lista_truncate_lt_lista_nth in H3.
                rewrite eq_lista_nth_lista_truncate_lt_lista_nth in H3.  auto. auto. auto. 
              }
              {
                clear H3. specialize (H2 (0, 0)). destruct H2.  clear H0. simpl in H. unfold _allocated in H.  simpl in H.  tauto.                 
              }
              {
                clear H3. specialize (H2 (0,0)). destruct H2.  clear H. simpl in H0. unfold _allocated in H0. simpl in H0. tauto. 
              }
              {
                reflexivity.
              }
            }
            {
              apply H.
              {
                intros. destruct v. destruct n.
                {
                  specialize (H2 (0, S n1)). simpl in H2. unfold _allocated in H2. simpl in H2. simpl. unfold _allocated. simpl. destruct n1. exact H2. exact H2.
                }
                {
                  specialize (H2 (S n, n1)). simpl in H2. unfold _allocated in H2. simpl in H2. unfold _nthTraversal, _nthTraversal' in H2. simpl in H2. simpl. unfold _allocated. simpl. unfold _nthTraversal, _nthTraversal'. simpl.  exact H2. 
                }
              }
              {
                clear H H2. intros. destruct v. destruct n.
                {
                  specialize (H3 (0, S n1) p). simpl in H3. unfold _read in H3. simpl in H3. simpl. unfold _read. simpl. destruct n1. exact H3. exact H3.
                }
                {
                  specialize (H3 (S n, n1) p). simpl in H3. unfold _read in H3. simpl in H3.  unfold _nthTraversal, _nthTraversal' in H3. simpl in H3. simpl. unfold _read. simpl.  unfold _nthTraversal, _nthTraversal'. simpl. exact H3.                     
                }
              }
            }
          }
        * destruct n. inversion l2. specialize (H1 (0, n) 0). destruct H1 as [H4 H1]. clear H1 H0 H2 H3. compute in H4. assert (0 = 0 /\ S n <= S n) as e. auto. specialize (H4 e). destruct H4. pose (nat_int _ _ l2) as e0. contradiction. 
      + apply H.
        * intros. clear H H1 H2 H3. specialize (H0 (S t0)). destruct H0. split.
          {
            intros. clear H0. 
            simpl in *. unfold _typeOfHeap in *. simpl in H. apply lt_S_n.  apply H. apply lt_n_S. auto.
          }
          {
            intros. clear H. 
            simpl in *. unfold _typeOfHeap in *. simpl in H0. apply lt_S_n.  apply H0. apply lt_n_S. auto.
          }          
        * intros. clear H H0 H2 H3 . destruct p.  specialize (H1  (S n, n0) (S t0)). destruct H1. split.
          {
            intros. clear H0. 
            simpl in *. unfold _predOfType in *. split. tauto. rewrite widthGetter_cons in H. rewrite widthGetter_cons in H.  apply H. split. simpl. f_equal. tauto. tauto.
          }
          {
            intros. clear H. 
            simpl in *. unfold _predOfType in *. split. tauto.  rewrite widthGetter_cons in H0. rewrite widthGetter_cons in H0.  apply H0. split. simpl. f_equal. tauto. tauto.
          }
        * intros. clear H H0 H1 H3. destruct v. specialize (H2 (S n , n0)). destruct H2. split.
          {
            intros. clear H0. 
            simpl in *. unfold _allocated  in *. simpl (addrToTableS @ _) in *. rewrite maybeRowGetter_cons in H. rewrite maybeRowGetter_cons in H. simpl (addrToRowS @ _) in *. auto. 
          }
          {
            intros. clear H. 
            simpl in *. unfold _allocated  in *. simpl (addrToTableS @ _) in *. rewrite maybeRowGetter_cons in H0. rewrite maybeRowGetter_cons in H0. simpl (addrToRowS @ _) in *. auto. 
          }
        * intros. clear H H0 H1 H2. destruct v, p. specialize (H3 (S n, n0) (S n1, n2)).  rewrite read_cons in H3. rewrite read_cons in H3. auto.
  Qed.

  Lemma eq_heap :
    forall (h1 h2 : t) ,
      (forall t, typeOfHeap @ t @ h1 <-> typeOfHeap @ t @ h2) ->
      (forall p t, predOfType @ p @ t @ h1 <-> predOfType @ p @ t @ h2) ->
      (forall v, allocated @ v @ h1 == allocated @ v @ h2) ->
      (forall v, readType @ v @ h1 == readType @ v @ h2) ->
      (forall v p, read @ v @ p @ h1 == read @ v @ p @ h2) ->
      h1 == h2.
  Proof.
    intros. auto using eq_heap0.
  Qed.


  Lemma extractAddr_addrToVal :
    forall addr,
      extractAddr @ (addrToVal @ addr) == Some addr.
  Proof.
    intros. reflexivity. 
  Qed.
  
  Lemma addrToVal_extractAddr :
    forall val addr,
      extractAddr @ val == Some addr ->
      addrToVal @ addr == val.
  Proof.
    intros val ? ?. destruct val.
    - inversion H.
    - simpl in H. rewrite H. reflexivity.
    - inversion H.
  Qed.

  Lemma cellGetter_maybeRowGetter :
    forall ti ri ci h,
      (maybeRowGetter @ ti @ ri @ h == None \/ maybeRowGetter @ ti @ ri @ h == Some None) ->
      cellGetter @ ti @ ri @ ci @ h == None.
  Proof.
    intros. unfold cellGetter, _cellGetter.  normalize. unfold maybeRowGetter, _maybeRowGetter in H. unfold injF2 in H. repeat rewrite eval_injF in H. unfold matrixCellTraversal. unfold matrixRowTraversal. repeat rewrite comp_associativity. rewrite nthTraversal_comp_preview. rewrite matrixRowsLens_comp_preview.  rewrite listaNthLens_comp_preview. unfold compM, _compM. normalize.
    rewrite (@comp_compM (lista (maybe row)) (maybe row) sqlVal _ _ _ maybe (@maybeS) maybe_Monad ) . 
    rewrite (@comp_compM (matrixp sqlVal) (lista (maybe row)) sqlVal _ _ _ maybe (@maybeS) maybe_Monad ) . rewrite <- compM_associativity. rewrite <- (associativity_compM maybe_Monad _ _ _ _ _ _ (previewS @ (nthTraversal @ ti) @ h) (ret ∘ view matrixRowsLens >=> ret ∘ view (listaNthLens ri)) (previewS @ (maybePrism ∘ listaNthLens ci))).
    destruct H.
    rewrite comp_associativity in H. rewrite nthTraversal_comp_preview in H. rewrite matrixRowsLens_comp_preview in H. unfold compM, _compM in H. unfold injF2 in H. repeat rewrite eval_injF in H.
    rewrite (comp_compM (view matrixRowsLens) (eval previewS (listaNthLens ri))) in H. rewrite H. reflexivity.
    rewrite comp_associativity in H. rewrite nthTraversal_comp_preview in H. rewrite matrixRowsLens_comp_preview in H. unfold compM, _compM in H. unfold injF2 in H. repeat rewrite eval_injF in H.
    rewrite (comp_compM (view matrixRowsLens) (eval previewS (listaNthLens ri))) in H. rewrite H. reflexivity.
  Qed.

  Lemma some_ret : forall A (AS : Setoid A) (a : A),
                     Some a == ret @ a.
  Proof.
    reflexivity.
  Qed.

  Opaque equiv.
  
  Lemma read_unallocated_addr:
    forall h pred1 addr,
      ~ allocated @ addr @ h -> read @ addr @ pred1 @ h == None.
  Proof.
    intros. simpl in *. unfold _allocated in H.  unfold _read. destruct (checkAddrPredS @ addr @ pred1).
    - rewrite some_ret. normalize_monad. unfold constS. normalize. apply cellGetter_maybeRowGetter. destruct (maybeRowGetter @ (addrToTableS @ addr) @ (addrToRowS @ addr) @ h).
      + right. destruct o. destruct H. unfold caseMaybeS, caseMaybe. simpl. auto. reflexivity.
      + left. reflexivity.
    - simpl. reflexivity.
  Qed.

  Lemma readType_unallocated_addr:
    forall h addr,
      ~ allocated @ addr @ h -> readType @ addr @ h == None.
  Proof.
    intros. simpl in *. unfold _allocated in H. unfold _readType. destruct (maybeRowGetter @ (addrToTableS @ addr) @ (addrToRowS @ addr) @ h).
    - simpl in *. unfold caseMaybe in *. destruct o.
      + simpl in *. tauto.
      + reflexivity.
    - simpl in *. reflexivity.
  Qed.


  Lemma update_unallocated_addr :
    forall h addr pred val2,
      ~ allocated @ addr @ h -> h [ addr , pred ↦  val2 ] == h.
  Proof.
    intros. simpl in *. unfold _allocated in H. unfold _update. destruct (checkAddrPredS @ addr @ pred).
    - rewrite some_ret. normalize_monad.
      rewrite (@left_unit _ _ maybe_Monad _ _ _ _ u (constS unitS @ (ret @ (cellSetter @ (addrToTableS @ addr) @ (addrToRowS @ addr) @ (predToColS @ pred) @ val2 @ h)))). unfold constS. normalize. rewrite <- some_ret. unfold caseMaybeS, caseMaybe. normalize. unfold idS, id. normalize. unfold cellSetter, _cellSetter. normalize. unfold setS. normalize. rewrite (nthTraversal_set _ _ sqlVal sqlValS (addrToTableS @ addr) (matrixCellTraversal (addrToRowS @ addr) (predToColS @ pred)) val2 h). destruct addr. simpl (addrToTableS @ _) in *. simpl (addrToRowS @ _) in *. unfold maybeRowGetter, _maybeRowGetter, injF2 in H. repeat rewrite eval_injF in H. rewrite comp_associativity in H. rewrite nthTraversal_comp_preview in H. unfold compM, _compM, injF2 in H.  repeat rewrite eval_injF in H.  destruct (maybe_case (@previewS (list (@matrixp sqlVal sqlVal_Pointed))
      (@matrixp sqlVal sqlVal_Pointed)
      (@listS (@matrixp sqlVal sqlVal_Pointed)
         (@matrixpS sqlVal sqlValS sqlVal_Pointed))
      (@matrixpS sqlVal sqlValS sqlVal_Pointed) @
    (@nthTraversal
       (@ConstMaybe (@matrixp sqlVal sqlVal_Pointed)
          (@matrixpS sqlVal sqlValS sqlVal_Pointed))
       (@ConstMaybeS (@matrixp sqlVal sqlVal_Pointed)
          (@matrixpS sqlVal sqlValS sqlVal_Pointed))
       (@ConstMaybeFunctor (@matrixp sqlVal sqlVal_Pointed)
          (@matrixpS sqlVal sqlValS sqlVal_Pointed))
       (@ConstMaybe_Applicative (@matrixp sqlVal sqlVal_Pointed)
          (@matrixpS sqlVal sqlValS sqlVal_Pointed))
       (@matrixp sqlVal sqlVal_Pointed)
       (@matrixpS sqlVal sqlValS sqlVal_Pointed) @ n) @ h)).
      + rewrite H0 in *. simpl. reflexivity.
      + destruct H0 as [m H0]. rewrite H0 in *. unfold caseMaybeS, caseMaybe.  normalize. rewrite some_ret in H. rewrite (left_unit _ _ _ _ m ( previewS @ (matrixRowsLens ∘ listaNthLens n0))) in H. rewrite matrixRowsLens_comp_preview in H. unfold comp in H. repeat rewrite eval_injF in H.
      unfold matrixCellTraversal, matrixRowTraversal. repeat rewrite comp_associativity.  unfold comp at 1. normalize. rewrite matrixRowsLens_comp_set. unfold comp at 1. normalize. rewrite listaNthLens_comp_set. rewrite comp_eval.
      rewrite listaNthLens_preview_view in H. destruct  (maybe_case (@view (lista (@maybe (lista sqlVal) (@listaS sqlVal sqlValS)))
        (@maybe (lista sqlVal) (@listaS sqlVal sqlValS))
        (@listaS (@maybe (lista sqlVal) (@listaS sqlVal sqlValS))
           (@optionS (lista sqlVal) (@listaS sqlVal sqlValS)))
        (@optionS (lista sqlVal) (@listaS sqlVal sqlValS))
        (@listaNthLens
           (@ConstFunc (@maybe (lista sqlVal) (@listaS sqlVal sqlValS))
              (@optionS (lista sqlVal) (@listaS sqlVal sqlValS)))
           (@ConstS (@maybe (lista sqlVal) (@listaS sqlVal sqlValS))
              (@optionS (lista sqlVal) (@listaS sqlVal sqlValS)))
           (ConstFunctor (@maybe (lista sqlVal) (@listaS sqlVal sqlValS))
              (@optionS (lista sqlVal) (@listaS sqlVal sqlValS)))
           (@maybe (lista sqlVal) (@listaS sqlVal sqlValS))
           (@optionS (lista sqlVal) (@listaS sqlVal sqlValS)) n0) @
      (@view (@matrixp sqlVal sqlVal_Pointed)
         (lista (@maybe (lista sqlVal) (@listaS sqlVal sqlValS)))
         (@matrixpS sqlVal sqlValS sqlVal_Pointed)
         (@listaS (@maybe (lista sqlVal) (@listaS sqlVal sqlValS))
            (@optionS (lista sqlVal) (@listaS sqlVal sqlValS)))
         (@matrixRowsLens
            (@ConstFunc
               (lista (@maybe (lista sqlVal) (@listaS sqlVal sqlValS)))
               (@listaS (@maybe (lista sqlVal) (@listaS sqlVal sqlValS))
                  (@optionS (lista sqlVal) (@listaS sqlVal sqlValS))))
            (@ConstS (lista (@maybe (lista sqlVal) (@listaS sqlVal sqlValS)))
               (@listaS (@maybe (lista sqlVal) (@listaS sqlVal sqlValS))
                  (@optionS (lista sqlVal) (@listaS sqlVal sqlValS))))
            (ConstFunctor
               (lista (@maybe (lista sqlVal) (@listaS sqlVal sqlValS)))
               (@listaS (@maybe (lista sqlVal) (@listaS sqlVal sqlValS))
                  (@optionS (lista sqlVal) (@listaS sqlVal sqlValS)))) sqlVal
            sqlValS sqlVal_Pointed) @ m))).
        * clear H. rewrite H1. rewrite maybePrism_comp_set. simpl (caseMaybeS @ _ @ _ @ _). rewrite <- H1. rewrite listaNthLens_view_set. rewrite matrixRowsLens_view_set.  unfold flipS. normalize. apply (nthTraversal_preview_set (matrixp sqlVal) (matrixpS sqlValS) n m h). left. rewrite H0. reflexivity.
        * destruct H1. rewrite H1 in *. simpl in H. tauto.
    - reflexivity.
  Qed.
  
  Axiom delete_unallocated_addr :
    forall h addr,
      ~ allocated @ addr @ h -> delete @ addr @ h == h.

  Axiom readType_allocated_addr:
    forall h addr,
      allocated @ addr @ h -> exists type1, readType @ addr @ h == Some type1.

  Axiom read_diff_pred :
    forall h val pred t,
      readType @ val @ h == Some t -> 
      ~ predOfType @ pred @ t @ h ->
      h [ val , pred ] == None.

  Axiom update_diff_pred :
    forall h val pred val2 t,
      readType @ val @ h == Some t -> 
      ~ predOfType @ pred @ t @ h ->
      h [ val , pred ↦ val2 ] == h.

  Axiom allocated_empty : forall v, ~ allocated @ v @ emptyH.
  
  Axiom allocated_newAddr_1:
    forall h type1 addr h',
      Some (h', addr) == newAddr @ type1 @ h -> ~ allocated @ addr @ h.
  
  Axiom allocated_newAddr_2:
    forall h type1 addr h',
      Some (h', addr) == newAddr @ type1 @ h -> allocated @ addr @ h'.

  Axiom readType_newAddr:
    forall h type1 addr h',
      Some (h', addr) == newAddr @ type1 @ h -> readType @ addr @ h' == Some type1.

  Axiom read_update :
    forall h val pred val2 t,
      readType @ val @ h == Some t -> 
      predOfType @ pred @ t @ h ->
      h [ val , pred ↦  val2 ] [ val , pred ] == Some val2.
  
  Axiom read_update_diff_addr :
    forall h val val' pred pred' val2,
      val <> val' ->
      h [ val , pred ↦ val2 ] [ val' , pred' ] == h [ val' , pred' ].
  
  Axiom allocated_update :
    forall h val pred val2 addr,
      allocated @ addr @ (h [ val , pred ↦  val2 ]) == allocated @ addr @ h.

  Axiom readType_update :
    forall h val pred val2 addr,
      readType @ addr @ (h [ val , pred ↦  val2 ]) == readType @ addr @ h.

  Axiom allocated_delete :
    forall h val,
      ~ allocated @ val @ (delete @ val @ h).
  
  Axiom allocated_delete_diff_addr :
    forall h addr1 addr',
      ~ addr1 == addr' ->
      allocated @ addr' @ (delete @ addr1 @ h) == allocated @ addr1 @ h.
  
  Axiom read_delete_diff_addr :
    forall h val val' pred,
      ~ val == val' ->
      (delete @ val @ h) [ val' , pred ] == h [val', pred].

  Axiom readType_delete_diff_addr :
    forall h val val',
      readType @ val' @ (delete @ val @ h) == readType @ val' @ h.
  
  Axiom update_update :
    forall h val pred val2 val3,
      h [ val , pred ↦  val2 ] [ val , pred ↦ val3 ] == h  [ val , pred ↦ val3 ].
  
  Axiom update_update_diff_addr :
    forall h val val' pred val2 val3,
      h [ val , pred ↦  val2 ] [ val' , pred ↦ val3 ] == h [ val' , pred ↦ val3 ] [ val , pred ↦ val3 ].
  
  Axiom update_update_diff_pred :
    forall h val pred pred' val2 val3,
      h [ val , pred ↦  val2 ] [ val , pred' ↦ val3 ] == h [ val , pred' ↦ val3 ] [ val , pred ↦ val3 ].

  Axiom delete_update :
    forall h val pred val2,
      delete @ val @ (h [ val , pred ↦  val2 ]) == delete @ val @ h.

  Axiom delete_update_diff_addr :
    forall h val val' pred val2 val3,
      delete @ val' @ (h [ val , pred ↦  val2 ]) == (delete @ val' @ h) [ val , pred ↦ val3 ].
  
  Axiom delete_delete :
    forall h val val',
      delete @ val' @ (delete @ val @ h) == delete @ val @ (delete @ val' @ h).

  Axiom update_newAddr_1 :
    forall h val pred val2 type1 h' addr,
      newAddr @ type1 @ h == Some (h', addr) ->
      newAddr @ type1 @ (h [ val , pred ↦  val2 ]) == Some (h' [ val , pred ↦  val2 ], addr).
  
  Axiom update_newAddr_2 :
    forall h val pred val2 type1,
      newAddr @ type1 @ h == None ->
      newAddr @ type1 @ (h [ val , pred ↦  val2 ]) == None.

  Axiom delete_newAddr :
    forall h type1 h' addr,
      newAddr @ type1 @ h == Some (h', addr) ->
      delete @ addr @ h' == h.
  


  Section AndMonoid.
  
    Existing Instance and_Monoid.

    Axiom read_lookupByObject :
      forall pred val h,
        fold @ ((equivS @  Some val) ∘ (cycle3S @ read @ pred @ h )  <$> lookupByObject @ pred @ val @ h) == True.

    Axiom read_lookupByPred :
      forall pred h,
             fold @ (uncurryS @ equivS ∘ (cycle3S @ read @ pred @ h *** SomeS ) <$> lookupByPred @ pred @ h) == True.

  End AndMonoid.

  Section OrMonoid.
    
    Existing Instance or_Monoid.

    Axiom lookupByObject_read :
      forall addr pred val h,
        h [addr, pred] == Some val ->
        fold @ (equivS @ addr <$> lookupByObject @ pred @ val @ h) == True.

    Axiom lookupByPred_read :
      forall addr pred val h,
        h [addr, pred] == Some val ->
        fold @ (equivS @ (addr, val)  <$> lookupByPred @ pred @ h) == True.
    
  End OrMonoid.
  




End SQLHeap.