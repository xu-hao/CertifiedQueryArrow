Require Import Definitions Algebra.Monoid Expr Algebra.SetoidCat Algebra.Maybe Tactics Algebra.ListUtils Algebra.Functor Algebra.Applicative Algebra.Alternative Algebra.FoldableFunctor Algebra.PairUtils Algebra.Maybe Algebra.Monad Algebra.Lens.Lens Algebra.Lens.MaybeLens ListLens Utils SetoidUtils SQL Pointed SQLUtils.
Require Import Coq.Structures.DecidableTypeEx List SetoidClass PeanoNat FMapWeakList Basics Coq.Arith.Compare_dec Coq.Arith.Le.


Definition insertRow table (h : database) : database :=
  match rowsGetter @ table @ h with
    | None => h
    | Some rows => maybeRowSetter @ table @ (lista_findaS maybe_row_eq_dec @ rows) @ (SomeS @ (lista_repeatS @ 0)) @ h
  end.

Instance insertRow_Proper : Proper (equiv ==> equiv ==> equiv) insertRow.
Proof.
  autounfold. intros. unfold insertRow. matchequiv. simpl in H1. rewrite H, H0, H1. reflexivity. auto. 
Qed.

Definition insertRowS : tableS ~> databaseS ~~> databaseS := injF2 insertRow _.

Definition deleteRow table rowid (h : database) : database :=
  match rowsGetter @ table @ h with
    | None => h
    | Some rows => maybeRowSetter @ table @ rowid @ None @ h
  end.

Instance deleteRow_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) deleteRow.
Proof.
  autounfold. intros. unfold deleteRow. matchequiv. rewritesr. auto. 
Qed.

Definition deleteRowS : tableS ~> natS ~~> databaseS ~~> databaseS := injF3 deleteRow _.

Definition newRowId table (h : database) : option nat :=
  match rowsGetter @ table @ h with
    | None => None
    | Some rows => SomeS @ (lista_findaS maybe_row_eq_dec @ rows)
  end.

Instance newRowId_Proper : Proper (equiv ==> equiv ==> equiv) newRowId.
Proof.
  autounfold. intros. unfold newRowId. matchequiv. simpl in H1. rewrite H1. reflexivity.
Qed.

Definition newRowIdS : tableS ~> databaseS ~~> maybeS natS := injF2 newRowId _.

Open Scope nat_scope.

Definition addrToTable addr (h : database) : table :=
  addr mod (length h).

Definition addrToRow addr (h : database) : nat :=
  addr / length h.

Instance addrToTable_Proper : Proper (equiv ==> equiv ==> equiv) addrToTable.
Proof.
  autounfold. intros. unfold addrToTable. rewritesr.  
Qed.

Definition addrToTableS : natS ~> databaseS ~~> tableS := injF2 addrToTable _.

Instance addrToRow_Proper : Proper (equiv ==> equiv ==> equiv) addrToRow.
Proof.
  autounfold. intros. unfold addrToRow. rewritesr.  
Qed.

Definition addrToRowS : natS ~> databaseS ~~> natS := injF2 addrToRow _.

Fixpoint _predToTable n t (pred1 : pred) (db : database) : maybe (table * colind) :=
  match db with
    | nil => None
    | tab :: tabs =>
      let (n2, rs) := tab in
      if lt_dec pred1 (n + n2) then
        Some (t, pred1 - n)
      else
        _predToTable (n + n2) (t + 1) pred1 tabs
  end
.

Instance _predToTable_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv) _predToTable.
Proof.
  autounfold. intros. rewrite H1. clear H1 x1. generalize x y H x0 y0 H0 y1 H2. clear x y H x0 y0 H0 y1 H2. apply list_ind_2 with (l1:=x2) (l2:=y2).
  intros. simpl. auto.
  intros. inversion H2.
  intros. inversion H2.
  intros. inversion H2. unfold _predToTable. fold _predToTable. destruct a, c.  destruct H6. rewrite H6, H0. destruct (lt_dec y1  (y + n0)). rewritesr. apply H. rewritesr. rewritesr. auto.
Qed.

Definition predToTableS : predS ~> databaseS ~~> maybeS tableS.
  simple refine (injF2 (fun pred1 db => fstS <$> _predToTable 0 0 pred1 db) _).
  exact (@maybeS).
  apply monadFunctor.
  Lemma predToTable_1 : Proper (equiv ==> equiv ==> equiv)
                               (fun (pred1 : pred) (db : database) =>
                                  fstS <$> _predToTable 0 0 pred1 db).
  Proof.
    solve_proper.
  Qed.
  apply predToTable_1.
Defined.

Definition predToColS : predS ~> databaseS ~~> maybeS natS.
  simple refine (injF2 (fun pred1 db => sndS <$> _predToTable 0 0 pred1 db) _).
  exact (@maybeS).
  apply monadFunctor.
  Lemma predToCol_1 : Proper (equiv ==> equiv ==> equiv)
                             (fun (pred1 : pred) (db : database) =>
                                sndS <$> _predToTable 0 0 pred1 db).
  Proof.
    solve_proper.
  Qed.
  apply predToCol_1.
Defined.      

Import SQLValType.


Definition getNewAddr (type1 : type) (h : database) : maybe nat.
  simple refine (newRowIdS @ type1 @ h >>= injF (fun rowid => ret @ (rowid * (length h) + type1)) _).
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

Definition checkAddrPred addr pred1 h :=
  (eqbS
     @ (addrToTableS @ addr @ h)
     <$> (predToTableS @ pred1 @ h) ) >>=
                                      noneFalse.

Definition _newAddr (type1 : type) h :=
  pairS
    @ (insertRowS @ type1 @ h)
    <$> (vNatS <$> getNewAddr type1 h).

Definition newAddr : typeS ~> databaseS ~~> maybeS (databaseS ~*~ valS).
  simple refine (injF2 _newAddr _).
  Lemma newAddr_1 : Proper (equiv ==> equiv ==> equiv) _newAddr.
  Proof.
    autounfold. intros. unfold _newAddr, getNewAddr. evalproper. rewritesr. evalproper. bindproper. rewritesr. rewritesr.
  Qed.
  apply newAddr_1.
Defined.

Definition _filterByCol ci val1 row  :=
  match nth_error row ci, extractNatS @ val1 with
    | Some n, Some n' => eqbS @ n @ n'
    | _, _ => false
  end.

Instance _filterByCol_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _filterByCol.
Proof.
  autounfold. intros. unfold _filterByCol. matchequiv. matchequiv. rewritesr.
Qed.

Definition filterByCol := injF3 _filterByCol _.

Definition _filterVal val1 val2  :=
  match val2, extractNatS @ val1 with
    | Some n, Some n' => eqbS @ n @ n'
    | _, _ => false
  end.

Instance _filterVal_Proper : Proper (equiv ==> equiv ==> equiv) _filterVal.
Proof.
  autounfold. intros. unfold _filterVal. matchequiv. matchequiv. rewritesr.
Qed.

Definition filterVal := injF2 _filterVal _.

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

Definition _getAddr (h : database) t ri  : nat  :=
  ri * length h + t.

Instance _getAddr_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _getAddr.
Proof.
  autounfold. intros. unfold _getAddr. rewritesr. 
Qed.

Definition getAddr := injF3 _getAddr _.

Definition _lookupByObject pred1 val1 h : list sqlVal :=
  match predToTableS @ pred1 @ h, predToColS @ pred1 @ h with
    | Some t, Some ci =>
      match colGetter @ t @ ci @ h with
        | Some col =>
          mapS
            @ (vNatS ∘ getAddr @ h @ t)
            @ (lista_filter_indexS @ (filterVal @ val1) @ col )
        | None => nil                  
      end
    | _, _ => nil
  end.

Lemma _predToTable_le : forall n t pred1 m, _predToTable n t pred1 m = None \/ (exists a b, _predToTable n t pred1 m = Some (a, b) /\ a >= t).
    intros. generalize  n t pred1. clear n t pred1.   induction m. left. auto.
    intros. destruct a.  simpl. destruct (lt_dec pred1 (n + n0)). right. exists t. exists (pred1 - n). auto.  pose (IHm (n+n0) (t+1) pred1). destruct o. tauto. right. destruct H as [? [? ?]]. exists x. exists x0. split. tauto. destruct H. unfold ge in *. apply le_Sn_le. rewrite plus_symmetry in H0.  auto.
Qed.

Module SQLHeap <: Heap SQLValType.
  
  Definition t := database.
  Program Instance tS : Setoid t.

  Definition _delete0 addr h : t := deleteRowS
                                    @ (addrToTableS @ addr @ h)
                                    @ (addrToRowS @ addr @ h)
                                    @ h.

  
  Instance _delete0_Proper : Proper (equiv ==> equiv ==> equiv) _delete0.
  Proof.
    autounfold. intros. unfold _delete0. rewritesr. 
  Qed.

  Definition delete0 : natS ~> tS ~~>  tS := injF2 _delete0 _.

  Definition _delete addr h :=
    fromMaybeS @ h @ (delete0 <$> extractNatS @ addr <*> pure @ h).

  Instance _delete_Proper : Proper (equiv ==> equiv ==> equiv) _delete.
  Proof.
    autounfold. intros. unfold _delete. rewritesr.
  Qed.

  Definition delete := injF2 _delete _.

  Definition _read0 addr pred1 h : maybe nat :=
    checkAddrPred addr pred1 h >>
                  (cellGetter
                     @ (addrToTableS @ addr @ h)
                     @ (addrToRowS @ addr @ h)
                     <$> predToColS @ pred1 @ h
                     <*> pure @ h : maybe (maybe nat)) >>= fmap @ idS.

  Instance _read0_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _read0.                     
  Proof.
    autounfold. intros. unfold _read0, checkAddrPred. rewritesr. 
  Qed.

  Definition read0 := injF3 _read0 _.

  Definition _read addr pred1 h : maybe sqlVal :=
    (read0 <$> extractNatS @ addr <*> pure @ pred1 <*> pure @ h : maybe (maybe nat)) >>= fmap @ vNatS.
  
  Instance _read_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _read.                     
  Proof.
    autounfold. intros. unfold _read. rewritesr. 
  Qed.

  Definition read : valS ~> predS ~~> tS ~~> maybeS valS := injF3 _read _.
  
  Definition _update0 addr pred1 val1 h : maybe t :=
    checkAddrPred addr pred1 h >>
                  (cellSetter
                     @ (addrToTableS @ addr @ h)
                     @ (addrToRowS @ addr @ h)
                     <$> predToColS @ pred1 @ h
                     <*> pure @ val1 
                     <*> pure @ h).
  
  Instance _update0_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv) _update0.
  Proof.
    autounfold. intros. unfold _update0, checkAddrPred. rewritesr. 
  Qed.

  Definition update0 := injF4 _update0 _.

  Definition _update addr pred1 val1 h : t :=
    fromMaybeS @ h @ ((update0 <$> extractNatS @ addr <*> pure @ pred1 <*> extractNatS @ val1 <*> pure @ h) >>= fmap @ idS).

  Instance _update_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv) _update.
  Proof.
    autounfold. intros. unfold _update. rewritesr. 
  Qed.

  Definition update : valS ~> predS ~~> valS ~~> tS ~~> tS := injF4 _update _.
  
  Definition emptyH : database := nil.
  Definition union : tS ~> tS ~~> tS := unionDatabases.

  Definition _allocated0 addr h : Prop :=
    match fromMaybeS @ None @ (maybeRowGetter
                                 @ (addrToTableS @ addr @ h)
                                 @ (addrToRowS @ addr @ h)
                                 @ h) with
      | None => False
      | Some _ => True
    end.

  Instance _allocated0_Proper : Proper (equiv ==> equiv==>equiv) _allocated0.
  Proof.
    autounfold. intros. unfold _allocated0. matchequiv.
  Qed.

  Definition allocated0 := injF2 _allocated0 _.
  
  Definition _allocated addr h :=
    match allocated0
            <$> extractNatS @ addr
            <*> pure @ h with
      | None => False
      | Some a => a
    end
  .
  
  Instance _allocated_Proper : Proper (equiv ==> equiv==>equiv) _allocated.
  Proof.
    autounfold. intros. unfold _allocated. matchequiv. auto.
  Qed.

  Definition allocated := injF2 _allocated _.

  Definition l A (AS : Setoid A) := list A.
  Instance lS A (AS : Setoid A) : Setoid (l A AS) := listS AS.
  Instance func : @Functor l lS := listFunctor.
  Instance alt : @Alternative l lS := list_Alternative.
  Instance foldable : @FoldableFunctor l lS func := list_Foldable.
  Instance app : @Applicative l lS func := list_Applicative.

  Definition _lookupBySPO addr pred1 val1 h :=
    match read @ addr @ pred1 @ h with
      | None => false
      | Some val2 =>         
        if SQLValType.equiv_dec val1 val2 then true else false
    end
  .

  Instance _lookupBySPO_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv) _lookupBySPO.
  Proof.
    autounfold. intros. unfold _lookupBySPO. matchequiv. rewritesr. 
  Qed.

  Definition lookupBySPO :  valS ~> predS ~~> valS ~~> tS ~~> boolS := injF4 _lookupBySPO _.

  Instance _lookupByObject_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _lookupByObject.
  Proof.
    autounfold. intros. unfold _lookupByObject. matchequiv. matchequiv. matchequiv. simpl in H2, H3, H4. rewrite H0, H1, H2, H4. reflexivity.
  Qed.

  Definition lookupByObject   : predS ~> valS ~~> tS ~~> lS _ valS := injF3 _lookupByObject _.
  
  Definition _lookupByPred pred1 h : list (sqlVal * sqlVal) :=
    match predToTableS @ pred1 @ h, predToColS @ pred1 @ h with
      | Some t, Some ci =>
        match colGetter @ t @ ci @ h with
          | Some col =>
            mapS
              @ ((vNatS ∘ getAddr @ h @ t) *** vNatS)
              @ (lista_filter_indexS' @ col)
          | None => nil                  
        end
      | _, _ => nil
    end.

  Instance _lookupByPred_Proper : Proper (equiv ==> equiv ==> equiv) _lookupByPred.
  Proof.
    autounfold. intros. unfold _lookupByPred. matchequiv. matchequiv. matchequiv. simpl in H1, H2, H3. rewrite H0, H1, H3. reflexivity.
  Qed.

  Definition lookupByPred   : predS ~> tS ~~> lS _ (valS ~*~ valS) := injF2 _lookupByPred _. 

  Definition _predOfType pred1 type1 h :=
    match predToTableS @ pred1 @ h with
      | None => False
      | Some t' => type1 == t'
    end.

  Instance _predOfType_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _predOfType.
  Proof.
    autounfold. intros. unfold _predOfType. matchequiv. simpl in H2. rewrite H0, H2. reflexivity.
  Qed.

  Definition predOfType :
    predS ~> typeS ~~> databaseS ~~> iff_setoid := injF3 _predOfType _.
  
  Definition _typeOfHeap type1 (h : database) :=
    type1 < length h.

  Instance _typeOfHeap_Proper : Proper (equiv ==> equiv ==> equiv) _typeOfHeap.
  Proof.
    autounfold. intros. unfold _typeOfHeap. rewrite H, H0. reflexivity.
  Qed.

  Definition typeOfHeap : typeS  ~> databaseS ~~> iff_setoid := injF2 _typeOfHeap _.    
             
  Notation "heap [ val , pred ]" := (read @ val @ pred @ heap) (at level 11).
  Notation "heap [ val , pred  ↦  val2 ]  " := (update @ val @ pred @ val2 @ heap) (at level 11).

  Require Import Coq.Arith.Minus.
  

  Lemma _read_cons_1 :
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
  
    
  Lemma eq_heap :
    forall (h1 h2 : t) ,
      (forall v, allocated @ v @ h1 == allocated @ v @ h2) ->
      (forall v p, read @ v @ p @ h1 == read @ v @ p @ h2) ->
      (forall p t, predOfType @ p @ t @ h1 <-> predOfType @ p @ t @ h2) ->
      (forall t, typeOfHeap @ t @ h1 <-> typeOfHeap @ t @ h2) ->
      h1 == h2.
  Proof.
    
    intros. generalize H H0 H1 H2. clear H H0 H1 H2. apply list_ind_2 with (l1:=h1)(l2:=h2).
    -    reflexivity.
    - intros. pose (H3 0).    simpl in i . unfold _typeOfHeap in i. simpl in i.  assert (0 < S (length b)).  apply le_n_S. apply Nat.le_0_l.  destruct i. pose (H6 H4). inversion l0. 
    - intros. pose (H3 0).    simpl in i . unfold _typeOfHeap in i. simpl in i.  assert (0 < S (length b)).  apply le_n_S. apply Nat.le_0_l.  destruct i. pose (H5 H4). inversion l0. 
    - intros. constructor. destruct a, c.
      + destruct (lt_eq_lt_dec n n0) as [[? | ?] | ?].
        * destruct n0. inversion l2.
          specialize (H2 n0 0). simpl in H2. unfold _predOfType in H2. simpl in H2. assert False. clear H3 H0 H. destruct (lt_dec n0 n) , (lt_dec n0 (S n0)).
          apply (nat_int _ _ l2 l3).
          apply (nat_int _ _ l2 l3).
          destruct b. simpl in H1. tauto. pose (_predToTable_le n 1 n0 (m::b)). destruct o. rewrite H in H2. apply H2. auto. destruct H as [? [? [? ?]]]. rewrite H in H2. simpl in H2. destruct H2. rewrite <- H3 in H0. inversion H0. auto.
          apply n2. constructor.
          tauto. 
        * rewrite e in *. clear n e. clear H H2 H3. split. auto. destruct l0, l1. unfold _rows. generalize H0 H1. clear H0 H1. apply list_ind_2 with (l1:=l0) (l2:=l1).
          {
            intros. induction n0.
            {
              destruct o, o0.
              {
                simpl. destruct l2, l3.  simpl. auto.
              }
              {
                Opaque equiv _read0.  simpl in e. unfold _read in e. simpl in e. destruct l2, l3. Transparent equiv. induction n0.
              {
                simpl.  auto.
              }
              {
                simpl. auto.
                simpl in e. unfold lista_equiv0. 

pose (_read_cons_1 0 0 (matrixpCons nat n0 (listaCons (option (lista nat)) (Some l2) nil)) b).

              assert (_read0 0 0
       (matrixpCons nat n0 (listaCons (option (lista nat)) (Some l2) nil)
        :: b) == rewrite uncurry_fmap_prod. rewrite uncurry_fmap_prod. rewrite uncurry_fmap_prod. rewrite fmap_eval. rewrite fmap_eval. rewrite fmap_eval. unfold ap. normalize_monad. unfold comp2S. normalizecomp. normalize_monad.
              unfold injF3 in e. unfold injF2 in e. simpl in e. unfold monad_fmap in e. normalize_monad. simpl in e.
              pose _read_cons_1. assert (exists a', _read0 0 0
          (matrixpCons nat n0 (listaCons (option (lista nat)) (Some l2) nil)
                       :: b) = Some a').
              {
                
                rewrite _read_cons_1 in e. rewritesr. simpl. simpl in H0. destruct H0.
           pose (nat_int _ _ l2).
          simpl in H1. destruct m, (lt_dec n0 (n + n2)). destruct H1. simpl in H0. assert (0 = 0). auto. pose (H0 H1). inversion e. destruct H0. auto. tauto.
          unfold _predToTable in H1. destruct b.
          apply (nat_int _ _ l2 l3).
          pose (H2 0).    simpl in i . unfold _typeOfHeap in i. simpl in i.  assert (0 < S (length b)).  apply le_n_S. apply Nat.le_0_l.  destruct i. pose (H5 H3). inversion l0. 

  Axiom dom_lookup : forall h val,  inDom @ val @ h -> exists pred val2, h [val,pred] == Some val2.

  Axiom dom_domPred : forall h val, inDom @ val @ h -> exists pred, inPredDom @ val @ pred @ h.

  Axiom domPred_lookup : forall h val pred, inPredDom @ val @ pred @ h -> exists val2, h[val, pred] == Some val2.

  Axiom lookupBySubject_empty : forall val pred, emptyH [val,pred] == None.

  Axiom lookupByObject_empty : forall pred val, lookupByObject @ pred @ val @ emptyH == empty.

  Axiom lookupByPred_empty : forall pred , lookupByPred @ pred @ emptyH == empty.

  Axiom lookupBySPO_empty : forall val pred val2, lookupBySPO @ val @ pred @ val2 @ emptyH == false.
  
  Axiom lookup_predDom : forall h val pred, (exists val2, lookupBySubject @ val @ pred @ h == Some val2) ->  inPredDom @ val @ pred @ h.

  Axiom predDom_dom : forall h val, (exists pred, inPredDom @ val @ pred @ h) -> inDom @ val @ h.

  Lemma lookup_dom : forall h val, (exists pred val2, lookupBySubject @ val @ pred @ h == Some val2) -> inDom @ val @ h.
  Proof.
    intros. apply predDom_dom. destruct H as [? [? ?]]. exists x. apply lookup_predDom. exists x0.  auto.
  Qed.

  Axiom predDom_newAddr:
        forall h h' val pred, (h', val) == newAddr @ h -> ~ inPredDom @ val @ pred @ h.
  
  Axiom lookupBySubject_predDom_0:
        forall h val pred, ~ inPredDom @ val @ pred @ h -> h [val , pred] == None.
  
  Axiom lookupBySubject_predDom_1:
        forall h val pred, inPredDom @ val @ pred @ h -> exists val2, h [val , pred] == val2.

  Lemma lookupBySubject_newAddr:
        forall h h' val pred, (h', val) == newAddr @ h -> h [val, pred] == None.
  Proof.
    intros. apply lookupBySubject_predDom_0. apply predDom_newAddr with (h:=h) (h':=h'). auto.
  Qed.
  
  Axiom lookup_update :
    forall h val pred val2,
      h [ val , pred ↦  val2 ] [ val , pred ] == Some val2.
  
  Axiom lookup_update_diff_addr :
    forall h val val' pred pred' val2,
      val <> val' ->
      h [ val , pred ↦ val2 ] [ val' , pred' ] == h [ val' , pred' ].
  
  Axiom lookup_update_diff_pred :
    forall h val val' pred pred' val2,
      pred <> pred' ->
      h [ val , pred ↦ val2 ] [ val' , pred' ] == h [ val' , pred' ].
  
  Axiom update_update :
    forall h val pred val2 val3,
      h [ val , pred ↦  val2 ] [ val , pred ↦ val3 ] == h  [ val , pred ↦ val3 ].
  
  Axiom predDom_update :
    forall h val pred val2,
       inPredDom @ val @ pred @ ( h [ val , pred ↦ val2 ]).
  
  Axiom predDom_update_diff_addr :
    forall h val val' pred pred' val2,
      val <> val' -> 
      inPredDom @ val @ pred @ ( h [ val' , pred' ↦ val2 ]) == inPredDom @ val @ pred @ h.

  Axiom predDom_update_diff_pred :
    forall h val val' pred pred' val2,
      pred <> pred' -> 
      inPredDom @ val @ pred @ ( h [ val' , pred' ↦ val2 ]) == inPredDom @ val @ pred @ h.

  Axiom dom_update_diff_addr :
    forall h val val' pred val2,
      val <> val' -> 
      inDom @ val @ ( h [ val' , pred ↦ val2 ]) == inDom @ val @ h.






End SQLHeap.