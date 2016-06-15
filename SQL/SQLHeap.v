Require Import Definitions Algebra.Monoid Expr Algebra.SetoidCat Algebra.Maybe Tactics Algebra.ListUtils Algebra.Functor Algebra.Applicative Algebra.Alternative Algebra.FoldableFunctor Algebra.PairUtils Algebra.Maybe Algebra.Monad Algebra.Lens.Lens Algebra.Lens.MaybeLens ListLens Utils SetoidUtils SQL Pointed SQLUtils Lista Matrixp ListaLens MatrixpLens MonoidUtils.
Require Import Coq.Structures.DecidableTypeEx List SetoidClass PeanoNat FMapWeakList Basics Coq.Arith.Compare_dec Coq.Arith.Le Coq.Arith.Lt.
Definition insertRow (table : nat) (h : database) : database :=
  caseMaybeS
    @ (cycle24S @ maybeRowSetter @ table @ (SomeS @ (lista_repeat)) @ h
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


Definition _filterVal val1 val2  :=
  if SQLValType.equiv_dec val1 val2 then true else false.

Instance _filterVal_Proper : Proper (equiv ==> equiv ==> equiv) _filterVal.
Proof.
  autounfold. intros. unfold _filterVal. rewrite H, H0. destruct (SQLValType.equiv_dec y y0). reflexivity. reflexivity. 
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

  Definition _lookupByObject pred1 val1 h : list sqlAddr :=
    let t := predToTableS @ pred1 in
    caseMaybeS
      @ (mapS @ (getAddr @ t) ∘ lista_filter_indexS @ (filterSomeVal @ val1))
      @ nil
      @ (colGetter @ t @ (predToColS @ pred1) @ h).

  Instance _lookupByObject_Proper : Proper (equiv ==> equiv ==> equiv ==> equiv) _lookupByObject.
  Proof.
    solve_properS _lookupByObject.
  Qed.

  Definition lookupByObject   : sqlPredS ~> sqlValS ~~> tS ~~> listS sqlAddrS := injF3 _lookupByObject _.
  
  Definition _lookupByPred pred1 h : list (sqlAddr * sqlVal) :=
    let t := predToTableS @ pred1 in
    caseMaybeS
      @ (mapS @ ((getAddr @ t) *** idS) ∘ lista_filter_indexS')
      @ nil                  
      @ (colGetter @ t @ (predToColS @ pred1) @ h).

  Instance _lookupByPred_Proper : Proper (equiv ==> equiv ==> equiv) _lookupByPred.
  Proof.
    solve_properS _lookupByPred.
  Qed.

  Definition lookupByPred   : sqlPredS ~> tS ~~> listS (sqlAddrS ~*~ sqlValS) := injF2 _lookupByPred _.
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
    type1 == predToTableS @ pred1 .

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

Lemma nthPreview_cons : forall A (AS : Setoid A) n (a : A) l, preview @ nthPreview (S n) @ (a :: l) == preview @ nthPreview n @ l.
Proof.
  intros. reflexivity.
Qed.

Lemma maybeRowGetter_cons : forall n r a l, maybeRowGetter @ (S n) @ r @ (a :: l) == maybeRowGetter @ n @ r @ l.
Proof.
  intros. reflexivity. 
Qed.

Lemma read_cons : forall n n2 r c a l, read @ (S n, r) @ (S n2, c) @ (a :: l) == read @ (n, r) @ (n2, c) @ l.
Proof.
  intros. reflexivity. 
Qed.
  
Lemma eq_heap0 :
  forall (h1 h2 : t) ,
    (forall t, typeOfHeap @ t @ h1 <-> typeOfHeap @ t @ h2) ->
    (forall p t, predOfType @ p @ t @ h1 <-> predOfType @ p @ t @ h2) ->
    (forall v, allocated @ v @ h1 == allocated @ v @ h2) ->
    (forall v p, read @ v @ p @ h1 == read @ v @ p @ h2) ->
    h1 == h2.
Proof.
    
  intros. generalize H H0 H1 H2. clear H H0 H1 H2. apply list_ind_2 with (l1:=h1)(l2:=h2).
  - reflexivity.
  - intros. destruct (H0 0). simpl in H5. unfold _typeOfHeap in H5. simpl in H5. assert (0 < S(length b)). apply lt_O_Sn. pose (H5 H6) as e. inversion e.
  - intros. destruct (H0 0). simpl in H4. unfold _typeOfHeap in H4. simpl in H4. assert (0 < S(length b)). apply lt_O_Sn. pose (H4 H6) as e. inversion e.
  - intros. constructor.
    + clear H. destruct a, c. clear H0 H1. destruct l0, l1. generalize H2 H3. clear H2 H3. apply list_ind_2 with (l1:=l0) (l2:=l1).
      * intros. reflexivity.
      * intros. simpl. destruct a.
        {
          specialize (H3 (0, 0) (0, 0)). simpl in H3.  tauto.
        }
        {
          split; [reflexivity|]. apply listAll_nth. intros. specialize (H2 (0, S ci)). simpl in H2. unfold _allocated in H2. simpl in H2. simpl.  destruct (nth ci b0 None).
          {
            simpl in H2. tauto. 
          }
          {
            reflexivity.
          }
        }
      * intros. simpl. destruct a.
        {
          specialize (H3 (0, 0) (0, 0)). simpl in H3.  tauto.
        }
        {
          split; [reflexivity|]. apply lista_equiv_nil. apply listAll_nth. intros. specialize (H2 (0, S ci)). simpl in H2. unfold _allocated in H2. simpl in H2. simpl.  destruct (nth ci b0 None).
          {
            simpl in H2. tauto. 
          }
          {
            reflexivity.
          }
        }
      * intros. split.
        {
          destruct a, c.
          {
            simpl. apply lista_equiv_nth.  intros. specialize (H3 (0, 0) (0, ci)). simpl in H3.  auto.        }
          {
            specialize (H2 (0, 0)). simpl in H2. unfold _allocated in H2. simpl in H2. tauto. 
          }
          {
            specialize (H2 (0, 0)). simpl in H2. unfold _allocated in H2. simpl in H2. tauto. 
          }
          {
            reflexivity.
          }
        }
        {
          apply H.
          {
            clear H H3. intros. destruct v. destruct n.
            {
              specialize (H2 (0, S n0)).  simpl in *. unfold _allocated in *. simpl in *. auto.
            }
            {
              specialize (H2 (S n, n0)).  simpl in *. unfold _allocated in *. simpl in *. auto.
            }
          }
          {
            clear H H2. intros. destruct v, p. destruct n.
            {
              specialize (H3 (0, S n0) (n1, n2)). simpl in *. unfold _read in *. unfold checkAddrPredS, checkAddrPred in *. simpl (addrToRowS @ _) in *. simpl (addrToTableS @ _) in *. simpl (predToTableS @ _) in *. simpl (predToColS @ _) in *. normalize. normalizeHyp H3. simpl (fst _) in *. simpl (snd _) in *. destruct (eqbS @ 0 @ n1).
              {
                simpl in *. auto.
              }
              {
                simpl in *. auto.
              }
            }
            {
              specialize (H3 (S n, n0) (n1, n2)). simpl in *. auto. 
            }
          }
        }
    + apply H.
      * intros. clear H H1 H2 H3. specialize (H0 (S t0)). simpl in *. unfold _typeOfHeap in *. simpl in *. split.
        {
          intros. apply lt_S_n. apply H0. apply lt_n_S. auto.
        }
        {
          intros. apply lt_S_n. apply H0. apply lt_n_S. auto.
        }
      * intros. clear H H0 H2 H3 . destruct p.  specialize (H1  (S n, n0) (S t0)). split.
          {
            intros.  
            simpl in *. unfold _predOfType in *. auto. 
          }
          {
            intros. 
            simpl in *. unfold _predOfType in *. auto. 
          }
        * intros. clear H H0 H1 H3. destruct v. specialize (H2 (S n , n0)). split.
          {
            intros. 
            simpl in *. unfold _allocated  in *. simpl in *. apply H2.   auto. 
          }
          {
            intros. 
            simpl in *. unfold _allocated  in *. simpl in *. apply H2. auto. 
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
    - inversion H.
    - inversion H.
  Qed.
Require Import MonadUtils.
  
  (*Lemma some_ret : forall A (AS : Setoid A) (a : A),
                     Some a == ret @ a.
  Proof.
    reflexivity.
  Qed. *)



  Arguments row / .
  Arguments rowS / .
  Arguments SQLValType.valS /.
  Arguments maybe A {SA} / .
  Arguments maybeS {A} SA / .
  Arguments table / .
  Arguments caseMaybe {A B AS BS} some none val1 / .
  Arguments _predOfType pred1 type1 h / .
  Arguments _update addr pred1 val1 h / .
  Arguments _readType addr h /.
  Arguments checkAddrPred addr pred1 /.
  Arguments _allocated addr h /.
  Arguments _read addr pred1 h /.
  Arguments _delete addr h /.
  Arguments deleteRow table rowid h / .
  Arguments id {A} x / .
  Arguments _MatrixRowsLens_set {A AS AP} l r m /.
  Arguments _newAddr type1 h / .
  Arguments getNewAddr type1 h / .
  Arguments newRowId table h / .
  Arguments tableS / .
  Arguments emptyH /. 
  Arguments insertRow table h / .

                  

  Lemma read_unallocated_addr:
    forall h pred1 addr,
      ~ allocated @ addr @ h -> read @ addr @ pred1 @ h == None.
  Proof.
    intros. destruct addr, pred1. simpl in *. destruct ( (n =? n1)).
    - simpl in *.
      destruct (@nth_error (@matrixp sqlVal sqlValS sqlVal_Pointed) h n).
      destruct (@lista_nth (option (lista sqlVal))
       (@optionS (lista sqlVal) (@listaS sqlVal sqlValS sqlVal_Pointed))
       (maybe_Pointed (lista sqlVal)) n0
       (@_rows sqlVal sqlValS sqlVal_Pointed m)).
      tauto. reflexivity. reflexivity.
    - simpl. reflexivity.
  Qed.

  Lemma readType_unallocated_addr:
    forall h addr,
      ~ allocated @ addr @ h -> readType @ addr @ h == None.
  Proof.
    intros. destruct addr. simpl in *. destruct (@nth_error (@matrixp sqlVal sqlValS sqlVal_Pointed) h n).
    - destruct (@lista_nth (option (lista sqlVal))
       (@optionS (lista sqlVal) (@listaS sqlVal sqlValS sqlVal_Pointed))
       (maybe_Pointed (lista sqlVal)) n0
       (@_rows sqlVal sqlValS sqlVal_Pointed m)). tauto. reflexivity. 
    - reflexivity.
  Qed.


  Lemma update_unallocated_addr :
    forall h addr pred val2,
      ~ allocated @ addr @ h -> h [ addr , pred ↦  val2 ] == h.
  Proof.
    intros. destruct addr, pred. simpl in *. destruct ( (n =? n1)).
    - simpl in *.
      destruct (maybe_case (@nth_error (@matrixp sqlVal sqlValS sqlVal_Pointed) h n)).
      + rewrite H0 in *. reflexivity.
      + destruct H0.  rewrite H0 in *. destruct (@lista_nth (option (lista sqlVal))
       (@optionS (lista sqlVal) (@listaS sqlVal sqlValS sqlVal_Pointed))
       (maybe_Pointed (lista sqlVal)) n0
       (@_rows sqlVal sqlValS sqlVal_Pointed x)).
        * tauto.
        * simpl in *. apply (list_update_list_nth table tableS n x h). simpl. rewrite H0. reflexivity.
    - reflexivity.
  Qed.

  
  Lemma delete_unallocated_addr :
    forall h addr,
      ~ allocated @ addr @ h -> delete @ addr @ h == h.
  Proof.
    intros. destruct addr. simpl in *. destruct (maybe_case (@nth_error (@matrixp sqlVal sqlValS sqlVal_Pointed) h n)).
    - rewrite H0 in *. reflexivity.
    - destruct H0. rewrite H0 in *. simpl in *. destruct x.
      simpl in *. destruct (maybe_case (@lista_nth (option (lista sqlVal))
          (@optionS (lista sqlVal) (@listaS sqlVal sqlValS sqlVal_Pointed))
          (maybe_Pointed (lista sqlVal)) n0 l0)).
      + rewrite H1 in H. auto. rewrite <- H1. rewrite lista_update_lista_nth. rewrite list_update_list_nth.  reflexivity. rewrite H0. reflexivity.
      +  destruct H1. rewrite H1 in H. tauto. 
  Qed.
  
  Lemma readType_allocated_addr:
    forall h addr,
      allocated @ addr @ h -> exists type1, readType @ addr @ h == Some type1.
  Proof.
    intros. destruct addr.  simpl in *. destruct (maybe_case (@nth_error (@matrixp sqlVal sqlValS sqlVal_Pointed) h n)).
    - rewrite H0 in *. tauto. 
    - destruct H0. rewrite H0 in *. destruct x. simpl in *. destruct ( lista_nth n0 l0).  
      + exists n. reflexivity.
      + tauto.
  Qed.
  
  Lemma read_diff_pred :
    forall h val pred t,
      readType @ val @ h == Some t -> 
      ~ predOfType @ pred @ t @ h ->
      h [ val , pred ] == None.
  Proof.
    intros. destruct val, pred. simpl in *.  destruct (bool_case (n =? n1)). 
    - rewrite H1. destruct (maybe_case (@nth_error (@matrixp sqlVal sqlValS sqlVal_Pointed) h n)).
      + rewrite H2. reflexivity.
      + destruct H2. rewrite H2 in *. destruct x. simpl in *. destruct ( lista_nth n0 l0).
        * apply H0. rewrite <- H. apply Nat.eqb_eq. auto. 
        * reflexivity.  
    - rewrite H1.  reflexivity. 
  Qed.

  Lemma update_diff_pred :
    forall h val pred val2 t,
      readType @ val @ h == Some t -> 
      ~ predOfType @ pred @ t @ h ->
      h [ val , pred ↦ val2 ] == h.
  Proof.
    intros. destruct val, pred. simpl in *. normalize. destruct (bool_case (n =? n1)). rewrite H1.
    - simpl in *. destruct (maybe_case (nth_error h n)).
      + simpl in *. rewrite H2 in *. reflexivity.
      + simpl in *.  destruct H2. rewrite H2 in *. destruct x. destruct (maybe_case (lista_nth n0 l0)).
        * simpl in *. rewrite H3 in *. rewrite (list_update_list_nth _ _ n (matrixpCons _ l0) h). reflexivity. simpl in *. rewrite H2.   reflexivity. 
        * simpl in *. destruct H3.   rewrite H3 in *. destruct H0. rewrite <- H. apply Nat.eqb_eq. auto.
    - rewrite H1. reflexivity.
  Qed.      

  Lemma allocated_empty : forall v, ~ allocated @ v @ emptyH.
  Proof.
    intros. destruct v. simpl.  destruct n.
    - simpl. auto.
    - simpl. auto.
  Qed.
  

  Lemma allocated_newAddr_1:
    forall h type1 addr h',
      Some (h', addr) == newAddr @ type1 @ h -> ~ allocated @ addr @ h.
  Proof.
    intros. destruct addr. simpl in *. destruct (maybe_case (@nth_error (@matrixp sqlVal sqlValS sqlVal_Pointed) h type1)).
    - rewrite H0 in H. auto.
    -  destruct H0. destruct x. rewrite H0 in H.   simpl in H. destruct H as [? [? ?]].  rewrite H1. clear H1. rewrite H0. simpl.  destruct (maybe_case (lista_nth n0 l0)).
       + simpl in *. rewrite H1. auto.
       + destruct H1. clear H H0. assert False ; [|tauto]. generalize H1 H2. clear H1 H2. destruct l0. apply nat_list_ind_2 with (l1:= n0)(l2:=l0).
         * intros. simpl in *. inversion H1.
         * intros. simpl in *. rewrite H1 in H2. clear H H1. pose (list_findan_ge _ _ _ b 1 maybe_row_equiv_dec) as g.  simpl in g. rewrite <- H2 in g. inversion g.
         * intros. simpl in *. inversion H1.
         * intros. apply H;[ auto |]. clear H H1. destruct c.
           {
             simpl in H2.   rewrite  (list_findan_plus _ _ _ d 0 1 maybe_row_equiv_dec) in H2.  rewrite <- plus_n_Sm in H2.  inversion H2. auto.
           }
           {
             simpl in *. inversion H2.
           }
  Qed.
  
 
  Lemma allocated_newAddr_2:
    forall h type1 addr h',
      Some (h', addr) == newAddr @ type1 @ h -> allocated @ addr @ h'.
  Proof. 
    intros. destruct addr. simpl in *. destruct (maybe_case (@nth_error (@matrixp sqlVal sqlValS sqlVal_Pointed) h type1)).
    - rewrite H0 in H. tauto.
    - destruct H0. destruct x. rewrite H0 in H.  simpl in H. destruct H as [? [? ?]].  destruct (maybe_case (@nth_error (@matrixp sqlVal sqlValS sqlVal_Pointed) h' n)).
      + rewrite H3. Unset Printing Implicit. rewrite H1 in *. clear H1. pose (eq_equiv H3) as H1. 
        rewrite H in H1.  rewrite ( list_nth_list_update  _ _ type1 (matrixpCons sqlVal
                 (lista_update (lista_finda maybe_row_equiv_dec l0) l0
                               (Some lista_repeat))) (matrixpCons sqlVal l0) h) in H1.
        inversion H1. auto.
      + destruct H3. rewrite H3. destruct x. simpl in *. pose (eq_equiv H3) as H4. 
        rewrite H in H4.  rewrite H1 in H4. simpl in *. rewrite ( list_nth_list_update  _ _ type1 (matrixpCons sqlVal
                 (lista_update (lista_finda maybe_row_equiv_dec l0) l0
                               (Some lista_repeat))) (matrixpCons sqlVal l0) h) in H4.
        * simpl in H4. destruct (maybe_case (lista_nth n0 l1)).
          {
            simpl in *. rewrite H5. pose (eq_equiv H5) as e.
            rewrite <- H4 in e.  rewrite <- H2 in e. rewrite lista_nth_lista_update in e. inversion e.
          }
          
          {
            destruct H5. simpl in *. rewrite H5. auto.
          }
        * auto. 
  Qed.
  
  Lemma readType_newAddr:
    forall h type1 addr h',
      Some (h', addr) == newAddr @ type1 @ h -> readType @ addr @ h' == Some type1.
  Proof. 
    intros. destruct addr. destruct (maybe_case (nth_error h type1)).
    - simpl in *. rewrite H0 in H. tauto.
    - destruct H0. destruct x. simpl in *. rewrite H0 in H.   simpl in H. destruct H as [? [? ?]].  rewrite H1. clear H1.  simpl. destruct (maybe_case (nth_error h' type1)).
      * simpl in *. rewrite H1. pose (eq_equiv H1) as e. rewrite H in e. rewrite ( list_nth_list_update ) with (a':=matrixpCons sqlVal l0) in e. inversion e. auto. 
      * destruct H1. simpl in *. rewrite H1. destruct x. simpl in *. destruct (maybe_case (lista_nth n0 l1)).
        {
          simpl in *. rewrite H3. pose (eq_equiv H1) as e. rewrite H in e. rewrite list_nth_list_update with (a':=matrixpCons sqlVal l0) in e. simpl in e. pose (eq_equiv H3) as e0. rewrite <- e in e0. rewrite <- H2 in e0. rewrite lista_nth_lista_update in e0. inversion e0. auto.
        }
        {
          destruct H3. simpl in *. rewrite H3. reflexivity.
        }
  Qed.

  Lemma read_update :
    forall h val pred val2 t,
      readType @ val @ h == Some t -> 
      predOfType @ pred @ t @ h ->
      h [ val , pred ↦  val2 ] [ val , pred ] == Some val2.
  Proof.
    intros. destruct val, pred. simpl in *. destruct (bool_case (n =? n1)).
    - rewrite H1 in *. simpl in *. destruct (maybe_case (nth_error h n)).
      + simpl in *. rewrite H2 in *. inversion H. 
      + simpl in *. destruct H2. rewrite H2 in *. destruct x.  simpl in *. destruct (maybe_case (lista_nth n0 l0)).
        * simpl in *. rewrite H3 in *. inversion H. 
        * simpl in *. destruct H3. rewrite H3 in *.   rewrite list_nth_list_update with (a':=matrixpCons sqlVal l0).
          {
            simpl in *.
            destruct (maybe_case (lista_nth n0 (lista_update n0 l0 (Some (lista_update n2 x val2))))).
            {
              simpl in *. rewrite H4 in *. pose (eq_equiv H4) as e. rewrite lista_nth_lista_update in e.  inversion e.
            }
            {
              simpl in *. destruct H4. rewrite H4 in *. pose (eq_equiv H4) as e. rewrite (lista_nth_lista_update) in e. simpl in e. rewrite <- e. rewrite lista_nth_lista_update. reflexivity.
            }
          }
          {
            auto.
          }
    - simpl in *. rewrite H1 in *. destruct (maybe_case (nth_error h n)).
      + simpl in *. rewrite H2 in *. tauto.
      + simpl in *. destruct H2. rewrite H2 in *. destruct x.  simpl in *. destruct (maybe_case (lista_nth n0 l0)).
        * simpl in *. rewrite H3 in *. tauto.
        * simpl in *. destruct H3. rewrite H3 in *. assert (n<>n1). apply Nat.eqb_neq. auto. congruence.
  Qed.               

  Lemma read_update_diff_addr :
    forall h val val' pred pred' val2,
      val <> val' ->
      h [ val , pred ↦ val2 ] [ val' , pred' ] == h [ val' , pred' ].
  Proof.
    intros. destruct val, pred, val', pred'. simpl in *. destruct (bool_case (n3 =? n5)).
    - rewrite H0. destruct (bool_case (n =? n1)).
      + rewrite H1. destruct (maybe_case (nth_error h n)).
        * simpl in *. rewrite H2 in *. reflexivity. 
        * destruct H2. simpl in *. rewrite H2 in *. destruct x. simpl. destruct (maybe_case (lista_nth n0 l0)). 
          {
            simpl in *. rewrite H3. destruct (Nat.eq_dec n n3).
            {
              rewrite e. rewrite list_nth_list_update with (a':= matrixpCons sqlVal l0).
              {
                rewrite e in *. clear n e. clear H0 H1. rewrite H2. reflexivity.
              }
              {
              congruence.
              }
            }
            {
               rewrite (list_nth_list_update_diff_index);[|auto]. reflexivity. 
            }
          }
          {
            destruct H3. simpl in *. rewrite H3. destruct (Nat.eq_dec n n3).
            {
              rewrite e. rewrite list_nth_list_update with (a':= matrixpCons sqlVal l0).
              {
                simpl. destruct (Nat.eq_dec n0 n4); [congruence|]. rewrite lista_nth_lista_update_diff_index; [| auto].   rewrite e in *. rewrite H2. reflexivity. 
              }
              {
                congruence.
              }
            }
            {
              rewrite list_nth_list_update_diff_index; [|auto]. reflexivity. 
            }
          }
      + rewrite H1. reflexivity. 
    - rewrite H0.  reflexivity. 
  Qed.
  
  Lemma allocated_update :
    forall h val pred val2 addr,
      allocated @ addr @ (h [ val , pred ↦  val2 ]) == allocated @ addr @ h.
  Proof.
    intros. destruct val, pred, addr. simpl. destruct (n =? n1).
    - destruct (maybe_case (nth_error h n)).
      + simpl in *. rewrite H. reflexivity. 
      + simpl in *. destruct H. rewrite H. destruct x. simpl in *. destruct (maybe_case (lista_nth n0 l0)).
        * simpl in *. rewrite H0. destruct (Nat.eq_dec n n3).
          {
            rewrite e in *. rewrite list_nth_list_update with (a':=matrixpCons sqlVal l0); [| auto].
            simpl. rewrite H. simpl. reflexivity.
          }
          {
            rewrite list_nth_list_update_diff_index; [|auto]. reflexivity.
          }
        * destruct H0. simpl in *. rewrite H0. destruct (Nat.eq_dec n n3).
          {
            rewrite e in *. rewrite list_nth_list_update with (a':=matrixpCons sqlVal l0); [| auto].
            simpl. rewrite H. simpl. destruct (Nat.eq_dec n0 n4).
            {
              rewrite e0 in *. rewrite lista_nth_lista_update. rewrite H0. reflexivity.
            }
            {
              rewrite lista_nth_lista_update_diff_index; [|auto]. reflexivity.
            }
          }
          {
            rewrite list_nth_list_update_diff_index; [|auto]. reflexivity.
          }
    - reflexivity.
  Qed.
  
          
  Lemma readType_update :
    forall h val pred val2 addr,
      readType @ addr @ (h [ val , pred ↦  val2 ]) == readType @ addr @ h.
  Proof.
    intros. destruct val, pred, addr. simpl in *. destruct (n =? n1).
    - destruct (maybe_case (nth_error h n)).
      + simpl in *. rewrite H. reflexivity. 
      + simpl in *. destruct H. rewrite H. destruct x. simpl in *. destruct (maybe_case (lista_nth n0 l0)).
        * simpl in *. rewrite H0. destruct (Nat.eq_dec n n3).
          {
            rewrite e in *. rewrite list_nth_list_update with (a':=matrixpCons sqlVal l0); [| auto].
            simpl. rewrite H. simpl. reflexivity.
          }
          {
            rewrite list_nth_list_update_diff_index; [|auto]. reflexivity.
          }
        * destruct H0. simpl in *. rewrite H0. destruct (Nat.eq_dec n n3).
          {
            rewrite e in *. rewrite list_nth_list_update with (a':=matrixpCons sqlVal l0); [| auto].
            simpl. rewrite H. simpl. destruct (Nat.eq_dec n0 n4).
            {
              rewrite e0 in *. rewrite lista_nth_lista_update. rewrite H0. reflexivity.
            }
            {
              rewrite lista_nth_lista_update_diff_index; [|auto]. reflexivity.
            }
          }
          {
            rewrite list_nth_list_update_diff_index; [|auto]. reflexivity.
          }
    - reflexivity.
  Qed.
  
  Lemma allocated_delete :
    forall h val,
      ~ allocated @ val @ (delete @ val @ h).
  Proof.
    intros. destruct val. simpl in *. destruct (maybe_case (nth_error h n)).
    + simpl in *. rewrite H. rewrite H. auto. 
    + simpl in *. destruct H. rewrite H. destruct x. simpl in *. rewrite list_nth_list_update with (a':=matrixpCons sqlVal l0); [| auto]. simpl in *. rewrite lista_nth_lista_update. auto. 
  Qed.

  Lemma allocated_delete_diff_addr :
    forall h addr1 addr',
      ~ addr1 == addr' ->
      allocated @ addr1 @ (delete @ addr' @ h) == allocated @ addr1 @ h.
  Proof.
    intros. destruct addr1, addr'.     destruct (Nat.eq_dec n n1).
    + rewrite e in *.   simpl in *. destruct (maybe_case (nth_error h n1)).
      {
        simpl in *. rewrite H0 in *. rewrite H0 in *. reflexivity. 
      }
      {
        destruct H0. simpl in *. rewrite H0.  rewrite list_nth_list_update with (a':=x);[|auto]. destruct x. simpl in *. rewrite lista_nth_lista_update_diff_index. reflexivity. intro. apply H. auto.  
      }
    + simpl in *. destruct (maybe_case (nth_error h n)). 
          {
            simpl in *. rewrite H0 in *. destruct (maybe_case (nth_error h n1)).
            {
              simpl in *. rewrite H1 in *. rewrite H0 in *. reflexivity. 
            }
            {
              destruct H1. simpl in *. rewrite H1 in *. rewrite list_nth_list_update_diff_index;[|auto]. rewrite H0. reflexivity.
            }
          }
          {
            destruct H0. simpl in *. rewrite H0. destruct (maybe_case (nth_error h n1)).
            {
              simpl in *. rewrite H1 in *. rewrite H0 in *. reflexivity. 
            }
            {
              destruct H1. simpl in *. rewrite H1 in *. rewrite list_nth_list_update_diff_index;[|auto]. rewrite H0. reflexivity.
            }
          }
          
       
  Qed.
  
  Lemma read_delete_diff_addr :
    forall h val val' pred,
      ~ val == val' ->
      (delete @ val @ h) [ val' , pred ] == h [val', pred].
  Proof.
    intros. destruct val, val', pred.     destruct (Nat.eq_dec n n1).
    - rewrite e in *.   simpl in *. destruct (bool_case (n1 =? n3)).
      + rewrite H0. destruct (maybe_case (nth_error h n1)).
      {
        simpl in *. rewrite H1 in *. rewrite H1 in *. reflexivity. 
      }
      {
        destruct H1. simpl in *. rewrite H1.  rewrite list_nth_list_update with (a':=x);[|auto]. destruct x. simpl in *. rewrite lista_nth_lista_update_diff_index. reflexivity. intro. apply H. auto.  
      }
      + rewrite H0. reflexivity. 
    - simpl in *. destruct (bool_case (n1 =? n3)).
      + rewrite H0. destruct (maybe_case (nth_error h n)). 
          {
            simpl in *. rewrite H1 in *. reflexivity. 
          }
          {
            destruct H1. simpl in *. rewrite H1. destruct x. rewrite list_nth_list_update_diff_index;[|auto]. reflexivity. 
          }
      + rewrite H0. reflexivity.
       
  Qed.

  Lemma readType_delete_diff_addr :
    forall h val val',
      ~val == val' ->
      readType @ val' @ (delete @ val @ h) == readType @ val' @ h.
  Proof.
    intros. destruct val, val'.     destruct (Nat.eq_dec n n1).
    - rewrite e in *.   simpl in *.  destruct (maybe_case (nth_error h n1)).
      {
        simpl in *. rewrite H0 in *. rewrite H0 in *. reflexivity. 
      }
      {
        destruct H0. simpl in *. rewrite H0.  rewrite list_nth_list_update with (a':=x);[|auto]. destruct x. simpl in *. rewrite lista_nth_lista_update_diff_index. reflexivity. intro. apply H. auto.  
      }
      
    - simpl in *.  destruct (maybe_case (nth_error h n)). 
          {
            simpl in *. rewrite H0 in *. reflexivity. 
          }
          {
            destruct H0. simpl in *. rewrite H0. destruct x. rewrite list_nth_list_update_diff_index;[|auto]. reflexivity. 
          }
  Qed.
  
  Lemma update_update :
    forall h val pred val2 val3,
      h [ val , pred ↦  val2 ] [ val , pred ↦ val3 ] == h  [ val , pred ↦ val3 ].
  Proof.
    intros. destruct val, pred.     simpl in *. destruct (bool_case (n =? n1)). 
    - rewrite H.   simpl in *.  destruct (maybe_case (nth_error h n)).
      {
        simpl in *. rewrite H0 in *. rewrite H0 in *. reflexivity. 
      }
      {
        destruct H0. simpl in *. rewrite H0.  destruct x. rewrite list_nth_list_update with (a':=matrixpCons sqlVal l0);[|auto]. simpl. rewrite list_update_list_update. destruct (maybe_case (lista_nth n0 l0)).
        {
          simpl in *. rewrite H1. simpl. rewrite H1. reflexivity.
        }
        {
          simpl in *. destruct H1. rewrite H1. simpl. rewrite lista_nth_lista_update. rewrite lista_update_lista_update. rewrite lista_update_lista_update. reflexivity.
        }
      }
    - rewrite H. reflexivity.
  Qed.
  

  Lemma update_update_diff_addr :
    forall h val val' pred val2 val3,
      ~ val == val'->
      h [ val , pred ↦  val2 ] [ val' , pred ↦ val3 ] == h [ val' , pred ↦ val3 ] [ val , pred ↦ val2 ].
  Proof.
    intros. destruct val, val', pred.     simpl in *. destruct (bool_case (n1 =? n3)). 
    - rewrite H0.   simpl in *.  destruct (bool_case (n =? n3)).
      + 
        rewrite H1. simpl in *. assert (n = n1).
        transitivity n3. apply Nat.eqb_eq. auto. symmetry. apply Nat.eqb_eq. auto.
        assert (n0 <> n2) as z.
        intro. apply H. auto. 
        rewrite H2 in *. clear H2.  destruct (maybe_case (nth_error h n1)).
        {
          simpl in *. rewrite H2 in *.  rewrite H2 in *.  reflexivity. 
        }
        {
          destruct H2. simpl in *. rewrite H2. destruct x. simpl. rewrite list_nth_list_update with (a':=matrixpCons sqlVal l0);[|auto]. rewrite list_update_list_update. rewrite list_nth_list_update with (a':=matrixpCons sqlVal l0);[|auto]. rewrite list_update_list_update. destruct (maybe_case (lista_nth n0 l0)).
          {
            simpl in *. rewrite H3. simpl. destruct (maybe_case (lista_nth n2 l0)).
            {
              simpl in *. rewrite H4. simpl. 
              rewrite H3. reflexivity.
            }
            {
              destruct H4. simpl in *. rewrite H4. simpl. 
              rewrite lista_nth_lista_update_diff_index;[|auto].
              rewrite H3. reflexivity. 
            }
          }
          {
            destruct H3. simpl in *. rewrite H3. simpl.
            rewrite lista_nth_lista_update_diff_index; [| auto]. destruct (maybe_case (lista_nth n2 l0)).
            {
              simpl in *. rewrite H4. simpl. 
              rewrite H3. reflexivity.
            }
            {
              destruct H4. simpl in *. rewrite H4. simpl. 
              rewrite lista_nth_lista_update_diff_index;[|auto].
              rewrite H3. rewrite lista_update_lista_update_diff_index;[|auto]. reflexivity. 
            }
          }
        }
      + rewrite H1. reflexivity. 
    - rewrite H0. reflexivity.
  Qed.
  
  Lemma update_update_diff_pred :
    forall h val pred pred' val2 val3,
      ~ pred == pred' ->
      h [ val , pred ↦  val2 ] [ val , pred' ↦ val3 ] == h [ val , pred' ↦ val3 ] [ val , pred ↦ val2 ].
  Proof.
    intros. destruct val, pred, pred'.     simpl in *. destruct (bool_case (n =? n3)). 
    - rewrite H0.   simpl in *.  destruct (bool_case (n =? n1)).
      + 
        rewrite H1. simpl in *. assert (n1 = n3).
        transitivity n. symmetry. apply Nat.eqb_eq. auto. apply Nat.eqb_eq. auto.
        assert (n2 <> n4) as z.
        intro. apply H. auto. 
        rewrite H2 in *. clear H2.  destruct (maybe_case (nth_error h n)).
        {
          simpl in *. rewrite H2 in *.  rewrite H2 in *.  reflexivity. 
        }
        {
          destruct H2. simpl in *. rewrite H2. destruct x. simpl. rewrite list_nth_list_update with (a':=matrixpCons sqlVal l0);[|auto]. rewrite list_update_list_update. rewrite list_nth_list_update with (a':=matrixpCons sqlVal l0);[|auto]. rewrite list_update_list_update. destruct (maybe_case (lista_nth n0 l0)).
          {
            simpl in *. rewrite H3. simpl. rewrite H3.  reflexivity. 
          }
          {
            destruct H3. simpl in *. rewrite H3. simpl.
            rewrite lista_nth_lista_update. rewrite lista_update_lista_update. rewrite lista_nth_lista_update.  rewrite lista_update_lista_update.   rewrite lista_update_lista_update_diff_index;[|auto]. reflexivity. 
          }
        }
      + rewrite H1. reflexivity. 
    - rewrite H0. reflexivity.
  Qed.

  Lemma delete_update :
    forall h val pred val2,
      delete @ val @ (h [ val , pred ↦  val2 ]) == delete @ val @ h.
  Proof.
    intros. destruct val, pred.     simpl in *. destruct (bool_case (n =? n1)). 
    - rewrite H.   simpl in *.  destruct (maybe_case (nth_error h n)).
      {
        simpl in *. rewrite H0 in *. rewrite H0 in *. reflexivity. 
      }
      {
        destruct H0. simpl in *. rewrite H0.  destruct x. rewrite list_nth_list_update with (a':=matrixpCons sqlVal l0);[|auto]. simpl. rewrite list_update_list_update. destruct (maybe_case (lista_nth n0 l0)).
        {
          simpl in *. rewrite H1. simpl. reflexivity.
        }
        {
          simpl in *. destruct H1. rewrite H1. simpl. rewrite lista_update_lista_update. reflexivity.
        }
      }
    - rewrite H.   reflexivity.
  Qed.
  
  Lemma delete_update_diff_addr :
    forall h val val' pred val2,
      ~ val == val'->
      delete @ val' @ (h [ val , pred ↦  val2 ]) == (delete @ val' @ h) [ val , pred ↦ val2 ].
  
  Proof.
    intros. destruct val, val', pred.     simpl in *. destruct (bool_case (n =? n3)).
    + rewrite H0. simpl in *.  destruct (maybe_case (nth_error h n)).
      {
        simpl in *. rewrite H1 in *.  destruct (Nat.eq_dec n1 n).
        {
          rewrite e in *. rewrite H1. rewrite H1. reflexivity. 
        }
        {
          destruct (maybe_case (nth_error h n1)).
          {
            simpl in *. rewrite H2 in *. rewrite H1. reflexivity.
          }
          {
            destruct H2. simpl in *. rewrite H2 in *. destruct x. simpl. 
            rewrite list_nth_list_update_diff_index;[|auto].  rewrite H1.  reflexivity. 
          }
        }
      }
      {
        destruct H1. simpl in *. rewrite H1. destruct x. simpl. destruct (Nat.eq_dec n1 n). 
        {
          rewrite e. rewrite H1. simpl. repeat (rewrite list_nth_list_update with (a':=matrixpCons sqlVal l0);[|auto]). repeat rewrite list_update_list_update.  assert (n0 <> n2). intro; apply H; auto.  simpl. rewrite lista_nth_lista_update_diff_index;[|auto]. destruct (maybe_case (lista_nth n0 l0)).
          {
            simpl in *. rewrite H3. simpl.  reflexivity.
          }
          {
            destruct H3. simpl in *. rewrite H3. simpl. rewrite lista_update_lista_update_diff_index;[|auto].  reflexivity. 
          }
        }
        {
          destruct (maybe_case (lista_nth n0 l0)). 
          {
            simpl in *. rewrite H2. simpl. destruct (maybe_case (nth_error h n1)).
            {
              simpl in *. 
              rewrite H3. rewrite list_nth_list_update_diff_index;[|auto]. rewrite H3. rewrite H1. simpl. rewrite H2. reflexivity.
            }
            {
              destruct H3. simpl in *. rewrite H3. simpl. 
              rewrite list_nth_list_update_diff_index;[|auto].
              rewrite list_nth_list_update_diff_index;[|auto].
              rewrite H3. rewrite H1.  destruct x. simpl. rewrite H2. rewrite list_update_list_update_diff_index ;[|auto]. reflexivity. 
            }
          }
          {
            destruct H2. simpl in *. rewrite H2.  destruct (maybe_case (nth_error h n1)).
            {
              simpl in *. 
              rewrite H3. rewrite list_nth_list_update_diff_index;[|auto]. rewrite H3. rewrite H1. simpl. rewrite H2. reflexivity.
            }
            {
              destruct H3. simpl in *. rewrite H3. simpl. 
              rewrite list_nth_list_update_diff_index;[|auto].
              rewrite list_nth_list_update_diff_index;[|auto].
              rewrite H3. rewrite H1.  destruct x. simpl. rewrite H2. rewrite list_update_list_update_diff_index ;[|auto]. reflexivity. 
            }
          }
        }
      }        
    + rewrite H0. simpl. reflexivity. 
  Qed.
  
  Lemma delete_delete :
    forall h val val',
      delete @ val' @ (delete @ val @ h) == delete @ val @ (delete @ val' @ h).
  Proof.
    intros. destruct val, val'.     simpl in *. destruct (maybe_case (nth_error h n)).
    {
      simpl in *. rewrite H in *.  destruct (maybe_case (nth_error h n1)).
      {
        simpl in *. rewrite H0 in *.  rewrite H. reflexivity. 
      }
      {
        destruct H0. simpl in *. rewrite H0. destruct x. simpl. destruct (Nat.eq_dec n n1).
        {
          rewrite e in *. rewrite H in H0. inversion H0.
        }
        {
          rewrite list_nth_list_update_diff_index; [| auto]. rewrite H. reflexivity.
        }
      }
    }
    {
      destruct H. simpl in *. rewrite H.  destruct (Nat.eq_dec n n1).
      {
        rewrite e in *.  destruct x. rewrite H. simpl.   repeat (rewrite list_nth_list_update with (a':=matrixpCons sqlVal l0); [|auto]).  simpl. destruct (Nat.eq_dec n0 n2).
        {
          rewrite e0 in *. reflexivity.
        }
        {
          rewrite lista_update_lista_update_diff_index; [|auto]. rewrite list_update_list_update. rewrite list_update_list_update. reflexivity. 
        }
      }
      {
        rewrite list_nth_list_update_diff_index; [| auto]. destruct (maybe_case (nth_error h n1)).
        {
          simpl in *. rewrite H0 in *.  rewrite H. reflexivity. 
        }
        {
          destruct H0. simpl in *. rewrite H0. 
          rewrite list_nth_list_update_diff_index; [| auto]. rewrite H. destruct x, x0. simpl. rewrite list_update_list_update_diff_index;[|auto]. reflexivity.
        }
      }
    }
  Qed.

      
  Lemma update_newAddr_1 :
    forall h val pred val2 type1 h' addr,
      newAddr @ type1 @ h == Some (h', addr) ->
      val <> addr ->
      newAddr @ type1 @ (h [ val , pred ↦  val2 ]) == Some (h' [ val , pred ↦  val2 ], addr).
  Proof.
    intros. destruct val, pred, addr . destruct (maybe_case (nth_error h type1)).
    - simpl in *. rewrite H1 in *.  inversion H. 
    - destruct H1. simpl (newAddr @ _ @ _) in H. simpl in H1. rewrite H1 in H. simpl in H. destruct x.  destruct H as [? [? ?]]. simpl in H. assert (Some (h' [(n, n0), (n1, n2) ↦ val2] , (n3, n4)) == Some ((list_update' type1 h
           (matrixpCons sqlVal
              (lista_update (lista_finda maybe_row_equiv_dec l0) l0
                            (Some lista_repeat)))) [(n, n0), (n1, n2) ↦ val2] , (n3, n4))).
      apply Some_Proper. split;[| reflexivity]. evalproper. symmetry. auto. rewrite H4. clear H H4. rewrite H2 in *.  clear type1 H2. simpl in H3. simpl. destruct_bool (n =? n1).
      + destruct_maybe (nth_error h n).
        * rewrite H1. simpl. assert (n3 <> n).  intro. rewrite H4 in H1.  rewrite  H1 in H2. inversion H2. rewrite list_nth_list_update_diff_index;[|auto]. rewrite H2. split. reflexivity. auto.
        * destruct x.  simpl. destruct (Nat.eq_dec n n3).
          {
            rewrite e in *. simpl. repeat (rewrite list_nth_list_update with (a':=matrixpCons sqlVal l0);[|auto]). rewrite H1 in H4. 
            inversion H4. rewrite H5 in H3.  rewrite H3 in *. simpl.  assert (n4 <> n0).
            intro. apply H0. auto.
            destruct_maybe (lista_nth n0 l1).
            {
              repeat rewrite list_update_list_update. simpl.  rewrite H3 in *.
              rewrite lista_nth_lista_update_diff_index;[|auto]. rewrite H6.  split. reflexivity. auto.
            }
            {
              rewrite list_update_list_update. rewrite list_update_list_update.  rewrite lista_nth_lista_update_diff_index; [| auto]. rewrite H7. simpl. rewrite lista_finda_lista_update. rewrite H3. rewrite lista_update_lista_update_diff_index;[|auto].   split. reflexivity. auto.
              rewrite H7. intro. inversion H6. intro. inversion H6.
            }
          }
          {
            rewrite list_nth_list_update_diff_index;[|auto]. rewrite H1.  rewrite list_nth_list_update_diff_index; [| auto]. simpl. rewrite H4. simpl. rewrite list_update_list_update_diff_index; [|auto]. split. reflexivity. auto.
          }
      + rewrite H1. simpl. split. reflexivity .
        auto.
  Qed.
  
  Lemma update_newAddr_2 :
    forall h val pred val2 type1,
      newAddr @ type1 @ h == None ->
      newAddr @ type1 @ (h [ val , pred ↦  val2 ]) == None.
Proof.
    intros. destruct val, pred . destruct (maybe_case (nth_error h type1)).
    - rewrite <- H. clear H. simpl in *. rewrite H0. destruct_bool (n =? n1).
      + destruct_maybe (nth_error h n).
        * rewrite H0. reflexivity.
        * destruct x.  simpl. destruct (Nat.eq_dec n type1).
          {
            rewrite e in *. simpl. repeat (rewrite list_nth_list_update with (a':=matrixpCons sqlVal l0);[|auto]). rewrite H0 in H2. 
            inversion H2.
          }
          {
            rewrite list_nth_list_update_diff_index;[|auto]. rewrite H0.  reflexivity. 
          }
      + rewrite H0.  reflexivity .
    - simpl in *. destruct H0. rewrite H0 in *.  inversion H. 
  Qed.

  Lemma delete_newAddr :
    forall h type1 h' addr,
      newAddr @ type1 @ h == Some (h', addr) ->
      delete @ addr @ h' == h.
  Proof.
    intros. destruct addr . destruct (maybe_case (nth_error h type1)).
    - simpl in *. rewrite H0 in *.  inversion H. 
    - destruct H0. simpl (newAddr @ _ @ _) in H. simpl in H0. rewrite H0 in H. simpl in H. destruct x.  destruct H as [? [? ?]]. simpl in H. rewrite <- H. clear H. simpl in H2. rewrite H2 in *.  rewrite H1 in *. clear type1 H1. simpl. repeat (rewrite list_nth_list_update with (a':=matrixpCons sqlVal l0);[|auto]). simpl. repeat rewrite list_update_list_update. simpl.
      rewrite lista_update_lista_update. rewrite list_update_list_nth.  reflexivity. rewrite H0. simpl. rewrite <- H2.  rewrite lista_update_lista_finda. reflexivity. 
  Qed.



    Arguments _lookupByObject pred1 val1 h /.
    Arguments _lookupByPred pred1 h /.
    Arguments _readMatrixCol {A AS AP} n mat /.
    Arguments _readWholeCol {A AS AP} n l /.
    Arguments _filterSomeVal val1 /.
    Arguments _filterVal val1 val2 /.

    Arguments _readCol  {A AS AP} n l / .
    
    Arguments SQLAddrType.addr /.
    Arguments SQLAddrType.addrS /.
    Arguments sqlAddr /.
    Arguments sqlAddrS /.
    Arguments SQLValType.val /.
    Arguments SQLValType.valS /.
    Arguments SQLTypeType.type /.
    Arguments SQLTypeType.typeS /.
  Section AndMonoid.

    
    Existing Instance and_Monoid.

    

    Lemma lookupByObject_table_0 : forall n val a b,
      lookupByObject @ (0, n) @ val @ (a :: b) = mapS @ (getAddr @ 0) @ (lista_filter_indexS @ (filterSomeVal @ val) @ (tableColGetter @ n @ a)).
    Proof.
      intros. reflexivity.
    Qed.

    
    Lemma lookupByObject_table_S : forall m n val a b,
      lookupByObject @ (S m, n) @ val @ (a :: b) = mapS @ (getAddr @ S m  ∘ addrToRowS) @ (lookupByObject @ (m, n) @ val @ b).
    Proof.
      intros. simpl. destruct_maybe (nth_error b m).
      auto.
      rewrite map_map. reflexivity. 
    Qed.
    
    Lemma read_table_diff_table : forall t1 t2 ci ri a,
      t1 <> t2 -> read @ (t1, ri) @ (t2, ci) @ a = None.
    Proof.
      intros. simpl. destruct_bool (t1 =? t2).
      destruct H. apply Nat.eqb_eq.  auto.
      reflexivity.
    Qed.
    
    Lemma read_table_0 : forall ci a b,
      cycle3S @ read @ (0, ci) @ (a :: b) ∘ getAddr @ 0 == cycle3S @ tableCellGetter @ ci @ a.
    Proof.
      intros. simpl_equiv. rewrite normalize_cycle3S. normalizecomp. rewrite normalize_cycle3S. reflexivity.
    Qed.
    Lemma read_table_S : forall n ci a b,
      cycle3S @ read @ (S n, ci) @ (a :: b) ∘ getAddr @ (S n) == cycle3S @ read @ (n, ci) @ b ∘ getAddr @ n.
    Proof.
      intros. simpl_equiv. normalizecomp. repeat rewrite normalize_cycle3S. reflexivity.  
    Qed.
    


    Lemma tableCellGetter_comp : forall ci a,
                                             cycle3S @ tableCellGetter @ ci @ a == flipS @ lista_nthS @ (tableColGetter @ ci @ a).
    Proof.
      intros. destruct a. destruct l0. simpl_equiv. apply nat_list_ind_2 with (l1:=a) (l2:=l0).
      - simpl. auto.
      - intros. simpl. reflexivity.
      - intros. simpl. reflexivity.
      - auto.
    Qed.

    Lemma addrToRowS_getAddr : forall n, addrToRowS ∘ getAddr @ n == idS.
    Proof.
      intros. simpl. arrequiv.
    Qed.
    Lemma read_lookupByObject :
      forall pred val h,
        fold @ ((equivS @  Some val) ∘ (cycle3S @ read @ pred @ h )  <$> lookupByObject @ pred @ val @ h) == True.
    Proof.
      intros. destruct pred. apply nat_list_ind_2 with (l1:=n) (l2:=h).
      - simpl. reflexivity.
      - intros. rewrite lookupByObject_table_0.  simpl fmap. setoid_rewrite (mapS_mapS).  rewrite comp_associativity. rewrite read_table_0.  rewrite tableCellGetter_comp. apply filterTrue.  intros. simpl in H0. simpl. destruct b0. destruct (SQLValType.equiv_dec val s). auto. inversion H0. inversion H0.
      - intros. simpl. tauto.
      - intros. rewrite lookupByObject_table_S.  simpl fmap. setoid_rewrite (mapS_mapS).  rewrite <- comp_associativity.  setoid_rewrite comp_associativity at 2.  rewrite read_table_S.
        rewrite <- H. clear H. evalproper. destruct b, d. 
        + reflexivity. 
        + intros. rewrite lookupByObject_table_0.  rewrite read_table_0. simpl fmap. setoid_rewrite  mapS_mapS. rewrite (comp_associativity (getAddr @ 0) (cycle3S @ read @ (0, n0) @ (t0 :: d)) (equivS @ Some val)). rewrite read_table_0. reflexivity .
        + intros. reflexivity.
        + intros. rewrite lookupByObject_table_S. rewrite read_table_S. simpl fmap. setoid_rewrite mapS_mapS. rewrite (comp_associativity (getAddr @ S b ∘ addrToRowS) (cycle3S @ read @ (S b, n0) @ (t0 :: d)) (equivS @ Some val)). rewrite <- (comp_associativity addrToRowS (getAddr @ S b) (cycle3S @ read @ (S b, n0) @ (t0 :: d))). rewrite read_table_S. rewrite (comp_associativity (getAddr @ S b ∘ addrToRowS) addrToRowS (equivS @ Some val ∘ (cycle3S @ read @ (b, n0) @ d ∘ getAddr @ b))). rewrite <- (comp_associativity addrToRowS (getAddr @ S b) addrToRowS). rewrite addrToRowS_getAddr. rewrite comp_left_unit. reflexivity.
    Qed.
    
    Lemma lookupByPred_table_0 : forall n a b,
      lookupByPred @ (0, n) @ (a :: b) = mapS @ (getAddr @ 0 *** idS) @ (lista_filter_indexS' @ (tableColGetter @ n @ a)).
    Proof.
      intros. reflexivity.
    Qed.

    Arguments _lookupByPred pred1 h /. 
    Lemma lookupByPred_table_S : forall m n a b,
      lookupByPred @ (S m, n) @ (a :: b) = mapS @ ((getAddr @ S m  ∘ addrToRowS) *** idS) @ (lookupByPred @ (m, n) @ b).
    Proof.
      intros. simpl. destruct_maybe (nth_error b m).
      auto.
      rewrite map_map. destruct x. auto. generalize (@lista_filter_index' sqlVal sqlValS
        (@lista_map (option (lista sqlVal))
           (@optionS (lista sqlVal) (@listaS sqlVal sqlValS sqlVal_Pointed))
           (maybe_Pointed (lista sqlVal)) (option sqlVal)
           (@optionS sqlVal sqlValS) (maybe_Pointed sqlVal)
           (@injF (option (lista sqlVal)) (option sqlVal)
              (@optionS (lista sqlVal)
                 (@listaS sqlVal sqlValS sqlVal_Pointed))
              (@optionS sqlVal sqlValS)
              (@_readCol sqlVal sqlValS sqlVal_Pointed n)
              (proper_xx nat (option (lista sqlVal)) 
                 (option sqlVal) natS
                 (@optionS (lista sqlVal)
                    (@listaS sqlVal sqlValS sqlVal_Pointed))
                 (@optionS sqlVal sqlValS)
                 (@_readCol sqlVal sqlValS sqlVal_Pointed) n
                 (@_readCol_Proper sqlVal sqlValS sqlVal_Pointed)))
           (@readCol_PointedFunction sqlVal sqlValS sqlVal_Pointed n) l0)).  intros. induction l1.
      - reflexivity.
      - rewrite map_cons. rewrite map_cons. f_equal.
        + destruct a0. reflexivity.
        + apply IHl1.
    Qed.

    Lemma read_lookupByPred :
      forall pred h,
        fold @ (uncurryS @ equivS ∘ (cycle3S @ read @ pred @ h *** SomeS ) <$> lookupByPred @ pred @ h) == True.
    Proof.
      intros. destruct pred.  apply nat_list_ind_2 with (l1:=n) (l2:=h).
      - simpl. reflexivity.
      - intros. rewrite lookupByPred_table_0. simpl fmap. setoid_rewrite (mapS_mapS).  rewrite comp_associativity. rewrite pairing_comp.  rewrite read_table_0.  rewrite tableCellGetter_comp. rewrite comp_right_unit. apply filterTrue'.  
      - intros. simpl. tauto.
      - intros. rewrite lookupByPred_table_S.  simpl fmap. setoid_rewrite (mapS_mapS). setoid_rewrite comp_associativity.  rewrite pairing_comp. rewrite <- comp_associativity.    rewrite read_table_S.
 rewrite comp_right_unit. rewrite <- H. clear H. evalproper. destruct b, d. 
        + reflexivity. 
        + intros. rewrite lookupByPred_table_0.  rewrite read_table_0. simpl fmap. setoid_rewrite  mapS_mapS. rewrite (comp_associativity (getAddr @ 0 *** idS) (cycle3S @ read @ (0, n0) @ (t0 :: d) *** SomeS) (uncurryS @ equivS)). rewrite pairing_comp.  rewrite read_table_0. rewrite comp_associativity.  rewrite pairing_comp. rewrite comp_associativity.  rewrite addrToRowS_getAddr. rewrite (comp_right_unit (cycle3S @ tableCellGetter @ n0 @ t0)). reflexivity.
        + intros. reflexivity.
        + intros. rewrite lookupByPred_table_S. rewrite read_table_S. simpl fmap. setoid_rewrite mapS_mapS. rewrite (comp_associativity (getAddr @ S b ∘ addrToRowS *** idS) (cycle3S @ read @ (S b, n0) @ (t0 :: d) *** SomeS) (uncurryS @ equivS)). rewrite pairing_comp. rewrite <- (comp_associativity addrToRowS (getAddr @ S b) (cycle3S @ read @ (S b, n0) @ (t0 :: d))). rewrite read_table_S. rewrite   (comp_associativity).  rewrite pairing_comp. rewrite (comp_associativity (getAddr @ S b ∘ addrToRowS) addrToRowS ((cycle3S @ read @ (b, n0) @ d ∘ getAddr @ b))). rewrite <- (comp_associativity addrToRowS (getAddr @ S b) addrToRowS). rewrite addrToRowS_getAddr. rewrite comp_left_unit. reflexivity.
    Qed.
        

  End AndMonoid.

  Section OrMonoid.
    
    Existing Instance or_Monoid.

    Lemma eqb_x_x : forall x, x =? x = true.
    Proof.
      intros. pose (Nat.eqb_eq x x). apply i. reflexivity.
    Qed.

    Lemma nth_map : forall A B (f  : A -> B) (a : A) n (l : list A),
                      nth n (map f l) (f a) = f (nth n l a).
    Proof.
      intros. apply nat_list_ind_2 with (l1:=n) (l2:=l0).
      reflexivity.
      intros. simpl. reflexivity.
      intros. simpl. reflexivity.
      intros. simpl. auto.
    Qed.
    
    Lemma lookupByObject_read :
      forall addr pred val h,
        h [addr, pred] == Some val ->
        fold @ (equivS @ addr <$> lookupByObject @ pred @ val @ h) == True.
    Proof.
      intros. destruct addr, pred.  simpl in *. destruct (Nat.eq_dec n n1).
      - rewrite e in *. clear n e. rewrite eqb_x_x in H. destruct_maybe (nth_error h n1).
        + inversion H.
        + destruct x. simpl in *. rewrite map_map. refine (filterTrue_one _ _ _ (injF (fun x : nat => n1 = n1 /\ n0 = x) _) (injF
              (caseMaybe
                 (injF (_filterVal val)
                    (proper_xx sqlVal sqlVal bool sqlValS sqlValS boolS
                       _filterVal val _filterVal_Proper)) false)
              (proper_xx bool (option sqlVal) bool boolS 
                 (optionS sqlValS) boolS
                 (caseMaybe
                    (injF (_filterVal val)
                       (proper_xx sqlVal sqlVal bool sqlValS sqlValS boolS
                          _filterVal val _filterVal_Proper))) false
                 (injF3_1 caseMaybe
                    (caseMaybe_Proper sqlVal bool sqlValS boolS)
                    (injF (_filterVal val)
                       (proper_xx sqlVal sqlVal bool sqlValS sqlValS boolS
                          _filterVal val _filterVal_Proper))))) (lista_map
              (injF (_readCol n2)
                 (proper_xx nat (option (lista sqlVal)) 
                    (option sqlVal) natS (optionS (listaS sqlValS))
                    (optionS sqlValS) _readCol n2
                    (_readCol_Proper sqlVal_Pointed)))
              (readCol_PointedFunction n2) l0) _ _).
          * simpl. reflexivity. 
          * simpl. exists n0. split ; [| auto]. destruct l0. simpl in *. rewrite (nth_map _ _ (fun a : option (lista sqlVal) =>
           match a with
           | Some l' => Some (lista_nth n2 l')
           | None => None
           end) None). destruct_maybe ( match nth n0 l0 None with
     | Some l' => Some (lista_nth n2 l')
     | None => None
                                        end). inversion H. inversion H. destruct (SQLValType.equiv_dec val val). reflexivity. destruct n. reflexivity.
      - simpl in H. destruct_bool (n =? n1).
        + destruct n3. apply Nat.eqb_eq. auto.
        + inversion H.
    Qed.
    
    Lemma lookupByPred_read :
      forall addr pred val h,
        h [addr, pred] == Some val ->
        fold @ (equivS @ (addr, val)  <$> lookupByPred @ pred @ h) == True.
    Proof.
      intros. destruct addr, pred.  simpl in *. destruct (Nat.eq_dec n n1).
      - rewrite e in *. clear n e. rewrite eqb_x_x in H. destruct_maybe (nth_error h n1).
        + inversion H.
        + destruct x. simpl in *. rewrite map_map. refine (filterTrue_one' _ _ (injF (fun x : nat * sqlVal =>
         let (c, d) := let (a, c) := x in (n1, a, c) in
         (let (c0, d0) := c in n1 = c0 /\ n0 = d0) /\ val = d) _) (lista_map
              (injF (_readCol n2)
                 (proper_xx nat (option (lista sqlVal)) 
                    (option sqlVal) natS (optionS (listaS sqlValS))
                    (optionS sqlValS) _readCol n2
                    (_readCol_Proper sqlVal_Pointed)))
              (readCol_PointedFunction n2) l0) _).
          * simpl. exists n0. exists val. split ; [| auto]. destruct l0. simpl in *. rewrite (nth_map _ _ (fun a : option (lista sqlVal) =>
           match a with
           | Some l' => Some (lista_nth n2 l')
           | None => None
           end) None). auto. 
      - simpl in H. destruct_bool (n =? n1).
        + destruct n3. apply Nat.eqb_eq. auto.
        + inversion H.
    Unshelve.
    autounfold. intros. destruct x, y. destruct H0. simpl in H0, H2. rewrite H0, H2. reflexivity. 
    Qed.
    
    
  End OrMonoid.
  




End SQLHeap.