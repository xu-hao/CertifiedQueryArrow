Require Import Definitions Algebra.Monoid Expr Algebra.SetoidCat Algebra.Maybe Tactics Algebra.ListUtils Algebra.Functor Algebra.Applicative Algebra.Alternative Algebra.FoldableFunctor Algebra.PairUtils Algebra.Maybe Algebra.Monad Algebra.Lens.Lens Algebra.Lens.MaybeLens ListLens Utils SetoidUtils SQL Pointed Lista Matrixp GenUtils.
Require Import Coq.Structures.DecidableTypeEx List SetoidClass PeanoNat FMapWeakList Basics Coq.Arith.Compare_dec.

Existing Instance maybe_Monad.
Instance maybeFunctor : @Functor maybe (@maybeS) := monadFunctor.
Instance maybe_Applicative : @Applicative maybe (@maybeS) _ := monad_Applicative.
  
(*  (* based on https://github.com/bacam/coqjvm/blob/master/coqjvm/ListExt.v *)
  Fixpoint list_update {A:Type} {AS : Setoid A} (l:list A) (n:nat) (t:A -> maybe A) {struct n} : maybe (list A) :=
  match n, l with
    | 0,   old_v::rest => match t old_v with
                            | None => None
                            | Some v => Some (v::rest)
                          end
  | S n, v'::rest    => match list_update rest n t with None => None | Some rest' => Some (v'::rest') end
  | _,   nil         => None
  end.

  Instance listUpdate_Proper A (AS : Setoid A): Proper (equiv ==> equiv ==> (equiv ==> equiv) ==> equiv) (@list_update A AS).
  Proof.
    autounfold. intros. rewrite H0.  clear x0 H0. generalize y0 H. clear H. apply list_ind_2 with (l1:=x) (l2:=y).
    intros. induction y2.
    simpl. auto.
    simpl. auto.
    intros. inversion H0.
    intros. inversion H0.
    intros. inversion H0. induction y2.
    simpl. assert (x1 a == y1 c). apply H1. auto. destruct (x1 a), (y1 c). constructor. auto. auto. inversion H8. inversion H8. auto.
    simpl. assert (list_update b y2 x1 == list_update d y2 y1). apply H. auto. destruct (list_update b y2 x1), (list_update d y2 y1). constructor. auto. auto. inversion H8. inversion H8. auto.
  Qed.

  Fixpoint list_update' {A:Type} (l:list A) (n:nat) (t:A ->  A) {struct n} :  list A :=
  match n, l with
    | 0,   old_v::rest => t old_v::rest
  | S n, v'::rest    =>  v'::list_update' rest n t 
  | _,   nil         => nil
  end.

  Instance listUpdate'_Proper A (AS : Setoid A): Proper (equiv ==> equiv ==> (equiv ==> equiv) ==> equiv) (@list_update' A).
  Proof.
    autounfold. intros. rewrite H0.  clear x0 H0. generalize y0 H. clear H. apply list_ind_2 with (l1:=x) (l2:=y).
    intros. induction y2.
    simpl. auto.
    simpl. auto.
    intros. inversion H0.
    intros. inversion H0.
    intros. inversion H0. induction y2.
    simpl. assert (x1 a == y1 c). apply H1. auto. constructor. auto. auto. 
    simpl. constructor. auto. apply H. auto.
  Qed.
 *)


(* Definition _maybe_mappend {C} {CS : Setoid C} {mon : @Monoid C CS} (a b : maybe C) : maybe C :=
  match a with
    | None => b
    | Some a' => match b with
                   | None => a
                   | Some b' => Some (mappend @ a' @ b')
                 end
  end
.

Instance _maybe_mappend_Proper {C} {CS : Setoid C} {mon : @Monoid C CS} : Proper (equiv ==> equiv ==> equiv) _maybe_mappend.
Proof.
  autounfold. intros. unfold _maybe_mappend. matchequiv. matchequiv. simpl in *. rewritesr.  auto. auto.
Qed.

Definition maybe_mappend {C} {CS : Setoid C} {mon : @Monoid C CS}: maybeS CS ~> maybeS CS ~~> maybeS CS := injF2 _maybe_mappend _.
      
Instance maybe_A_Monoid {C} {CS : Setoid C} {mon : @Monoid C CS}: @Monoid (maybe C) _.
Proof.
  exists (None) (maybe_mappend).
  intros. simpl. destruct a. reflexivity. auto.
  intros. simpl. destruct a. simpl. reflexivity. simpl. auto.
  intros. simpl. destruct a. simpl. destruct b. simpl. destruct c. rewrite associativity_monoid. reflexivity. reflexivity. destruct c. simpl. reflexivity. simpl. reflexivity. destruct b. simpl. destruct c. reflexivity. reflexivity. destruct c. simpl. reflexivity. simpl. auto.
Defined. *)



Definition unionRows : listaS (maybeS rowS) ~> listaS (maybeS rowS) ~~> listaS (maybeS rowS) :=
  lista_zipWithS maybe_first_mappend.

Definition minS := injF2 min _.

Existing Instance sqlVal_Pointed.

Definition _unionTables (tab1 tab2 : matrixp sqlVal) : matrixp sqlVal :=
  matrixpConsS @ (unionRows @ (tableRowsGetter @ tab1) @ (tableRowsGetter @ tab2)).

Instance _unionTables_Proper : Proper (equiv ==> equiv ==> equiv) _unionTables.
Proof.
  autounfold. intros. unfold _unionTables. rewritesr.
Qed.

Definition unionTables := injF2 _unionTables _.

Definition unionDatabases : databaseS ~> databaseS ~~> databaseS :=
  list_zipWithS' @ unionTables.



Definition caseSqlVal {A} {AS : Setoid A} (nat1 : natS ~> AS) (addr1 : natS ~*~ natS ~> AS) (row1 : listS sqlValS ~> AS) val1 : A :=
  match val1 with
    | vNat n => nat1 @ n
    | vAddr a => addr1 @ a
  end
.

Instance caseSqlVal_Proper A AS : Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv) (@caseSqlVal A AS).
Proof.
  autounfold. intros. unfold caseSqlVal. simpl in H2. rewrite H2. destruct y2. 
  rewritesr.
  rewritesr. 
Qed.

Definition caseSqlValS {A AS} := injF4 (@caseSqlVal A AS) _.

Definition extractAddrS : sqlValS ~> maybeS (natS ~*~ natS) :=
  caseSqlValS
    @ (constS _ @ None)
    @ (SomeS)
    @ (constS _ @ None).

Definition extractNatS : sqlValS ~> maybeS natS :=
  caseSqlValS
    @ (SomeS)
    @ (constS _ @ None)
    @ (constS _ @ None).

Instance vNat_Proper : Proper (equiv ==> equiv) vNat.
Proof.
  solve_proper.    
Qed.

Definition vNatS : natS ~> sqlValS := injF vNat _.

Instance vAddr_Proper : Proper (equiv ==> equiv) vAddr.
Proof.
  autounfold. intros. destruct x,y. simpl in *. f_equal. f_equal. tauto.  tauto. 
Qed.

Definition vAddrS : sqlAddrS ~> sqlValS := injF vAddr _.


Lemma row_equiv_dec : forall (r1 r2 : row) ,  {r1 == r2} + {~r1 == r2}.
Proof.
  intros. apply lista_equiv_dec.  apply SQLValType.equiv_dec.
Defined.

Lemma maybe_row_equiv_dec : forall r1 r2 : maybe row, {r1 == r2} + {~r1 == r2}.
Proof.
  intros. apply maybe_equiv_dec. apply row_equiv_dec. 
Defined.

  
