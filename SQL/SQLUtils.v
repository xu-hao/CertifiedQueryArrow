Require Import Definitions Algebra.Monoid Expr Algebra.SetoidCat Algebra.Maybe Tactics Algebra.ListUtils Algebra.Functor Algebra.Applicative Algebra.Alternative Algebra.FoldableFunctor Algebra.PairUtils Algebra.Maybe Algebra.Monad Algebra.Lens.Lens Algebra.Lens.MaybeLens ListLens Utils SetoidUtils SQL Pointed.
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


Existing Instance list_A_Monoid.

Definition _maybe_mappend {C} {CS : Setoid C} {mon : @Monoid C CS} (a b : maybe C) : maybe C :=
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
Defined.


Definition unionRows : listaS (maybeS rowS) ~> listaS (maybeS rowS) ~~> listaS (maybeS rowS) :=
  lista_zipWithS @ mappend.

Definition minS := injF2 min _.

Definition _unionTables (tab1 tab2 : matrixp nat) : matrixp nat :=
  matrixpConsS @ (minS @ (tableWidthGetter @ tab1) @ (tableWidthGetter @ tab2)) @ (unionRows @ (tableRowsGetter @ tab1) @ (tableRowsGetter @ tab2)).

Instance _unionTables_Proper : Proper (equiv ==> equiv ==> equiv) _unionTables.
Proof.
  autounfold. intros. unfold _unionTables. rewritesr.
Qed.

Definition unionTables := injF2 _unionTables _.

Definition unionDatabases : databaseS ~> databaseS ~~> databaseS :=
  list_zipWithS' @ unionTables.

Fixpoint list_maybe_filter {A : Type} {AS : Setoid A} (p : AS ~> boolS) (l : list (maybe A)) : list A :=
    match l with
      | nil => nil
      | None :: l' => list_maybe_filter p l'
      | Some a :: l' => if p @ a then a :: list_maybe_filter p l' else list_maybe_filter p l'
    end.

Instance list_maybe_filter_Proper A (AS : Setoid A) : Proper (equiv ==> equiv ==> equiv) (@list_maybe_filter A AS).
  Proof.
    autounfold. intros. generalize H0. clear H0. apply list_ind_2 with (l1:=x0) (l2:=y0).
    intros. reflexivity.
    intros. inversion H1.
    intros. inversion H1.
    intros. inversion H1. simpl. matchequiv. simpl in H8. rewrites. destruct (y @ a0). constructor. auto. apply H0.  auto. apply H0. auto. apply H0. auto.
  Qed.
  
Fixpoint list_maybe_filter_index {A : Type} {AS : Setoid A} n (p : AS ~> boolS) (l : list (maybe A)) : list nat :=
    match l with
      | nil => nil
      | None :: l' => list_maybe_filter_index (S n) p l'
      | Some a :: l' => if p @ a then n :: list_maybe_filter_index (S n) p l' else list_maybe_filter_index (S n) p l'
    end.

Instance list_maybe_filter_index_Proper A (AS : Setoid A) : Proper (equiv ==> equiv ==> equiv ==> equiv) (@list_maybe_filter_index A AS).
Proof.
    autounfold. intros. generalize H1 x y H . clear H x y H1. apply list_ind_2 with (l1:=x1) (l2:=y1).
    intros. reflexivity.
    intros. inversion H1.
    intros. inversion H1.
    intros. inversion H1. simpl. matchequiv. simpl in H9. rewrite H0, H9. destruct (y0 @ a0). constructor. auto. apply H.  auto. rewritesr. apply H. auto. rewritesr. apply H. auto. rewritesr.
Qed.

Fixpoint list_maybe_filter_index' {A : Type} {AS : Setoid A} n (p : AS ~> boolS) (l : list (maybe A)) : list (nat * A) :=
    match l with
      | nil => nil
      | None :: l' => list_maybe_filter_index' (S n) p l'
      | Some a :: l' => if p @ a then (n,a) :: list_maybe_filter_index' (S n) p l' else list_maybe_filter_index' (S n) p l'
    end.

Instance list_maybe_filter_index'_Proper A (AS : Setoid A) : Proper (equiv ==> equiv ==> equiv ==> equiv) (@list_maybe_filter_index' A AS).
Proof.
    autounfold. intros. generalize H1 x y H . clear H x y H1. apply list_ind_2 with (l1:=x1) (l2:=y1).
    intros. reflexivity.
    intros. inversion H1.
    intros. inversion H1.
    intros. inversion H1. simpl. matchequiv. simpl in H9. rewrite H0, H9. destruct (y0 @ a0). constructor. auto. apply H.  auto. rewritesr. apply H. auto. rewritesr. apply H. auto. rewritesr.
Qed.

Fixpoint duplicate {A} (n : nat) (a : A) : list A :=
  match n with
    | 0 => nil
    | S n => a :: duplicate n a
  end.

Definition extractNat  (val1 : sqlVal)  : maybe nat :=
  match val1 with
    | vNat n => Some n
    | _ => None
  end.
  
Instance extractNat_Proper : Proper (equiv ==> equiv) extractNat.
Proof.
  autounfold. intros. unfold extractNat.  matchequiv.  inversion H. rewritesr. inversion H. inversion H. 
Qed.
  
Definition extractNatS : sqlValS ~> maybeS natS := injF extractNat _.


Instance vNat_Proper : Proper (equiv ==> equiv) vNat.
Proof.
  solve_proper.    
Qed.

Definition vNatS : natS ~> sqlValS := injF vNat _.

Instance pair_Proper A B (AS : Setoid A) (BS : Setoid B): Proper (equiv ==> equiv ==> equiv) (@pair A B).
Proof.
  autounfold. intros. split. auto. auto.
Qed.


Lemma maybe_row_eq_dec : forall r1 r2 : maybe row, {r1 == r2} + {~r1 == r2}.
  intros.  destruct r1, r2.
  - destruct r, r0. destruct (Nat.eq_dec n n0).
    + apply list_rect_2 with (l1:=l) (l2:=l0).
      * left. rewrite e. reflexivity.
      * intros. destruct H.
        destruct e0. destruct (Nat.eq_dec a n).
        rewrite <- e, e0. left. simpl. auto.
        right. simpl. tauto.
        right. simpl in *. tauto.
      * intros. destruct H.
        destruct (Nat.eq_dec a n0).
        rewrite e, e1. left. rewrite e in e0. simpl. auto.
        right. simpl. tauto.
        right. simpl in *. tauto.
      * intros. destruct H.
        destruct (Nat.eq_dec a c).
        rewrite <- e, e1. left. simpl in *. rewrite <- e in e0. auto.
        right. simpl. tauto.
        right. simpl in *. tauto.
    + right. intro. apply n1. assert (n == n0). apply listaCons_equiv with (l1:=l)(l2:=l0). auto. auto.
  - right. intro. inversion H.
  - right. intro. inversion H.
  - left. reflexivity.
Qed.

  Lemma nat_int : forall n n' , n < S n' -> ~ n' < n.
  Proof.
    double induction n n'.
    intros. intro. inversion H0.
    intros. intro. inversion H0. inversion H1.
    intros. intro. inversion H0. inversion H3.
    intros. intro. apply H0 with (n':=n0). apply le_S_n. auto. apply le_S_n. auto.
  Qed.

  Open Scope nat_scope.
  Lemma plus_symmetry : forall a b, a+b = b+a.
  Proof.
    induction a. intros. simpl. apply plus_n_O.
    intros. simpl. rewrite <- plus_n_Sm. f_equal. apply IHa.
  Qed.
