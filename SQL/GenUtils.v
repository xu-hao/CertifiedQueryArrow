Require Import Definitions Algebra.Monoid Expr Algebra.SetoidCat Algebra.Maybe Tactics Algebra.ListUtils Algebra.Functor Algebra.Applicative Algebra.Alternative Algebra.FoldableFunctor Algebra.PairUtils Algebra.Maybe Algebra.Monad Algebra.Lens.Lens Algebra.Lens.MaybeLens ListLens Utils SetoidUtils Pointed Lista Matrixp.
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


Definition _maybe_first_mappend {C} {CS : Setoid C}  (a b : maybe C) : maybe C :=
  match a with
    | None => b
    | Some a' => a
  end
.

Instance _maybe_first_mappend_Proper {C} {CS : Setoid C}  : Proper (equiv ==> equiv ==> equiv) _maybe_first_mappend.
Proof.
  autounfold. intros. unfold _maybe_first_mappend. matchequiv. auto. auto. 
Qed.

Definition maybe_first_mappend {C} {CS : Setoid C} : maybeS CS ~> maybeS CS ~~> maybeS CS := injF2 _maybe_first_mappend _.
      
Instance maybe_first_Monoid {C} {CS : Setoid C} : @Monoid (maybe C) _.
Proof.
  exists (None) (maybe_first_mappend).
  intros. simpl. destruct a. reflexivity. reflexivity.
  intros. destruct a. simpl. reflexivity. simpl. auto.
  intros. destruct a. simpl. reflexivity. destruct b. simpl. reflexivity. simpl. destruct c.  reflexivity. reflexivity.
Defined.


Instance maybe_mappend_PointedFunction2 A AS : PointedFunction2 (@maybe_first_mappend A AS).
Proof.
  split. simpl. auto.
Qed.

Definition minS := injF2 min _.


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

Existing Instance pair_Proper.

Existing Instance listaCons_Proper.

Lemma lista_equiv_dec : forall {A} {AS :Setoid A} {AP : Pointed A } (r1 r2 : lista A) (equiv_dec : forall a1 a2 : A, {a1 == a2} + {~a1 == a2}),  {r1 == r2} + {~r1 == r2}.
Proof.
  intros. destruct r1 as [l], r2 as [l0].
  
  apply list_rect_2 with (l1:=l) (l2:=l0).
      - left.  reflexivity.
      - intros. destruct H.
        + destruct (equiv_dec a point).
          * left. split. auto. auto. 
          * right. simpl. tauto.
        + right. simpl. tauto. 
      - intros. destruct H.
        + destruct (equiv_dec a point).
          * left. split. auto. simpl in e. auto.
          * right. simpl. tauto.
        + right. simpl in *. tauto.
      - intros. destruct H.
        + destruct (equiv_dec a c).
          * left. simpl. auto. 
          * right. simpl. tauto.
        + right. simpl in *. tauto.
Defined.

Lemma maybe_equiv_dec : forall {A} {AS :Setoid A} (r1 r2 : maybe A) (equiv_dec : forall a1 a2 : A, {a1 == a2} + {~a1 == a2}), {r1 == r2} + {~r1 == r2}.
Proof.
  intros.  destruct r1 as [n|], r2 as [n0 |].
  - destruct (equiv_dec n n0).
    + left. rewrite e. reflexivity. 
    + right. intro. apply n1. auto. 
  - right. intro. inversion H.
  - right. intro. inversion H.
  - left. reflexivity.
Defined.

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

Definition ltS : natS ~> natS ~~> iff_setoid := injF2 lt _.

  Definition ltMaybe a b :=
    caseMaybeS
      @ (ltS @ a) 
      @ False
      @ b.

  Instance ltMaybe_Proper : Proper (equiv ==> equiv ==> equiv) ltMaybe.
  Proof.
    solve_properS ltMaybe.
  Qed.
  
  Definition ltMaybeS := injF2 ltMaybe _.
  
