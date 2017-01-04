Require Import Algebra.Functor Algebra.Applicative Algebra.SetoidCat Algebra.SetoidCat.ListUtils Algebra.SetoidCat.PairUtils Algebra.Monad.Maybe Algebra.SetoidUtils Algebra.Monad Tactics Utils Algebra.Pointed Algebra.Lens.Lista Algebra.Lens.Matrixp Lens Algebra.Monoid.

Require Import SetoidClass List Coq.Classes.RelationClasses Coq.Arith.PeanoNat Coq.Arith.Compare_dec.

Inductive ListaNthLens := listaNthLens : nat -> ListaNthLens.

Program Instance ListaNthLensS : Setoid ListaNthLens. 

Definition _ListaNthLens_set {A} {AS : Setoid A} {AP : Pointed A} (n : ListaNthLens) (a : A) (l : lista A) : lista A :=
  match n with
    | listaNthLens n => lista_update n l a
  end
.

Instance _ListaNthLens_set_Proper A (AS : Setoid A) AP: Proper (equiv ==> equiv ==> equiv ==> equiv) (@_ListaNthLens_set A AS AP).
Proof.
  autounfold. intros.  destruct x, y. unfold _ListaNthLens_set. simpl in H. inversion H. rewritesr.
Qed.

Definition ListaNthLens_set {A} {AS : Setoid A}{AP} := injF3 (@_ListaNthLens_set A AS AP) _.

Definition _ListaNthLens_view {A} {AS : Setoid A}{AP : Pointed A} (n : ListaNthLens) (l : lista A) : A :=
  match n with
    | listaNthLens n => lista_nth n l
  end
.

Instance _ListaNthLens_view_Proper A (AS : Setoid A) AP: Proper (equiv ==> equiv ==> equiv) (@_ListaNthLens_view A AS AP).
Proof.
  autounfold. intros. destruct x, y. unfold _ListaNthLens_view. simpl in H. inversion H. rewritesr.
Qed.

Definition ListaNthLens_view {A} {AS : Setoid A} {AP}:= injF2 (@_ListaNthLens_view A AS AP) _.

Instance ListaNthLens_Settable A (AS : Setoid A) (AP : Pointed A) : @Settable (lista A) A _ _ ListaNthLens _.
Proof.
  split.
  exact ListaNthLens_set.
Defined.

Instance ListaNthLens_PreLens A (AS : Setoid A) (AP : Pointed A): @PreLens (lista A) A _ _ ListaNthLens _ _.
Proof.
  exists ListaNthLens_view.
  intros. destruct l. simpl. apply lista_update_lista_nth.
Defined.

Instance ListaNthLens_Lens A (AS : Setoid A) (AP : Pointed A) : @Lens (lista A) A _ _ ListaNthLens _ _ _.
Proof.
  split. 
  - intros. destruct l, a. Opaque lista_update. simpl. apply lista_update_lista_update. 
  - intros. destruct l, a. Opaque lista_nth. simpl. apply lista_nth_lista_update_equiv. 
Qed.




