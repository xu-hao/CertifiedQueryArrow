Require Import Algebra.Functor Algebra.Applicative Algebra.SetoidCat Algebra.ListUtils Algebra.PairUtils Algebra.Maybe Algebra.SetoidUtils Algebra.Monad Algebra.Maybe Tactics Utils VectorUtils Algebra.Pointed Algebra.Lens.Lista Algebra.Lens.Matrixp Lens Algebra.Monoid.

Require Import SetoidClass List Coq.Classes.RelationClasses Coq.Arith.PeanoNat Coq.Arith.Compare_dec.

Inductive NthPreview := nthPreview : nat -> NthPreview.

Program Instance NthPreviewS : Setoid NthPreview. 

Definition _NthPreview_set {A} {AS : Setoid A} (n : NthPreview) (a : A) (l : list A) : list A :=
  match n with
    | nthPreview n => list_update' n l a
  end
.

Instance _NthPreview_set_Proper A (AS : Setoid A) : Proper (equiv ==> equiv ==> equiv ==> equiv) (@_NthPreview_set A AS).
Proof.
  autounfold. intros.  destruct x, y. unfold _NthPreview_set. simpl in H. inversion H. rewritesr.
Qed.

Definition NthPreview_set {A} {AS : Setoid A} := injF3 (@_NthPreview_set A AS) _.

Definition _NthPreview_preview {A} {AS : Setoid A} (n : NthPreview) (l : list A) : maybe A :=
  match n with
    | nthPreview n => nth_error l n
  end
.

Instance _NthPreview_preview_Proper A (AS : Setoid A) : Proper (equiv ==> equiv ==> equiv) (@_NthPreview_preview A AS).
Proof.
  autounfold. intros. destruct x, y. unfold _NthPreview_preview. simpl in H. inversion H. rewritesr.
Qed.

Definition NthPreview_preview {A} {AS : Setoid A} := injF2 _NthPreview_preview _.

Instance NthPreview_Settable A (AS : Setoid A) : @Settable (list A) A _ _ NthPreview _.
Proof.
  split.
  exact NthPreview_set.
Defined.

Instance NthPreview_Preview A (AS : Setoid A) : @Preview (list A) A _ _ NthPreview _ _.
Proof.
  exists NthPreview_preview.
  - intros. destruct l. generalize H. clear H. apply nat_list_ind_2 with (l1:=n) (l2:=a).
    + intros. simpl in *. auto.
    + intros. simpl in *. reflexivity.
    + intros. simpl in *. auto.
    + intros. simpl in *. apply H. auto.
  - intros. destruct l. generalize H. clear H. apply nat_list_ind_2 with (l1:=n) (l2:=a).
    + intros. simpl in *. auto.
    + intros. simpl in *. auto.
    + intros. simpl in *. auto.
    + intros. simpl in *. apply H. auto.
  - intros. destruct l. generalize H. clear H. apply nat_list_ind_2 with (l1:=n) (l2:=a).
    + intros. simpl in *. auto.
    + intros. simpl in *. constructor. symmetry. auto. reflexivity. 
    + intros. simpl in *. tauto.
    + intros. simpl in *. constructor. reflexivity. apply H. auto.
  - intros. destruct l. generalize H. clear H. apply nat_list_ind_2 with (l1:=n) (l2:=a).
    + intros. simpl in *. reflexivity.
    + intros. simpl in *. tauto.
    + intros. simpl in *. reflexivity.
    + intros. simpl in *. constructor. reflexivity. apply H. auto.
Defined.









