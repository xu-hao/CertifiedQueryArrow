Require Import Algebra.Functor Algebra.Applicative Algebra.SetoidCat Algebra.ListUtils Algebra.PairUtils Algebra.Maybe Algebra.SetoidUtils Algebra.Monad Algebra.Maybe Tactics Utils Algebra.Lens.Lista Algebra.Lens.Matrixp Lens Algebra.Monoid MaybeLens ListaLens Pointed.

Require Import SetoidClass List Coq.Classes.RelationClasses Coq.Arith.PeanoNat Coq.Arith.Compare_dec.

Inductive MatrixRowsLens := matrixRowsLens.

Program Instance MatrixRowsLensS : Setoid MatrixRowsLens. 

Definition _MatrixRowsLens_set {A} {AS : Setoid A} {AP : Pointed A} (_ : MatrixRowsLens) (r :  lista (maybe (lista A))) (m : matrixp A) :=
  match m with
    | matrixpCons _  r' => matrixpConsS @  r
  end
.

Instance _MatrixRowsLens_set_Proper A (AS : Setoid A) AP : Proper (equiv ==> equiv ==> equiv ==> equiv) (@_MatrixRowsLens_set A AS AP ).
Proof.
  autounfold. intros. destruct x1, y1. unfold _MatrixRowsLens_set.  rewritesr.
Qed.

Definition MatrixRowsLens_set {A} {AS : Setoid A} {AP} := injF3 (@_MatrixRowsLens_set A AS AP) _.

Definition _MatrixRowsLens_view {A} {AS : Setoid A} {AP : Pointed A} (_ : MatrixRowsLens) := rows.

Instance _MatrixRowsLens_view_Proper A (AS : Setoid A) AP : Proper (equiv ==> equiv) (@_MatrixRowsLens_view A AS AP ).
Proof.
  autounfold. intros.  destruct x, y. unfold _MatrixRowsLens_view. reflexivity. 
Qed.

Definition MatrixRowsLens_view {A} {AS : Setoid A} {AP} := injF (@_MatrixRowsLens_view A AS AP) _.


Instance MatrixRowsLens_Settable A (AS : Setoid A) (AP : Pointed A) : @Settable (matrixp A) (lista (maybe (lista A))) _ _ MatrixRowsLens _.
Proof.
  split.
  exact MatrixRowsLens_set.
Defined.

Instance MatrixRowsLens_PreLens A (AS : Setoid A) (AP : Pointed A) : @PreLens (matrixp A) (lista (maybe (lista A))) _ _ MatrixRowsLens _ _.
Proof.
  exists MatrixRowsLens_view.
  intros. destruct a.  simpl set.  unfold MatrixRowsLens_set, _MatrixRowsLens_set. normalize. unfold MatrixRowsLens_view, _MatrixRowsLens_view. normalize.  unfold rows, _rows. normalize. reflexivity. Defined.

Instance MatrixRowsLens_Lens A (AS : Setoid A) (AP : Pointed A) : @Lens (matrixp A) (lista (maybe (lista A))) _ _ MatrixRowsLens _ _ _.
Proof.
  split.
  intros. destruct a.  simpl. reflexivity.
  intros. destruct a.  simpl. reflexivity.
Qed.


Definition matrixCellPreview ri ci := matrixRowsLens >>>? listaNthLens ri >>>? maybePreview >>>? listaNthLens ci.

Existing Instance ComposeP_Preview.
Existing Instance Lens_Preview.

Definition _MatrixCellPreview_set {A} {AS : Setoid A} {AP : Pointed A} ri ci  :  AS ~> matrixpS  AS ~~> matrixpS AS :=
        set @ (matrixCellPreview ri ci)
.


Instance _MatrixCellPreview_set_Proper A (AS : Setoid A) AP : Proper (equiv ==> equiv ==> equiv) (@_MatrixCellPreview_set A AS AP).
Proof.
  autounfold. intros.   rewrite H, H0. reflexivity. 
Qed.

Definition MatrixCellPreview_set {A} {AS : Setoid A} AP := injF2 (@_MatrixCellPreview_set A AS AP) _.

Existing Instance Preview_Maybe_Settable.
Existing Instance Preview_PreLens.
Set Printing Implicit.
Definition _MatrixCellPreview_preview {A} {AS : Setoid A} {AP : Pointed A} ri ci: matrixpS AS ~>  maybeS AS :=
  preview @ (matrixRowsLens >>>? listaNthLens ri >>>? maybePreview >>>? listaNthLens ci).

Instance _MatrixCellPreview_preview_Proper A (AS : Setoid A) AP : Proper (equiv ==> equiv ==> equiv) (@_MatrixCellPreview_preview A AS AP).
Proof.
  autounfold. intros.  rewritesr. 
Qed.

Definition MatrixCellPreview_preview {A} {AS : Setoid A} {AP : Pointed A} := injF2 (@_MatrixCellPreview_preview A AS AP ) _.





Definition matrixRowPreview ri := matrixRowsLens >>>? listaNthLens ri >>>? maybePreview.


Definition _MatrixRowPreview_set {A} {AS : Setoid A} {AP : Pointed A} ri  :  listaS AS ~> matrixpS  AS ~~> matrixpS AS :=
        set @ (matrixRowPreview ri)
.


Instance _MatrixRowPreview_set_Proper A (AS : Setoid A) AP : Proper (equiv ==> equiv) (@_MatrixRowPreview_set A AS AP).
Proof.
  autounfold. intros.   rewrite H. reflexivity. 
Qed.

Definition MatrixRowPreview_set {A} {AS : Setoid A} AP := injF (@_MatrixRowPreview_set A AS AP) _.

Definition _MatrixRowPreview_preview {A} {AS : Setoid A} {AP : Pointed A} ri: matrixpS AS ~>  maybeS (listaS AS) :=
  preview @ (matrixRowPreview ri).

Instance _MatrixRowPreview_preview_Proper A (AS : Setoid A) AP : Proper (equiv ==> equiv) (@_MatrixRowPreview_preview A AS AP).
Proof.
  autounfold. intros.  rewritesr. 
Qed.

Definition MatrixRowPreview_preview {A} {AS : Setoid A} {AP : Pointed A} := injF (@_MatrixRowPreview_preview A AS AP ) _.

Definition matrixMaybeRowLens ri := matrixRowsLens >>>? listaNthLens ri.


Definition _MatrixMaybeRowLens_set {A} {AS : Setoid A} {AP : Pointed A} ri  :  maybeS (listaS AS) ~> matrixpS  AS ~~> matrixpS AS :=
        set @ (matrixMaybeRowLens ri)
.


Instance _MatrixMaybeRowLens_set_Proper A (AS : Setoid A) AP : Proper (equiv ==> equiv) (@_MatrixMaybeRowLens_set A AS AP).
Proof.
  autounfold. intros.   rewrite H. reflexivity. 
Qed.

Definition MatrixMaybeRowLens_set {A} {AS : Setoid A} AP := injF (@_MatrixMaybeRowLens_set A AS AP) _.

Definition _MatrixMaybeRowLens_view {A} {AS : Setoid A} {AP : Pointed A} ri: matrixpS AS ~>  maybeS (listaS AS) :=
  view @ (matrixRowPreview ri).

Instance _MatrixMaybeRow_view_Proper A (AS : Setoid A) AP : Proper (equiv ==> equiv) (@_MatrixMaybeRowLens_view A AS AP).
Proof.
  autounfold. intros.  rewritesr. 
Qed.

Definition MatrixMaybeRowLensP_view {A} {AS : Setoid A} {AP : Pointed A} := injF (@_MatrixMaybeRowLens_view A AS AP ) _.
