Require Import Algebra.Functor Algebra.Applicative Algebra.SetoidCat Algebra.PairUtils Algebra.SetoidUtils Algebra.Monad Tactics Utils Algebra.Lens.LensTypes Algebra.Maybe Lens.
Require Import SetoidClass Vector.


Inductive MaybePreview := maybePreview.

Program Instance MaybePreviewS : Setoid MaybePreview.

Definition _MaybePreview_set {A} {AS : Setoid A} (_ : MaybePreview) (a : A) : maybeS AS ~> maybeS AS :=
  caseMaybeS
    @ (constS _ @ (SomeS @ a))
    @ None.

Instance _MaybePreview_set_Proper A (AS : Setoid A) : Proper (equiv ==> equiv ==> equiv) (@_MaybePreview_set A AS).
Proof.
  autounfold. intros. unfold _MaybePreview_set. rewritesr.
Qed.

Definition MaybePreview_set {A} {AS : Setoid A} := injF2 (@_MaybePreview_set A AS) _.

Definition MaybePreview_preview {A} {AS : Setoid A} : MaybePreviewS ~> maybeS AS ~~> maybeS AS :=
  constS _ @ idS.

Instance maybePreview_Settable A (AS : Setoid A) : @Settable (maybe A) A _  _ MaybePreview _ .
Proof.
  split.
  exact (MaybePreview_set).
Defined.

Instance maybePreview_Preview A (AS : Setoid A) : @Preview (maybe A) A _ _ MaybePreview _ _.
Proof.
  exists (MaybePreview_preview).
  intros. destruct a; [simpl; reflexivity | simpl in H; tauto].
  intros. destruct a; [simpl in H; tauto | simpl; auto].
  intros. destruct a; [simpl in *; symmetry; auto | simpl; auto].
  intros. destruct a; [simpl in H; tauto | simpl; auto].

Defined.