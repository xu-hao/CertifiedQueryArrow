Require Import SetoidClass SetoidCat.

Instance natS : Setoid nat :=
  {
    equiv := eq
  }
.

Definition plusS : natS ~> natS ~~> natS := injF2 plus _.

Definition minS := injF2 min _.

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

