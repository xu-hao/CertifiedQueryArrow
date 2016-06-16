Require Import Algebra.SetoidCat.BoolUtils Algebra.Monoid.

Section Aux.
  Instance bool_and_Monoid : @Monoid bool boolS.
  Proof.
    exists (true) (andbS).
    intros. reflexivity.
    intros. simpl. destruct a. reflexivity. reflexivity.
    intros. simpl. destruct a. reflexivity. reflexivity.
  Defined.
End Aux.
