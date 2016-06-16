Require Import SetoidClass SetoidCat Monoid Algebra.SetoidCat.NatUtils.


Section NatMonoid.

  Open Scope nat_scope.

  Lemma nat_plus_associativity : forall a b c, a + b + c = a + (b + c).
  Proof.
    intros. induction a. reflexivity.
    simpl. congruence.
  Qed.

  Instance nat_Monoid : @Monoid nat natS.
  Proof.
    exists (0) (plusS).
    intros. reflexivity.
    intros. rewrite plus_n_O. reflexivity.
    intros. apply nat_plus_associativity.
  Defined.

End NatMonoid.
