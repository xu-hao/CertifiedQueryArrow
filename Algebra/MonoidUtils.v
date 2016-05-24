
Require Import  Utils Algebra.SetoidCat Algebra.Monoid Algebra.Monad Algebra.SetoidUtils Algebra.PairUtils Algebra.Functor Algebra.Applicative.

Require Import RelationClasses Relation_Definitions Morphisms SetoidClass.

Require Import List.

Open Scope type_scope.

Section Arr_Monoid.
  Context
    {A B : Type}
    {SA : Setoid A}
    {SB : Setoid B}
    {B_Monoid : @Monoid _ SB}.

  Definition arr_mempty : SA ~> SB := constS SA @ mempty.

  Definition arr_mappend : (SA ~~> SB) ~> (SA ~~> SB) ~~> (SA ~~> SB) :=
    comp3S @ pairingF @ (uncurryS @ mappend).

  Instance arr_Monoid : @Monoid _ (SA ~~> SB).
  Proof.
    exists (arr_mempty) (arr_mappend).
    intros. simpl. arrequiv. apply left_unit_monoid.
    intros. simpl. arrequiv. apply right_unit_monoid.
    intros. simpl. arrequiv. apply associativity_monoid.
  Defined.
End Arr_Monoid.

Section MonadMonoid.

Context
    {m mS}
    {mnd : @Monad m mS}.

Definition monad_mempty {A} {SA : Setoid A} {A_Monoid : @Monoid _ SA}: m A _ :=
  ret @ mempty.

Existing Instance monad_Applicative.
Existing Instance monadFunctor.

Definition monad_mappend  {A} {SA : Setoid A} {A_Monoid : @Monoid _ SA} : mS _ SA ~> mS _ SA ~~> mS _ SA := ap ∘ (fmap @ mappend). 

Instance monad_Monoid A (SA : Setoid A) (A_Monoid : @Monoid _ SA): @Monoid _ (mS _ SA).
Proof.
  exists monad_mempty monad_mappend.
  intros. simpl. unfold monad_mempty. normalize_monad.  rewrite right_unit_equiv. reflexivity. simpl. arrequiv. normalize_monad. simpl. rewrite left_unit_monoid. reflexivity.
  intros. simpl. unfold monad_mempty. normalize_monad. rewrite right_unit_equiv. reflexivity. simpl.  arrequiv. normalize_monad. simpl. rewrite right_unit_monoid. reflexivity.
  intros. simpl. normalize_monad. 
  bindproper. simpl. arrequiv. normalize_monad. bindproper. simpl. arrequiv. normalize_monad. bindproper. simpl. normalize_monad. simpl. rewrite associativity_monoid. reflexivity.
Defined.
End MonadMonoid.

Section NatMonoid.

  Definition plusS : natS ~> natS ~~> natS := injF2 plus _.

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


Section Aux.

    Definition andS := injF2 and _.
    Instance and_Monoid : @Monoid Prop iff_setoid.
    Proof.
      exists True andS.
      intros. simpl. tauto.
      intros. simpl. tauto.
      intros. simpl. tauto.
    Defined.
    Definition orS := injF2 or _.
    Instance or_Monoid : @Monoid Prop iff_setoid.
    Proof.
      exists False orS.
      intros. simpl. tauto.
      intros. simpl. tauto.
      intros. simpl. tauto.
    Defined.
End Aux.