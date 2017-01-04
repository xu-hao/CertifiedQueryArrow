Require Import SetoidCat Algebra.SetoidCat.SetoidUtils Algebra.Functor.
Require Import SetoidClass.


Section Utils.
  Context
    {t : forall A, Setoid A -> Type}
    {tS  : forall A (AS : Setoid A), Setoid (t A AS)}
    {func : @Functor t tS}.

  Lemma comp_eval : forall {A B C} {AS : Setoid A} {BS : Setoid B}{
                             CS : Setoid C}(a : A) (f : AS ~> BS) (g : BS~> CS), (comp f g) @ a == g @ (f @ a).
  Proof.
    intros. simpl. reflexivity.
  Qed.  

    Lemma fmap_fmap : forall {A B C} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C}
                           (f : AS ~> BS) (g : BS ~> CS) (a : t A _),
                      g <$> (f <$> a) == (g ∘ f) <$> a.
  Proof.
    intros. rewrite <- comp_eval. rewrite functoriality_comp. reflexivity.
    Qed.
  Lemma fmap_idS_absorb : forall {A} {AS : Setoid A} (a : t A _), idS <$> a == a.
  Proof.
    intros. rewrite functoriality_id. simpl. reflexivity.
  Qed.

End Utils.
