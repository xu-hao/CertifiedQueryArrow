Require Import Monad SetoidCat.
Require Import SetoidClass.
Lemma compM_associativity : forall {A} {B} {C} {D} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C} {DS : Setoid D} {m mS} {mnd : @Monad m mS} (f : AS ~> mS _ BS) (g : BS ~> mS _ CS) (h : CS ~> mS _ DS),
                             f >=> g >=> h == f >=> (g >=> h).
Proof.
  intros. simpl_equiv. normalize_monad. reflexivity.
Qed.

Lemma comp_compM : forall {A} {B} {C} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C} {m mS} {mnd : @Monad m mS} (f : AS ~> BS) (g : BS ~> mS _ CS),
                             g ∘ f == ret ∘ f >=> g.
Proof.
  intros. simpl_equiv. normalize_monad. reflexivity.
Qed.

