Require Import SetoidCat Algebra.SetoidCat.SetoidUtils.
Require Import SetoidClass.


Section Functor.

  Context
    {t : forall A, Setoid A -> Type}
    {tS : forall A (AS : Setoid A), Setoid (t A AS)}.


  Instance tSetoid {A} {AS : Setoid A} : Setoid (t A _) := tS _ AS.

  Class Functor :=
    {
      fmap : forall {A B} {AS : Setoid A} {BS : Setoid B}, (AS ~~> BS) ~> tS _ AS ~~> tS _ BS;
      functoriality_comp : forall {A B C} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C}
                                  (f : AS ~> BS) (g : BS ~> CS),
                             fmap  @ (g ∘ f) == fmap  @ g ∘ fmap  @ f;
      
      functoriality_id: forall {A} {AS : Setoid A},
                         fmap  @ idS == idS
    }.

End Functor.

Notation "a <$> b" := (fmap  @ a @ b) (at level 49, left associativity).

