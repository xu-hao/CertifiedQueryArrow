Require Import SetoidCat SetoidUtils Functor Monoid.

Require Import SetoidClass.

Section FoldableFunctor.


  Context
    {t}
    {tS : forall A (AS : Setoid A), Setoid (t A AS)}
    {func : @Functor t tS}.
  

  Class FoldableFunctor :=
    {
      fold {A} {SA : Setoid A} {monoid : @Monoid _ SA} : tS _ SA ~> SA;
      fold_commutativity :
        forall {A B} {SA : Setoid A} {SB : Setoid B} {monoidA : @Monoid _ SA} {monoidB : @Monoid _ SB} (a : t A _) (f : SA ~> SB) (hom : MonoidHomomorphism f),
          f @ (fold @ a) == fold @ (f <$> a)
                                                            
    }.

End FoldableFunctor.
