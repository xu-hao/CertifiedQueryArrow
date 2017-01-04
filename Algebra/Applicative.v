Require Import SetoidCat Algebra.SetoidCat.SetoidUtils Algebra.Functor Algebra.Monoid PairUtils Algebra.Utils UnitUtils.

Require Import SetoidClass.

Section Applicative.

  Context
    {t : forall A, Setoid A -> Type}
    {tS : forall A (AS : Setoid A), Setoid (t A AS)}
    {func : @Functor t tS}.

  Definition left_unitor {A} {AS : Setoid A} : unitS ~*~ AS ~> AS := sndS.

  Definition right_unitor {A} {AS : Setoid A} : AS ~*~ unitS ~> AS := fstS. 
  
  Definition associator {A B C} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C} : (AS ~*~ BS) ~*~ CS ~> AS ~*~ (BS ~*~ CS) := (fstS ∘ fstS) &&& ((sndS ∘ fstS) &&& sndS).
                              
  Class Applicative :=
    {
      unitA :  t unit _;
      prod {A B} {AS : Setoid A} {BS : Setoid B} : tS _ AS ~> tS _ BS ~~> tS _ (AS ~*~ BS);
      
      left_unit_applicative :
        forall {A} {AS : Setoid A} (a : t A _),
          left_unitor <$> (prod  @ unitA @ a) == a;
      right_unit_applicative :
        forall {A} {AS : Setoid A} (a : t A _),
          right_unitor <$> (prod  @ a @ unitA) == a;
      associativity_applicative:
        forall {A B C} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C}
               (a : t A _) (b : t B _) (c : t C _) ,
          associator <$> (prod  @ (prod  @ a @ b) @ c) == prod  @ a @ (prod  @ b @ c);
      naturality_prod:
        forall {A B C D} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C} {DS : Setoid D}
               (f : AS ~> BS) (g : CS ~> DS) (a : t A _) (c : t C _),
          prod  @ (f <$> a) @ (g <$> c) == (f *** g) <$> (prod  @ a @ c)
    }.

  Context
    {app : Applicative}.

  Definition pure  {A} {AS : Setoid A} : AS ~> tS _ AS := (flipS @ fmap @ unitA) ∘ constS unitS.

  Definition ap {A B} {AS : Setoid A} {BS : Setoid B} : tS _ (AS ~~> BS) ~> tS _ AS ~~> tS _ BS :=
    comp2S @ prod @ (fmap @ (uncurryS @ evalS)).

  Definition produ {A B} {AS : Setoid A} {BS : Setoid B} : tS _ AS ~*~ tS _ BS ~> tS _ (AS ~*~ BS) := uncurryS @ prod  .


  
End Applicative.


Notation "a ** b" := (prod @ a @ b) (at level 49, left associativity).
Notation "a <*> b" := (ap @ a @ b) (at level 49, left associativity).

