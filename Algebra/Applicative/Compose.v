Require Import SetoidCat SetoidUtils Functor Monoid PairUtils  UnitUtils Algebra.Applicative Algebra.Functor.Compose Algebra.Functor.Utils.

Require Import SetoidClass.

Section ComposeApplicative.

  Context
    {t t' : forall A, Setoid A -> Type}
    {tS : forall A (AS : Setoid A), Setoid (t A AS)}
    {tS' : forall A (AS : Setoid A), Setoid (t' A AS)}
    {func : @Functor t tS} {func' : @Functor t' tS'}
    {app : @Applicative _ _ func} {app' : @Applicative _ _ func'}.


  Definition compFunc_unit : @ComposeFunc t t' _ unit _  := ComposeIsoS unitS @ (pure @ unitA).

  Definition compFunc_prod {A B} {AS : Setoid A} {BS : Setoid B} : @ComposeS t t' _ _ _ AS ~> @ComposeS t t' _ _ _ BS ~~> @ComposeS t t' _ _ _ (AS ~*~ BS) :=
    flipS @ compS @ ComposeIsoS (AS ~*~ BS)
          ∘ compS @ ComposeIsoS' BS
          ∘ comp2S  @  prod  @ (fmap @ produ) ∘ ComposeIsoS' AS.

  Existing Instance ComposeFunctor.
  Existing Instance ComposeS.

  Lemma compFunc_naturality_prod:
    forall {A B C D} {AS : Setoid A} {BS : Setoid B} {CS : Setoid C} {DS : Setoid D}
           (f : AS ~> BS) (g : CS ~> DS) (a : ComposeFunc A) (c : ComposeFunc C),
      compFunc_prod @ (compFunc_fmap @ f @ a) @ (compFunc_fmap @ g @ c) == compFunc_fmap @ (f *** g) @ (compFunc_prod @ a @ c).
  Proof.
    intros. unfold compFunc_fmap. unfold compFunc_prod. simpl. rewrite naturality_prod. rewrite fmap_fmap. rewrite fmap_fmap. evalproper. evalproper. simpl. arrequiv. destruct a0. simpl. rewrite naturality_prod. evalproper. 
  Qed.
  

  Instance Compose_Applicative : @Applicative (@ComposeFunc t t' _ ) (@ComposeS t t' _ _) _.
  Proof.
    exists (@compFunc_unit) (@compFunc_prod).
    intros. simpl. destruct a. simpl. rewrite <- (fmap_idS_absorb t0) at 1.  rewrite naturality_prod. rewrite fmap_fmap. rewrite fmap_fmap. rewrite <- (left_unit_applicative t0) at 2. evalproper. evalproper. simpl. arrequiv. destruct a. simpl. rewrite left_unit_applicative. reflexivity.
    intros. simpl. destruct a. simpl. rewrite <- (fmap_idS_absorb t0) at 1.  rewrite naturality_prod. rewrite fmap_fmap. rewrite fmap_fmap. rewrite <- (right_unit_applicative t0) at 2. evalproper. evalproper. simpl. arrequiv. destruct a. simpl. rewrite right_unit_applicative. reflexivity.
    intros. simpl. rewrite <- (fmap_idS_absorb (ComposeIso' C c)) at 1. rewrite naturality_prod. rewrite <- (fmap_idS_absorb (ComposeIso' A a)) at 2. rewrite naturality_prod. rewrite <- associativity_applicative. repeat rewrite fmap_fmap. evalproper. evalproper. simpl. arrequiv. destruct a0. simpl. apply associativity_applicative.
    intros. apply compFunc_naturality_prod.
  Defined. 
  

End ComposeApplicative.

